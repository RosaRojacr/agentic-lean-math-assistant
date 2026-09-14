/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundarySimpleLoop
import CMVBoundaryNonsmoothJunction
import CMVFigureThreeSourceExtraction
import CMVFigureFourBoundaryRigidity

/-!
# Selected-boundary trace adapter

The simple loop constructed on the selected bounded representative is packaged
in the unchanged Figure-3 `ClosedBoundaryTrace` interface.  Continuity and
half-open injectivity remain separate exported facts because that interface
intentionally records only closure and complete image.  Source minimality is
transported between the original carrier and the selected representative only
through the retained planar-AE invariance of the relaxed semantics.
-/

open Set Function MeasureTheory TopologicalSpace
open scoped Topology ENNReal MeasureTheory

noncomputable section

open Real

namespace CMVSourceClassification.RawFourArcCoordinates

variable (raw : CMVSourceClassification.RawFourArcCoordinates)

set_option maxHeartbeats 1200000 in
-- The five-piece carrier normalization is a large nonlinear arithmetic proof.
private theorem centered_upperLeft_closedModel
    (h : raw.SatisfiesClosedSnell 2) {q : PlanePoint}
    (hx : q.1 < 0) (hy : 0 < q.2) :
    q ∈ raw.centeredCarrier ↔
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q ≤ 0 ∨
        CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q ≤ 0 := by
  have hR : 0 < raw.sourceRadius := lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hsin : 0 < sin raw.exteriorHalfAngle :=
    sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
      (lt_trans h.exteriorHalfAngle_lt_pi_div_two (by linarith [Real.pi_pos]))
  have hRcos : raw.sourceRadius * cos raw.exteriorHalfAngle = 1 / 2 := by
    have hs := h.snell_incidence
    unfold curvature at hs
    field_simp [ne_of_gt hR] at hs
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq raw.exteriorHalfAngle
  have hwidthSq : raw.outerHalfWidth ^ 2 + (1 / 2 : ℝ) ^ 2 = raw.sourceRadius ^ 2 := by
    unfold outerHalfWidth
    nlinarith [mul_self_nonneg raw.sourceRadius]
  have hrad : 0 ≤ 1 - raw.curvature ^ 2 := by
    unfold curvature
    have hdiv : 1 / raw.sourceRadius ≤ 1 := (div_le_one hR).2 h.radius_ge_one
    have hdiv0 : 0 ≤ 1 / raw.sourceRadius := (one_div_pos.mpr hR).le
    nlinarith
  have hinnerSq : (raw.sourceRadius * raw.innerRadial) ^ 2 =
      raw.sourceRadius ^ 2 - 1 := by
    rw [innerRadial, mul_pow, Real.sq_sqrt hrad]
    unfold curvature
    field_simp [ne_of_gt hR]
  have hinner0 : 0 ≤ raw.sourceRadius * raw.innerRadial :=
    mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hWpos : 0 < raw.outerHalfWidth := by
    unfold outerHalfWidth
    exact mul_pos hR hsin
  have hsidePos : 0 < raw.sideCenterOffset := by
    rw [sideCenterOffset]
    have heq : raw.sourceRadius *
        (sin raw.exteriorHalfAngle - raw.innerRadial) =
      raw.outerHalfWidth - raw.sourceRadius * raw.innerRadial := by
      unfold outerHalfWidth
      ring
    rw [heq]
    nlinarith
  have hpLeft :
      CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius
        (-raw.outerHalfWidth, 1) = 0 := by
    unfold CMVFigureFour.circleValue leftCenter
    dsimp only
    have heq : -raw.outerHalfWidth - -raw.sideCenterOffset =
        -(raw.sourceRadius * raw.innerRadial) := by
      unfold sideCenterOffset outerHalfWidth
      ring
    rw [heq]
    nlinarith
  have hpUpper :
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius
        (-raw.outerHalfWidth, 1) = 0 := by
    unfold CMVFigureFour.circleValue upperCenter
    dsimp only
    nlinarith
  have hpLeCenter : -raw.outerHalfWidth ≤ raw.leftCenter.1 := by
    unfold leftCenter sideCenterOffset outerHalfWidth
    dsimp only
    nlinarith
  have hdiff (z : PlanePoint) :
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius z -
          CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius z =
        -2 * raw.sideCenterOffset * (z.1 + raw.outerHalfWidth) - (z.2 - 1) := by
    have hsideRelation :
        2 * raw.sideCenterOffset * raw.outerHalfWidth -
            raw.sideCenterOffset ^ 2 = 3 / 4 := by
      unfold CMVFigureFour.circleValue leftCenter at hpLeft
      dsimp only at hpLeft
      nlinarith [hwidthSq]
    unfold CMVFigureFour.circleValue upperCenter leftCenter
    dsimp only
    rw [hRcos]
    ring_nf
    nlinarith
  constructor
  · intro hq
    simp only [centeredCarrier, rectangleCarrier, leftSegmentCarrier,
      rightSegmentCarrier, upperCapCarrier, lowerCapCarrier,
      Set.mem_union, Set.mem_ofPred_eq] at hq
    rcases hq with (((hrect | hleft) | hright) | hupper) | hlower
    · left
      unfold CMVFigureFour.circleValue upperCenter
      dsimp only
      have hqy := abs_le.mp hrect.2.2
      nlinarith [sq_nonneg (q.1 + raw.outerHalfWidth),
        sq_nonneg (q.2 - (1 / 2 : ℝ))]
    · right
      simpa only [CMVFigureFour.circleValue] using
        (sub_nonpos.mpr hleft.1)
    · exfalso
      nlinarith [hright.2.1, hWpos]
    · left
      simpa only [CMVFigureFour.circleValue] using
        (sub_nonpos.mpr hupper.1)
    · exfalso
      linarith [hlower.2]
  · intro hq
    rcases hq with hupper | hleft
    · by_cases hyTop : 1 ≤ q.2
      · apply Or.inl
        apply Or.inr
        refine ⟨?_, hyTop⟩
        simpa only [CMVFigureFour.circleValue] using
          (sub_nonpos.mp hupper)
      · have hyLe : q.2 ≤ 1 := le_of_not_ge hyTop
        have habsy : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith, hyLe⟩
        by_cases hxRect : -raw.outerHalfWidth ≤ q.1
        · apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact ⟨hxRect, by linarith [hWpos], habsy⟩
        · have hxLeft : q.1 < -raw.outerHalfWidth := lt_of_not_ge hxRect
          have hdu := hdiff q
          have hleft' : CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q < 0 := by
            nlinarith
          apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inr
          refine ⟨?_, hxLeft.le, habsy⟩
          simpa only [CMVFigureFour.circleValue] using
            (sub_nonpos.mp hleft'.le)
    · by_cases hyCore : q.2 ≤ 1
      · have habsy : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith, hyCore⟩
        by_cases hxLeft : q.1 ≤ -raw.outerHalfWidth
        · apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inr
          refine ⟨?_, hxLeft, habsy⟩
          simpa only [CMVFigureFour.circleValue] using
            (sub_nonpos.mp hleft)
        · apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inl
          exact ⟨le_of_not_ge hxLeft, by linarith [hWpos], habsy⟩
      · have hyTop : 1 < q.2 := lt_of_not_ge hyCore
        have hxRight : -raw.outerHalfWidth < q.1 := by
          by_contra hnot
          have hxLeft : q.1 ≤ -raw.outerHalfWidth := le_of_not_gt hnot
          have hqCenter : q.1 ≤ raw.leftCenter.1 :=
            hxLeft.trans hpLeCenter
          have hprod : 0 ≤
              (-raw.outerHalfWidth - q.1) *
                (2 * raw.leftCenter.1 + raw.outerHalfWidth - q.1) :=
            mul_nonneg (by linarith) (by linarith)
          unfold CMVFigureFour.circleValue leftCenter at hleft hpLeft
          simp only [leftCenter] at hpLeCenter hqCenter hprod
          dsimp only at hleft hpLeft hpLeCenter hqCenter hprod
          nlinarith
        have hdu := hdiff q
        have hupper' : CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q < 0 := by
          nlinarith
        apply Or.inl
        apply Or.inr
        refine ⟨?_, hyTop.le⟩
        simpa only [CMVFigureFour.circleValue] using
          (sub_nonpos.mp hupper'.le)


set_option maxHeartbeats 1200000 in
-- Interior identification repeats that arithmetic and excludes residual frontier points.
theorem centered_upperLeft_interiorModel
    (h : raw.SatisfiesClosedSnell 2) {q : PlanePoint}
    (hx : q.1 < 0) (hy : 0 < q.2) :
    q ∈ interior raw.centeredCarrier ↔
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q < 0 := by
  have hR : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hsin : 0 < sin raw.exteriorHalfAngle :=
    sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
      (lt_trans h.exteriorHalfAngle_lt_pi_div_two
        (by linarith [Real.pi_pos]))
  have hWpos : 0 < raw.outerHalfWidth := by
    unfold outerHalfWidth
    exact mul_pos hR hsin
  have hRcos : raw.sourceRadius * cos raw.exteriorHalfAngle = 1 / 2 := by
    have hs := h.snell_incidence
    unfold curvature at hs
    field_simp [ne_of_gt hR] at hs
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq raw.exteriorHalfAngle
  have hwidthSq :
      raw.outerHalfWidth ^ 2 + (1 / 2 : ℝ) ^ 2 =
        raw.sourceRadius ^ 2 := by
    unfold outerHalfWidth
    nlinarith [mul_self_nonneg raw.sourceRadius]
  have hrad : 0 ≤ 1 - raw.curvature ^ 2 := by
    unfold curvature
    have hdiv : 1 / raw.sourceRadius ≤ 1 :=
      (div_le_one hR).2 h.radius_ge_one
    have hdiv0 : 0 ≤ 1 / raw.sourceRadius :=
      (one_div_pos.mpr hR).le
    nlinarith
  have hinnerSq :
      (raw.sourceRadius * raw.innerRadial) ^ 2 =
        raw.sourceRadius ^ 2 - 1 := by
    rw [innerRadial, mul_pow, Real.sq_sqrt hrad]
    unfold curvature
    field_simp [ne_of_gt hR]
  have hinner0 : 0 ≤ raw.sourceRadius * raw.innerRadial :=
    mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hsidePos : 0 < raw.sideCenterOffset := by
    rw [sideCenterOffset]
    have heq : raw.sourceRadius *
        (sin raw.exteriorHalfAngle - raw.innerRadial) =
      raw.outerHalfWidth - raw.sourceRadius * raw.innerRadial := by
      unfold outerHalfWidth
      ring
    rw [heq]
    nlinarith
  have hpUpper :
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius
        (-raw.outerHalfWidth, 1) = 0 := by
    unfold CMVFigureFour.circleValue upperCenter
    dsimp only
    nlinarith
  have hpLeft :
      CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius
        (-raw.outerHalfWidth, 1) = 0 := by
    unfold CMVFigureFour.circleValue leftCenter
    dsimp only
    have heq : -raw.outerHalfWidth - -raw.sideCenterOffset =
        -(raw.sourceRadius * raw.innerRadial) := by
      unfold sideCenterOffset outerHalfWidth
      ring
    rw [heq]
    nlinarith
  have hpLeCenter : -raw.outerHalfWidth ≤ raw.leftCenter.1 := by
    unfold leftCenter sideCenterOffset outerHalfWidth
    dsimp only
    nlinarith
  have hdiff (z : PlanePoint) :
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius z -
          CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius z =
        -2 * raw.sideCenterOffset * (z.1 + raw.outerHalfWidth) -
          (z.2 - 1) := by
    have hsideRelation :
        2 * raw.sideCenterOffset * raw.outerHalfWidth -
            raw.sideCenterOffset ^ 2 = 3 / 4 := by
      unfold CMVFigureFour.circleValue leftCenter at hpLeft
      dsimp only at hpLeft
      nlinarith [hwidthSq]
    unfold CMVFigureFour.circleValue upperCenter leftCenter
    dsimp only
    rw [hRcos]
    ring_nf
    nlinarith
  have residual_frontier
      {z : PlanePoint} (hzx : z.1 < 0) (hzy : 0 < z.2)
      (hzero :
        CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius z = 0 ∨
          CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius z = 0)
      (huNonneg : 0 ≤ CMVFigureFour.circleValue raw.upperCenter
        raw.sourceRadius z)
      (hlNonneg : 0 ≤ CMVFigureFour.circleValue raw.leftCenter
        raw.sourceRadius z) :
      z ∈ frontier raw.centeredCarrier := by
    let H := horizontalTranslation raw.horizontalPlacement
    have pull_frontier
        (hplaced : H z ∈ frontier raw.carrier) :
        z ∈ frontier raw.centeredCarrier := by
      change H z ∈ frontier (H '' raw.centeredCarrier) at hplaced
      rw [← H.image_frontier] at hplaced
      rcases hplaced with ⟨w, hw, hwz⟩
      have hwEq : w = z := H.injective hwz
      simpa [hwEq] using hw
    rcases hzero with hu | hl
    · have huSide : 1 ≤ z.2 := by
        by_contra hnot
        have hyLt : z.2 < 1 := lt_of_not_ge hnot
        have hySq :
            (z.2 - (1 / 2 : ℝ)) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
          nlinarith
        have hxLt : z.1 < -raw.outerHalfWidth := by
          unfold CMVFigureFour.circleValue upperCenter at hu
          dsimp only at hu
          rw [hRcos] at hu
          nlinarith [sq_nonneg (z.1 + raw.outerHalfWidth)]
        have hd := hdiff z
        nlinarith
      apply pull_frontier
      rw [CMVFigureFourTargetGeometry.RawFourArcCoordinates.frontier_carrier_eq_four_circles
        raw h.toGeometry]
      apply Or.inl
      apply Or.inl
      apply Or.inl
      refine ⟨?_, ?_⟩
      · simpa only [H,
          CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedUpperCenter,
          CMVFigureFour.circleValue_horizontalTranslation] using hu
      · change 1 ≤ (H z).2
        simpa only [H, horizontalTranslation_apply] using huSide
    · have hlSide : z.2 ≤ 1 := by
        by_contra hnot
        have hyTop : 1 < z.2 := lt_of_not_ge hnot
        have hxRight : -raw.outerHalfWidth < z.1 := by
          by_contra hxnot
          have hxLeft : z.1 ≤ -raw.outerHalfWidth := le_of_not_gt hxnot
          have hqCenter : z.1 ≤ raw.leftCenter.1 :=
            hxLeft.trans hpLeCenter
          have hprod : 0 ≤
              (-raw.outerHalfWidth - z.1) *
                (2 * raw.leftCenter.1 + raw.outerHalfWidth - z.1) :=
            mul_nonneg (by linarith) (by linarith)
          unfold CMVFigureFour.circleValue leftCenter at hl hpLeft
          simp only [leftCenter] at hpLeCenter hqCenter hprod
          dsimp only at hl hpLeft hpLeCenter hqCenter hprod
          nlinarith
        have hd := hdiff z
        nlinarith
      have hxLeft : z.1 ≤ -raw.outerHalfWidth := by
        by_contra hnot
        have hxRight : -raw.outerHalfWidth < z.1 := lt_of_not_ge hnot
        unfold CMVFigureFour.circleValue upperCenter at huNonneg
        dsimp only at huNonneg
        rw [hRcos] at huNonneg
        nlinarith [sq_nonneg (z.1 + raw.outerHalfWidth),
          sq_nonneg (z.2 - (1 / 2 : ℝ))]
      apply pull_frontier
      rw [CMVFigureFourTargetGeometry.RawFourArcCoordinates.frontier_carrier_eq_four_circles
        raw h.toGeometry]
      apply Or.inl
      apply Or.inr
      refine ⟨?_, ?_, ?_⟩
      · simpa only [H,
          CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter,
          CMVFigureFour.circleValue_horizontalTranslation] using hl
      · simpa [H, horizontalTranslation_apply] using
          (abs_le.mpr ⟨by linarith, hlSide⟩)
      · simpa [H, horizontalTranslation_apply,
          CMVFigureFour.HorizontalCircleBranch.Holds,
          CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter] using
            hxLeft.trans hpLeCenter
  constructor
  · intro hqInterior
    have hclosed :=
      (raw.centered_upperLeft_closedModel h hx hy).1
        (interior_subset hqInterior)
    by_cases huLt :
        CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q < 0
    · exact Or.inl huLt
    by_cases hlLt :
        CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q < 0
    · exact Or.inr hlLt
    have huNonneg := le_of_not_gt huLt
    have hlNonneg := le_of_not_gt hlLt
    have hzero :
        CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q = 0 ∨
          CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q = 0 := by
      rcases hclosed with huLe | hlLe
      · exact Or.inl (le_antisymm huLe huNonneg)
      · exact Or.inr (le_antisymm hlLe hlNonneg)
    have hfront := residual_frontier hx hy hzero huNonneg hlNonneg
    exact False.elim
      (Set.disjoint_left.1 disjoint_interior_frontier hqInterior hfront)
  · intro hstrict
    let V : Set PlanePoint := {z | z.1 < 0 ∧ 0 < z.2}
    let M : Set PlanePoint := {z |
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius z < 0 ∨
        CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius z < 0}
    have hVopen : IsOpen V :=
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const continuous_snd)
    have hcircleUpper :
        Continuous (CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius) := by
      unfold CMVFigureFour.circleValue
      fun_prop
    have hcircleLeft :
        Continuous (CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius) := by
      unfold CMVFigureFour.circleValue
      fun_prop
    have hMopen : IsOpen M :=
      (isOpen_lt hcircleUpper continuous_const).union
        (isOpen_lt hcircleLeft continuous_const)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset
      ((hVopen.inter hMopen).mem_nhds ⟨⟨hx, hy⟩, hstrict⟩)
    rintro z ⟨⟨hzx, hzy⟩, hzM⟩
    exact (raw.centered_upperLeft_closedModel h hzx hzy).2
      (hzM.imp le_of_lt le_of_lt)
private def reflectX : PlanePoint ≃ₜ PlanePoint where
  toFun q := (-q.1, q.2)
  invFun q := (-q.1, q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] private theorem reflectX_apply (q : PlanePoint) :
    reflectX q = (-q.1, q.2) := rfl

private def reflectY : PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1, -q.2)
  invFun q := (q.1, -q.2)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] private theorem reflectY_apply (q : PlanePoint) :
    reflectY q = (q.1, -q.2) := rfl

private theorem centeredCarrier_reflectX (raw : RawFourArcCoordinates)
    (q : PlanePoint) :
    reflectX q ∈ raw.centeredCarrier ↔ q ∈ raw.centeredCarrier := by
  have hrect : reflectX q ∈ raw.rectangleCarrier ↔
      q ∈ raw.rectangleCarrier := by
    simp only [reflectX_apply, rectangleCarrier, mem_ofPred_eq, neg_le, neg_neg]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
      exact ⟨by linarith, by linarith, h₃⟩
  have hleft : reflectX q ∈ raw.leftSegmentCarrier ↔
      q ∈ raw.rightSegmentCarrier := by
    simp only [reflectX_apply, leftSegmentCarrier, rightSegmentCarrier,
      mem_ofPred_eq, leftCenter, rightCenter]
    constructor <;> rintro ⟨hcircle, hx, hy⟩ <;>
      refine ⟨?_, by linarith, hy⟩ <;> nlinarith
  have hright : reflectX q ∈ raw.rightSegmentCarrier ↔
      q ∈ raw.leftSegmentCarrier := by
    simp only [reflectX_apply, leftSegmentCarrier, rightSegmentCarrier,
      mem_ofPred_eq, leftCenter, rightCenter]
    constructor <;> rintro ⟨hcircle, hx, hy⟩ <;>
      refine ⟨?_, by linarith, hy⟩ <;> nlinarith
  have hupper : reflectX q ∈ raw.upperCapCarrier ↔
      q ∈ raw.upperCapCarrier := by
    simp only [reflectX_apply, upperCapCarrier, mem_ofPred_eq, upperCenter]
    constructor <;> rintro ⟨hcircle, hy⟩ <;>
      refine ⟨?_, hy⟩ <;> nlinarith
  have hlower : reflectX q ∈ raw.lowerCapCarrier ↔
      q ∈ raw.lowerCapCarrier := by
    simp only [reflectX_apply, lowerCapCarrier, mem_ofPred_eq, lowerCenter]
    constructor <;> rintro ⟨hcircle, hy⟩ <;>
      refine ⟨?_, hy⟩ <;> nlinarith
  simp only [centeredCarrier, mem_union]
  rw [hrect, hleft, hright, hupper, hlower]
  tauto

private theorem centeredCarrier_reflectY (raw : RawFourArcCoordinates)
    (q : PlanePoint) :
    reflectY q ∈ raw.centeredCarrier ↔ q ∈ raw.centeredCarrier := by
  have hrect : reflectY q ∈ raw.rectangleCarrier ↔
      q ∈ raw.rectangleCarrier := by
    simp only [reflectY_apply, rectangleCarrier, mem_ofPred_eq, abs_neg]
  have hleft : reflectY q ∈ raw.leftSegmentCarrier ↔
      q ∈ raw.leftSegmentCarrier := by
    simp only [reflectY_apply, leftSegmentCarrier, mem_ofPred_eq, leftCenter,
      abs_neg]
    constructor <;> rintro ⟨hcircle, hx, hy⟩ <;>
      refine ⟨?_, hx, hy⟩ <;> nlinarith
  have hright : reflectY q ∈ raw.rightSegmentCarrier ↔
      q ∈ raw.rightSegmentCarrier := by
    simp only [reflectY_apply, rightSegmentCarrier, mem_ofPred_eq, rightCenter,
      abs_neg]
    constructor <;> rintro ⟨hcircle, hx, hy⟩ <;>
      refine ⟨?_, hx, hy⟩ <;> nlinarith
  have hupper : reflectY q ∈ raw.upperCapCarrier ↔
      q ∈ raw.lowerCapCarrier := by
    simp only [reflectY_apply, upperCapCarrier, lowerCapCarrier, mem_ofPred_eq,
      upperCenter, lowerCenter]
    constructor <;> rintro ⟨hcircle, hy⟩ <;>
      refine ⟨?_, by linarith⟩ <;> nlinarith
  have hlower : reflectY q ∈ raw.lowerCapCarrier ↔
      q ∈ raw.upperCapCarrier := by
    simp only [reflectY_apply, upperCapCarrier, lowerCapCarrier, mem_ofPred_eq,
      upperCenter, lowerCenter]
    constructor <;> rintro ⟨hcircle, hy⟩ <;>
      refine ⟨?_, by linarith⟩ <;> nlinarith
  simp only [centeredCarrier, mem_union]
  rw [hrect, hleft, hright, hupper, hlower]
  tauto

private theorem interior_centeredCarrier_reflectX (raw : RawFourArcCoordinates)
    (q : PlanePoint) :
    reflectX q ∈ interior raw.centeredCarrier ↔ q ∈ interior raw.centeredCarrier := by
  have himage : reflectX '' raw.centeredCarrier = raw.centeredCarrier := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (raw.centeredCarrier_reflectX w).2 hw
    · intro hz
      refine ⟨reflectX z, (raw.centeredCarrier_reflectX z).2 hz, ?_⟩
      simp only [reflectX_apply, neg_neg]
  constructor
  · intro hq
    rw [← himage] at hq
    rw [← reflectX.image_interior] at hq
    rcases hq with ⟨w, hw, hwq⟩
    have : w = q := reflectX.injective (by simpa [reflectX] using hwq)
    simpa [this] using hw
  · intro hq
    rw [← himage]
    rw [← reflectX.image_interior]
    exact ⟨q, hq, rfl⟩

private theorem interior_centeredCarrier_reflectY (raw : RawFourArcCoordinates)
    (q : PlanePoint) :
    reflectY q ∈ interior raw.centeredCarrier ↔ q ∈ interior raw.centeredCarrier := by
  have himage : reflectY '' raw.centeredCarrier = raw.centeredCarrier := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (raw.centeredCarrier_reflectY w).2 hw
    · intro hz
      refine ⟨reflectY z, (raw.centeredCarrier_reflectY z).2 hz, ?_⟩
      simp only [reflectY_apply, neg_neg]
  constructor
  · intro hq
    rw [← himage] at hq
    rw [← reflectY.image_interior] at hq
    rcases hq with ⟨w, hw, hwq⟩
    have : w = q := reflectY.injective (by simpa [reflectY] using hwq)
    simpa [this] using hw
  · intro hq
    rw [← himage]
    rw [← reflectY.image_interior]
    exact ⟨q, hq, rfl⟩


theorem centered_upperRight_interiorModel (raw : RawFourArcCoordinates)
    (h : raw.SatisfiesClosedSnell 2) {q : PlanePoint}
    (hx : 0 < q.1) (hy : 0 < q.2) :
    q ∈ interior raw.centeredCarrier ↔
      CMVFigureFour.circleValue raw.upperCenter raw.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue raw.rightCenter raw.sourceRadius q < 0 := by
  have hz := raw.centered_upperLeft_interiorModel h
    (q := reflectX q) (by simp [reflectX]; linarith) (by simpa [reflectX] using hy)
  rw [raw.interior_centeredCarrier_reflectX q] at hz
  simp only [reflectX_apply, CMVFigureFour.circleValue, upperCenter, leftCenter,
    rightCenter] at hz ⊢
  ring_nf at hz ⊢
  exact hz

theorem centered_lowerLeft_interiorModel (raw : RawFourArcCoordinates)
    (h : raw.SatisfiesClosedSnell 2) {q : PlanePoint}
    (hx : q.1 < 0) (hy : q.2 < 0) :
    q ∈ interior raw.centeredCarrier ↔
      CMVFigureFour.circleValue raw.lowerCenter raw.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue raw.leftCenter raw.sourceRadius q < 0 := by
  have hz := raw.centered_upperLeft_interiorModel h
    (q := reflectY q) (by simpa [reflectY] using hx)
      (by simp [reflectY]; linarith)
  rw [raw.interior_centeredCarrier_reflectY q] at hz
  simp only [reflectY_apply, CMVFigureFour.circleValue, upperCenter, lowerCenter,
    leftCenter] at hz ⊢
  ring_nf at hz ⊢
  exact hz

theorem centered_lowerRight_interiorModel (raw : RawFourArcCoordinates)
    (h : raw.SatisfiesClosedSnell 2) {q : PlanePoint}
    (hx : 0 < q.1) (hy : q.2 < 0) :
    q ∈ interior raw.centeredCarrier ↔
      CMVFigureFour.circleValue raw.lowerCenter raw.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue raw.rightCenter raw.sourceRadius q < 0 := by
  have hz := raw.centered_lowerLeft_interiorModel h
    (q := reflectX q) (by simp [reflectX]; linarith) (by simpa [reflectX] using hy)
  rw [raw.interior_centeredCarrier_reflectX q] at hz
  simp only [reflectX_apply, CMVFigureFour.circleValue, lowerCenter, leftCenter,
    rightCenter] at hz ⊢
  ring_nf at hz ⊢
  exact hz
variable (raw : CMVSourceClassification.RawFourArcCoordinates)

private theorem eventually_placed_twoCircle_interiorModel
    (p c d placedC placedD : PlanePoint) (V : Set PlanePoint)
    (hVopen : IsOpen V) (hpV : p ∈ V)
    (hplacedC : placedC = horizontalTranslation raw.horizontalPlacement c)
    (hplacedD : placedD = horizontalTranslation raw.horizontalPlacement d)
    (hmodel : ∀ {z : PlanePoint},
      horizontalTranslation raw.horizontalPlacement z ∈ V →
      (z ∈ interior raw.centeredCarrier ↔
        CMVFigureFour.circleValue c raw.sourceRadius z < 0 ∨
          CMVFigureFour.circleValue d raw.sourceRadius z < 0)) :
    ∀ᶠ q in 𝓝 p,
      q ∈ interior raw.carrier ↔
        CMVFigureFour.circleValue placedC raw.sourceRadius q < 0 ∨
          CMVFigureFour.circleValue placedD raw.sourceRadius q < 0 := by
  let H := horizontalTranslation raw.horizontalPlacement
  apply Filter.mem_of_superset (hVopen.mem_nhds hpV)
  intro q hq
  let z : PlanePoint := (q.1 - raw.horizontalPlacement, q.2)
  have hqEq : H z = q := by
    apply Prod.ext <;> simp [H, z, horizontalTranslation_apply]
  have hinterior :
      q ∈ interior raw.carrier ↔ z ∈ interior raw.centeredCarrier := by
    change q ∈ interior (H '' raw.centeredCarrier) ↔ _
    rw [← H.image_interior]
    constructor
    · rintro ⟨w, hw, hwq⟩
      have hwz : w = z := H.injective (hwq.trans hqEq.symm)
      simpa [hwz] using hw
    · intro hz
      exact ⟨z, hz, hqEq⟩
  calc
    q ∈ interior raw.carrier ↔ z ∈ interior raw.centeredCarrier := hinterior
    _ ↔ CMVFigureFour.circleValue c raw.sourceRadius z < 0 ∨
        CMVFigureFour.circleValue d raw.sourceRadius z < 0 := hmodel (by
      change H z ∈ V
      rwa [hqEq])
    _ ↔ _ := by
      rw [hplacedC, hplacedD, ← hqEq]
      simp only [H, CMVFigureFour.circleValue_horizontalTranslation]

private theorem outerHalfWidth_pos (h : raw.SatisfiesClosedSnell 2) :
    0 < raw.outerHalfWidth := by
  unfold outerHalfWidth
  exact mul_pos (lt_of_lt_of_le zero_lt_one h.radius_ge_one)
    (sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
      (lt_trans h.exteriorHalfAngle_lt_pi_div_two (by linarith [Real.pi_pos])))

theorem eventually_upperLeft_interiorModel
    (h : raw.SatisfiesClosedSnell 2) :
    ∀ᶠ q in 𝓝 (CMVFigureFourTargetGeometry.RawFourArcCoordinates.upperLeftJunction raw),
      q ∈ interior raw.carrier ↔
        CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedUpperCenter raw)
            raw.sourceRadius q < 0 ∨
          CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter raw)
            raw.sourceRadius q < 0 := by
  let V : Set PlanePoint :=
    {q | q.1 < raw.horizontalPlacement ∧ 0 < q.2}
  apply raw.eventually_placed_twoCircle_interiorModel
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.upperLeftJunction raw)
    raw.upperCenter raw.leftCenter
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedUpperCenter raw)
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter raw) V
    ((isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt continuous_const continuous_snd))
  · change raw.horizontalPlacement - raw.outerHalfWidth < raw.horizontalPlacement ∧
      0 < (1 : ℝ)
    exact ⟨by linarith [raw.outerHalfWidth_pos h], zero_lt_one⟩
  · rfl
  · rfl
  · intro z hz
    have hz' :
        z.1 + raw.horizontalPlacement < raw.horizontalPlacement ∧ 0 < z.2 := by
      simpa [V, horizontalTranslation_apply] using hz
    exact raw.centered_upperLeft_interiorModel h (by linarith [hz'.1]) hz'.2

theorem eventually_upperRight_interiorModel
    (h : raw.SatisfiesClosedSnell 2) :
    ∀ᶠ q in 𝓝 (CMVFigureFourTargetGeometry.RawFourArcCoordinates.upperRightJunction raw),
      q ∈ interior raw.carrier ↔
        CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedUpperCenter raw)
            raw.sourceRadius q < 0 ∨
          CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedRightCenter raw)
            raw.sourceRadius q < 0 := by
  let V : Set PlanePoint :=
    {q | raw.horizontalPlacement < q.1 ∧ 0 < q.2}
  apply raw.eventually_placed_twoCircle_interiorModel
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.upperRightJunction raw)
    raw.upperCenter raw.rightCenter
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedUpperCenter raw)
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedRightCenter raw) V
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd))
  · change raw.horizontalPlacement < raw.horizontalPlacement + raw.outerHalfWidth ∧
      0 < (1 : ℝ)
    exact ⟨by linarith [raw.outerHalfWidth_pos h], zero_lt_one⟩
  · rfl
  · rfl
  · intro z hz
    have hz' :
        raw.horizontalPlacement < z.1 + raw.horizontalPlacement ∧ 0 < z.2 := by
      simpa [V, horizontalTranslation_apply] using hz
    exact raw.centered_upperRight_interiorModel h (by linarith [hz'.1]) hz'.2

theorem eventually_lowerLeft_interiorModel
    (h : raw.SatisfiesClosedSnell 2) :
    ∀ᶠ q in 𝓝 (CMVFigureFourTargetGeometry.RawFourArcCoordinates.lowerLeftJunction raw),
      q ∈ interior raw.carrier ↔
        CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLowerCenter raw)
            raw.sourceRadius q < 0 ∨
          CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter raw)
            raw.sourceRadius q < 0 := by
  let V : Set PlanePoint :=
    {q | q.1 < raw.horizontalPlacement ∧ q.2 < 0}
  apply raw.eventually_placed_twoCircle_interiorModel
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.lowerLeftJunction raw)
    raw.lowerCenter raw.leftCenter
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLowerCenter raw)
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLeftCenter raw) V
    ((isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt continuous_snd continuous_const))
  · change raw.horizontalPlacement - raw.outerHalfWidth < raw.horizontalPlacement ∧
      (-1 : ℝ) < 0
    exact ⟨by linarith [raw.outerHalfWidth_pos h], by norm_num⟩
  · rfl
  · rfl
  · intro z hz
    have hz' :
        z.1 + raw.horizontalPlacement < raw.horizontalPlacement ∧ z.2 < 0 := by
      simpa [V, horizontalTranslation_apply] using hz
    exact raw.centered_lowerLeft_interiorModel h (by linarith [hz'.1]) hz'.2

theorem eventually_lowerRight_interiorModel
    (h : raw.SatisfiesClosedSnell 2) :
    ∀ᶠ q in 𝓝 (CMVFigureFourTargetGeometry.RawFourArcCoordinates.lowerRightJunction raw),
      q ∈ interior raw.carrier ↔
        CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLowerCenter raw)
            raw.sourceRadius q < 0 ∨
          CMVFigureFour.circleValue
            (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedRightCenter raw)
            raw.sourceRadius q < 0 := by
  let V : Set PlanePoint :=
    {q | raw.horizontalPlacement < q.1 ∧ q.2 < 0}
  apply raw.eventually_placed_twoCircle_interiorModel
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.lowerRightJunction raw)
    raw.lowerCenter raw.rightCenter
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedLowerCenter raw)
    (CMVFigureFourTargetGeometry.RawFourArcCoordinates.placedRightCenter raw) V
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_snd continuous_const))
  · change raw.horizontalPlacement < raw.horizontalPlacement + raw.outerHalfWidth ∧
      (-1 : ℝ) < 0
    exact ⟨by linarith [raw.outerHalfWidth_pos h], by norm_num⟩
  · rfl
  · rfl
  · intro z hz
    have hz' :
        raw.horizontalPlacement < z.1 + raw.horizontalPlacement ∧ z.2 < 0 := by
      simpa [V, horizontalTranslation_apply] using hz
    exact raw.centered_lowerRight_interiorModel h (by linarith [hz'.1]) hz'.2
end CMVSourceClassification.RawFourArcCoordinates
namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

variable {E U : Set PlanePoint}

open SmoothGraphAtlas

open CMVBoundaryLocalAtlas.NonsmoothJunction

/-- Every density-two bilateral source has the four literal local circle
sublevel occupancies.  The proof uses the reconstructed raw carrier interior
and exact source-to-raw center and junction alignment. -/
theorem bilateral_junctionCircleOccupancy
    (g : CMVFigureFour.BilateralSourceIncidence 2) :
    BilateralJunctionCircleOccupancy g := by
  let s := g.toSourceGeometry
  let raw := s.toRawFourArcCoordinates
  have hsnell : raw.SatisfiesClosedSnell 2 :=
    s.toRawFourArcCoordinates_satisfiesClosedSnell
  have hrepresentative : g.representative = interior raw.carrier := by
    exact s.representative_eq_interior_raw_carrier
  have halign :=
    CMVFigureFourTargetGeometry.SourceAlignment.centers_and_junctions_align s
  rcases halign with ⟨hleft, hright, hupper, hlower,
    hupperLeft, hupperRight, hlowerLeft, hlowerRight⟩
  constructor
  · rw [hrepresentative]
    change ∀ᶠ q in 𝓝 s.upperLeft, q ∈ interior raw.carrier ↔
      CMVFigureFour.circleValue s.upperCenter s.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue s.leftStripCenter s.sourceRadius q < 0
    rw [hupperLeft, hupper, hleft]
    exact raw.eventually_upperLeft_interiorModel hsnell
  · rw [hrepresentative]
    change ∀ᶠ q in 𝓝 s.upperRight, q ∈ interior raw.carrier ↔
      CMVFigureFour.circleValue s.upperCenter s.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue s.rightStripCenter s.sourceRadius q < 0
    rw [hupperRight, hupper, hright]
    exact raw.eventually_upperRight_interiorModel hsnell
  · rw [hrepresentative]
    change ∀ᶠ q in 𝓝 s.lowerLeft, q ∈ interior raw.carrier ↔
      CMVFigureFour.circleValue s.lowerCenter s.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue s.leftStripCenter s.sourceRadius q < 0
    rw [hlowerLeft, hlower, hleft]
    exact raw.eventually_lowerLeft_interiorModel hsnell
  · rw [hrepresentative]
    change ∀ᶠ q in 𝓝 s.lowerRight, q ∈ interior raw.carrier ↔
      CMVFigureFour.circleValue s.lowerCenter s.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue s.rightStripCenter s.sourceRadius q < 0
    rw [hlowerRight, hlower, hright]
    exact raw.eventually_lowerRight_interiorModel hsnell
/-- Build the unchanged topology input from source-local oriented smooth graph
regularity on the supplied open representative.  Selected-frontier points are
first restricted to the original frontier and the germs are then transported
through AE selection.  Representative, section, and connectedness hypotheses
remain explicit; ambient half-space charts are derived here. -/
noncomputable def ofOrientedSmoothBoundaryGraphAtlas
    (representative_nonempty : U.Nonempty)
    (representative_open : IsOpen U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (localRegularity :
      HasOrientedSmoothBoundaryGraphAtlas U) :
    SelectedBoundaryTopologyInput E U where
  representative_nonempty := representative_nonempty
  representative_open := representative_open
  representative_bounded := representative_bounded
  representative_connected := representative_connected
  carrier_ae := carrier_ae
  interval_sections := interval_sections
  local_atlas :=
    (localRegularity.selected representative_open carrier_ae)
      |>.toBoundaryHalfSpaceAtlas

/-- Build the unchanged topology input directly from the relaxation's literal
smooth-domain regularity.  Openness and all pointwise graph germs are derived
from that one source-faithful certificate. -/
noncomputable def ofSmoothDomain
    (representative_nonempty : U.Nonempty)
    (representative_smooth : CMVRelaxation.IsSmoothDomain U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E) :
    SelectedBoundaryTopologyInput E U :=
  ofOrientedSmoothBoundaryGraphAtlas representative_nonempty
    representative_smooth.isOpen representative_bounded
    representative_connected carrier_ae interval_sections
    (HasOrientedSmoothBoundaryGraphAtlas.of_isSmoothDomain
      representative_smooth)

/-- Literal four-circle reconstruction makes every bilateral representative
nonempty; this is derived from the raw carrier interior, not stored in the
incidence record. -/
theorem bilateral_representative_nonempty
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam) :
    g.representative.Nonempty := by
  let s := g.toSourceGeometry
  change s.representative.Nonempty
  rw [s.representative_eq_interior_raw_carrier]
  exact s.toRawFourArcCoordinates.interior_carrier_nonempty
    s.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry

/-- The same literal interior is path connected, hence connected. -/
theorem bilateral_representative_connected
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam) :
    IsConnected g.representative := by
  let s := g.toSourceGeometry
  change IsConnected s.representative
  rw [s.representative_eq_interior_raw_carrier]
  exact (s.toRawFourArcCoordinates.isPathConnected_interior_carrier
    s.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry).isConnected

/-- Almost-everywhere interval sections are inherited from the literal raw
four-arc carrier through planar AE equality. -/
theorem bilateral_hasAEIntervalHorizontalSections
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam) :
    CMVRelaxation.HasAEIntervalHorizontalSections g.sourceCarrier := by
  let s := g.toSourceGeometry
  let raw := s.toRawFourArcCoordinates
  have hgeometry : raw.SatisfiesClosedGeometry :=
    s.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry
  have hrepresentative :
      s.representative =ᵐ[volume] interior raw.carrier :=
    Filter.EventuallyEq.of_eq s.representative_eq_interior_raw_carrier
  have hsourceRaw : s.sourceCarrier =ᵐ[volume] raw.carrier :=
    s.sourceRepresentative.source_ae_representative.trans
      (hrepresentative.trans
        (CMVFigureFourTargetGeometry.RawFourArcCoordinates.interior_carrier_ae_eq_carrier
          raw hgeometry))
  have hslices :=
    CMVRelaxation.ae_horizontalSection_congr_ae hsourceRaw
  have hcentered :=
    raw.hasCenteredHorizontalIntervalSections hgeometry
  change CMVRelaxation.HasAEIntervalHorizontalSections s.sourceCarrier
  filter_upwards [hslices, hcentered] with y hsource hraw
  rcases hraw with ⟨length, _hlength, hsection⟩
  exact ⟨Icc (raw.horizontalPlacement - length / 2)
      (raw.horizontalPlacement + length / 2),
    Set.ordConnected_Icc, hsource.trans hsection⟩

/-- Build the unchanged topology input for a bilateral four-circle source with
four genuine nonsmooth junction germs.  All regular frontier points are
discharged from the complete four-trace frontier and local circle
one-sidedness; all global topology and section prerequisites are derived from
the literal raw source geometry. -/
noncomputable def ofBilateralJunctionGraphGerms
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam)
    (junctions :
      CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionGraphGerms g) :
    SelectedBoundaryTopologyInput g.sourceCarrier g.representative where
  representative_nonempty := bilateral_representative_nonempty g
  representative_open := g.sourceRepresentative.representative_open
  representative_bounded := g.sourceRepresentative.representative_bounded
  representative_connected := bilateral_representative_connected g
  carrier_ae := g.sourceRepresentative.source_ae_representative
  interval_sections := bilateral_hasAEIntervalHorizontalSections g
  local_atlas := junctions.selectedBoundaryHalfSpaceAtlas
    g.sourceRepresentative.source_ae_representative

/-- Source-facing constructor: four literal circle-sublevel exhaustions are
converted to joined max/min germs internally, then combined with all regular
circle points.  No graph, atlas, smooth-domain certificate, or trace is
supplied. -/
noncomputable def ofBilateralJunctionCircleOccupancy
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam)
    (occupied :
      CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionCircleOccupancy g) :
    SelectedBoundaryTopologyInput g.sourceCarrier g.representative :=
  ofBilateralJunctionGraphGerms g occupied.toJunctionGraphGerms

/-- Complete source-applicability constructor at density two.  It derives the
four nonsmooth junction germs and every regular circle chart from the literal
bilateral source geometry; callers supply no local atlas data. -/
noncomputable def ofBilateralSource
    (g : CMVFigureFour.BilateralSourceIncidence 2) :
    SelectedBoundaryTopologyInput g.sourceCarrier g.representative :=
  ofBilateralJunctionCircleOccupancy g (bilateral_junctionCircleOccupancy g)

/-- The completed simple loop packaged in the unchanged source-boundary trace
interface, on the selected representative only. -/
noncomputable def closedBoundaryTrace
    (D : SelectedBoundaryTopologyInput E U) :
    CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
      (CMVRelaxation.aeOpenRepresentative E) where
  trace := D.completedBoundaryLoop
  start := 0
  finish := 2
  start_le_finish := by norm_num
  trace_closed := D.completedBoundaryLoop_closed
  complete_image := D.image_completedBoundaryLoop_Icc

/-- Continuity deliberately exported beside, rather than added to, the
unchanged weak source trace record. -/
theorem continuous_closedBoundaryTrace
    (D : SelectedBoundaryTopologyInput E U) :
    Continuous D.closedBoundaryTrace.trace :=
  D.continuous_completedBoundaryLoop

/-- The constructed trace has a genuinely positive parameter length. -/
theorem closedBoundaryTrace_start_lt_finish
    (D : SelectedBoundaryTopologyInput E U) :
    D.closedBoundaryTrace.start < D.closedBoundaryTrace.finish := by
  change (0 : ℝ) < 2
  norm_num

/-- No vertex or positive-length piece is repeated before the terminal point. -/
theorem closedBoundaryTrace_injOn_Ico
    (D : SelectedBoundaryTopologyInput E U) :
    Set.InjOn D.closedBoundaryTrace.trace
      (Set.Ico D.closedBoundaryTrace.start D.closedBoundaryTrace.finish) := by
  simpa only [closedBoundaryTrace] using D.completedBoundaryLoop_injOn_Ico

/-- The literal-junction source constructor exercises the unchanged simple-loop
producer without a minimizer premise. -/
theorem exists_closedBoundaryTrace_of_bilateralJunctionCircleOccupancy
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam)
    (occupied :
      CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionCircleOccupancy g) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative g.sourceCarrier),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace
          (Set.Ico boundary.start boundary.finish) ∧
        boundary.trace '' Set.Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative g.sourceCarrier) := by
  let D : SelectedBoundaryTopologyInput g.sourceCarrier g.representative :=
    ofBilateralJunctionCircleOccupancy g occupied
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image⟩

/-- Source minimality transfers to the selected representative solely by the
concrete relaxation's planar-AE invariance.  The density hypothesis records the
CMV admissible range but is not needed by the invariant itself. -/
theorem selectedRepresentative_isMinimizer_of_source
    (D : SelectedBoundaryTopologyInput E U) {lam : ℝ} (_hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
      (CMVRelaxation.aeOpenRepresentative E) :=
  (CMVRelaxation.relaxedSourceSemantics_isMinimizer_aeOpenRepresentative_iff
    lam D.representative_open D.carrier_ae).2 hsource

/-- Conversely, selected-representative minimality transports back only through
the same planar-AE invariant semantics. -/
theorem source_isMinimizer_of_selectedRepresentative
    (D : SelectedBoundaryTopologyInput E U) {lam : ℝ} (_hlam : 1 < lam)
    (hselected : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
      (CMVRelaxation.aeOpenRepresentative E)) :
    (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E :=
  (CMVRelaxation.relaxedSourceSemantics_isMinimizer_aeOpenRepresentative_iff
    lam D.representative_open D.carrier_ae).1 hselected

/-- End-to-end selected-boundary construction from pointwise smooth graph germs
on the supplied open representative.  No selected-set germ, ambient half-space
chart, connected frontier, or global boundary curve is supplied.  Minimality
crosses from the original carrier only through planar almost-everywhere
invariance. -/
theorem exists_closedBoundaryTrace_of_orientedSmoothBoundaryGraphAtlas
    {lam : ℝ}
    (representative_nonempty : U.Nonempty)
    (representative_open : IsOpen U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (localRegularity :
      HasOrientedSmoothBoundaryGraphAtlas U)
    (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Set.Ico boundary.start boundary.finish) ∧
        boundary.trace '' Set.Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        IsConnected (frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) := by
  let D : SelectedBoundaryTopologyInput E U :=
    ofOrientedSmoothBoundaryGraphAtlas representative_nonempty
      representative_open representative_bounded representative_connected
      carrier_ae interval_sections localRegularity
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image,
    D.isConnected_frontier_aeOpenRepresentative,
    D.selectedRepresentative_isMinimizer_of_source hlam hsource⟩

/-- The literal `IsSmoothDomain` contract discharges both openness and every
pointwise oriented graph germ.  Thus no atlas or local chart is supplied by the
caller; representative boundedness, connectedness, nonemptiness, and the
almost-everywhere interval-section theorem remain explicit geometric inputs. -/
theorem exists_closedBoundaryTrace_of_smoothDomain
    {lam : ℝ}
    (representative_nonempty : U.Nonempty)
    (representative_smooth : CMVRelaxation.IsSmoothDomain U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Set.Ico boundary.start boundary.finish) ∧
        boundary.trace '' Set.Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        IsConnected (frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) := by
  let D : SelectedBoundaryTopologyInput E U :=
    ofSmoothDomain representative_nonempty representative_smooth
      representative_bounded representative_connected carrier_ae
      interval_sections
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image,
    D.isConnected_frontier_aeOpenRepresentative,
    D.selectedRepresentative_isMinimizer_of_source hlam hsource⟩

/-- End-to-end selected simple loop for a bilateral source whose four
nonsmooth junction germs have been derived from the literal source geometry.
No global smooth-domain certificate, prebuilt atlas, or boundary trace is an
input. -/
theorem exists_closedBoundaryTrace_of_bilateralJunctionGraphGerms
    {lam : ℝ} (g : CMVFigureFour.BilateralSourceIncidence lam)
    (junctions :
      CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionGraphGerms g)
    (hlam : 1 < lam)
    (hsource :
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
        g.sourceCarrier) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative g.sourceCarrier),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Set.Ico boundary.start boundary.finish) ∧
        boundary.trace '' Set.Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative g.sourceCarrier) ∧
        IsConnected
          (frontier (CMVRelaxation.aeOpenRepresentative g.sourceCarrier)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative g.sourceCarrier) := by
  let D : SelectedBoundaryTopologyInput g.sourceCarrier g.representative :=
    ofBilateralJunctionGraphGerms g junctions
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image,
    D.isConnected_frontier_aeOpenRepresentative,
    D.selectedRepresentative_isMinimizer_of_source hlam hsource⟩


/-- Compose the selected-representative loop and AE minimizer transport with
the still-explicit Figure-3 branch data.  No geometric label, Snell law,
symmetry, or circular-continuation premise is produced here. -/
noncomputable def toRegularFigureThreeBoundaryConfiguration
    (D : SelectedBoundaryTopologyInput E U) {lam : ℝ}
    (hsource :
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E)
    (orientation : CMVFigureThree.VerticalOrientation)
    (sourceRadius symmetryAxisX : ℝ)
    (primaryExterior addedExterior : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ)
    (regularSnell :
      CMVFigureThree.SourceBoundaryExtraction.RegularSnellData lam orientation
        sourceRadius primaryExterior addedExterior)
    (verticalSymmetry :
      CMVFigureThree.SourceBoundaryExtraction.VerticalSymmetryData orientation
        primaryExterior symmetryAxisX leftTangentX rightTangentX)
    (circularContinuation :
      CMVFigureThree.SourceBoundaryExtraction.CircularContinuationData
        orientation sourceRadius primaryExterior leftTangentX rightTangentX)
    (figureThreeBranch :
      CMVFigureThree.SourceBoundaryExtraction.FigureThreeBranchSelection
        (CMVRelaxation.aeOpenRepresentative E) orientation sourceRadius
        primaryExterior addedExterior leftTangentX rightTangentX
        D.closedBoundaryTrace) :
    CMVFigureThree.RegularFigureThreeBoundaryConfiguration lam
      (CMVRelaxation.relaxedSourceSemantics lam) where
  carrier := CMVRelaxation.aeOpenRepresentative E
  source_minimizer :=
    D.selectedRepresentative_isMinimizer_of_source
      regularSnell.density_jump hsource
  orientation := orientation
  sourceRadius := sourceRadius
  symmetryAxisX := symmetryAxisX
  primaryExterior := primaryExterior
  addedExterior := addedExterior
  leftTangentX := leftTangentX
  rightTangentX := rightTangentX
  regularSnell := regularSnell
  verticalSymmetry := verticalSymmetry
  circularContinuation := circularContinuation
  boundaryCurve := D.closedBoundaryTrace
  figureThreeBranch := figureThreeBranch

/-- Once the explicit Figure-3 labels and local geometric data have been
supplied on the selected loop, the retained non-fit consumer leaves only the
radius-one residual. -/
theorem figureThree_sourceRadius_eq_one
    (D : SelectedBoundaryTopologyInput E U) {lam : ℝ}
    (hsource :
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E)
    (orientation : CMVFigureThree.VerticalOrientation)
    (sourceRadius symmetryAxisX : ℝ)
    (primaryExterior addedExterior : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ)
    (regularSnell :
      CMVFigureThree.SourceBoundaryExtraction.RegularSnellData lam orientation
        sourceRadius primaryExterior addedExterior)
    (verticalSymmetry :
      CMVFigureThree.SourceBoundaryExtraction.VerticalSymmetryData orientation
        primaryExterior symmetryAxisX leftTangentX rightTangentX)
    (circularContinuation :
      CMVFigureThree.SourceBoundaryExtraction.CircularContinuationData
        orientation sourceRadius primaryExterior leftTangentX rightTangentX)
    (figureThreeBranch :
      CMVFigureThree.SourceBoundaryExtraction.FigureThreeBranchSelection
        (CMVRelaxation.aeOpenRepresentative E) orientation sourceRadius
        primaryExterior addedExterior leftTangentX rightTangentX
        D.closedBoundaryTrace) :
    sourceRadius = 1 :=
  (D.toRegularFigureThreeBoundaryConfiguration hsource orientation
    sourceRadius symmetryAxisX primaryExterior addedExterior leftTangentX
    rightTangentX regularSnell verticalSymmetry circularContinuation
    figureThreeBranch).sourceRadius_eq_one


namespace BilateralJunctionApplications

abbrev strictNegThreeSource : CMVFigureFour.BilateralSourceIncidence 2 :=
  CMVFigureFour.Examples.strictBilateralSourceAt (-3)

abbrev endpointSevenSource : CMVFigureFour.BilateralSourceIncidence 2 :=
  CMVFigureFour.Examples.endpointBilateralSourceAt 7

/-- Exact nonzero strict placement specialized through every derived local and
global prerequisite. -/
noncomputable def strictNegThreeTopologyInput :
    SelectedBoundaryTopologyInput strictNegThreeSource.sourceCarrier
      strictNegThreeSource.representative :=
  ofBilateralSource strictNegThreeSource

/-- The specialized strict source reaches the completed simple-loop producer,
including every regular coordinate tangency and all four junctions. -/
theorem strictNegThree_completedBoundaryLoop_contract :
    let D := strictNegThreeTopologyInput
    Continuous D.completedBoundaryLoop ∧
      D.completedBoundaryLoop 0 = D.completedBoundaryLoop 2 ∧
      Set.InjOn D.completedBoundaryLoop (Set.Ico 0 2) ∧
      D.completedBoundaryLoop '' Set.Icc 0 2 =
        frontier
          (CMVRelaxation.aeOpenRepresentative
            strictNegThreeSource.sourceCarrier) := by
  dsimp only
  exact ⟨strictNegThreeTopologyInput.continuous_completedBoundaryLoop,
    strictNegThreeTopologyInput.completedBoundaryLoop_closed,
    strictNegThreeTopologyInput.completedBoundaryLoop_injOn_Ico,
    strictNegThreeTopologyInput.image_completedBoundaryLoop_Icc⟩

/-- Exact radius-one placement specialized through the same source constructor. -/
noncomputable def endpointSevenTopologyInput :
    SelectedBoundaryTopologyInput endpointSevenSource.sourceCarrier
      endpointSevenSource.representative :=
  ofBilateralSource endpointSevenSource

/-- The radius-one branch exercises the same completed simple-loop producer;
no determinant test rejects its collinear tangent rays. -/
theorem endpointSeven_completedBoundaryLoop_contract :
    let D := endpointSevenTopologyInput
    Continuous D.completedBoundaryLoop ∧
      D.completedBoundaryLoop 0 = D.completedBoundaryLoop 2 ∧
      Set.InjOn D.completedBoundaryLoop (Set.Ico 0 2) ∧
      D.completedBoundaryLoop '' Set.Icc 0 2 =
        frontier
          (CMVRelaxation.aeOpenRepresentative
            endpointSevenSource.sourceCarrier) := by
  dsimp only
  exact ⟨endpointSevenTopologyInput.continuous_completedBoundaryLoop,
    endpointSevenTopologyInput.completedBoundaryLoop_closed,
    endpointSevenTopologyInput.completedBoundaryLoop_injOn_Ico,
    endpointSevenTopologyInput.image_completedBoundaryLoop_Icc⟩

end BilateralJunctionApplications

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
