/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourScalarReduction
import CMVFiniteJunctionDisagreement

/-!
# Literal target geometry for CMV Figure 4

This module aligns the actual Figure-4 supporting circles with the horizontally
placed raw closed-Snell target.  It also records the target-local membership
interface away from a supporting circle; the target itself is closed, so no
membership assertion is made on the null supporting circle.
-/

open Set
open Real

noncomputable section

namespace CMVFigureFourTargetGeometry

/-- Local membership in a fixed circle side away from the supporting circle.
Unlike `CMVFiniteJunctionDisagreement.LocallyOnCircleSide`, this interface is
appropriate for the literal closed target: boundary membership is deliberately
ignored. -/
def LocallyOnCircleSideAway (K : Set PlanePoint) (center : PlanePoint)
    (radius : ℝ) (side : CMVFigureFour.CircleSide) (p : PlanePoint) : Prop :=
  ∃ V : Set PlanePoint, IsOpen V ∧ p ∈ V ∧
    ∀ q, q ∈ V → CMVFigureFour.circleValue center radius q ≠ 0 →
      (q ∈ K ↔ side.sign * CMVFigureFour.circleValue center radius q < 0)

namespace RawFourArcCoordinates

open CMVSourceClassification

variable (raw : RawFourArcCoordinates)

/-- Horizontally placed supporting-circle centers of the literal raw target. -/
def placedLeftCenter : PlanePoint :=
  horizontalTranslation raw.horizontalPlacement raw.leftCenter

def placedRightCenter : PlanePoint :=
  horizontalTranslation raw.horizontalPlacement raw.rightCenter

def placedUpperCenter : PlanePoint :=
  horizontalTranslation raw.horizontalPlacement raw.upperCenter

def placedLowerCenter : PlanePoint :=
  horizontalTranslation raw.horizontalPlacement raw.lowerCenter

/-- The four horizontally placed density-interface junctions of the raw target. -/
def upperLeftJunction : PlanePoint :=
  (raw.horizontalPlacement - raw.outerHalfWidth, 1)

def upperRightJunction : PlanePoint :=
  (raw.horizontalPlacement + raw.outerHalfWidth, 1)

def lowerLeftJunction : PlanePoint :=
  (raw.horizontalPlacement - raw.outerHalfWidth, -1)

def lowerRightJunction : PlanePoint :=
  (raw.horizontalPlacement + raw.outerHalfWidth, -1)

end RawFourArcCoordinates


namespace SourceAlignment

open CMVFigureFour
open CMVSourceClassification

variable {lam : ℝ} (g : SourceGeometry lam)

private theorem curvature_div_density_bounds :
    (-1 : ℝ) ≤ (1 / g.sourceRadius) / lam ∧
      (1 / g.sourceRadius) / lam ≤ 1 := by
  have hR0 : 0 < 1 / g.sourceRadius := one_div_pos.mpr g.sourceRadius_pos
  have hlam0 : 0 < lam := lt_trans zero_lt_one g.density_jump
  have hcurvatureLe : 1 / g.sourceRadius ≤ 1 :=
    (div_le_iff₀ g.sourceRadius_pos).2 (by
      simpa only [one_mul] using g.sourceRadius_ge_one)
  have hratioPos : 0 < (1 / g.sourceRadius) / lam := div_pos hR0 hlam0
  have hratioLt : (1 / g.sourceRadius) / lam < 1 :=
    (div_lt_one hlam0).2 (lt_of_le_of_lt hcurvatureLe g.density_jump)
  exact ⟨by linarith, hratioLt.le⟩

/-- The actual upper signed component is the cosine used by the derived raw
target. -/
theorem upperExteriorComponent_eq_cos_exteriorHalfAngle :
    g.upperExteriorComponent = cos g.exteriorHalfAngle := by
  rw [g.upperExteriorComponent_eq_curvature_div_density]
  unfold SourceGeometry.exteriorHalfAngle
  rw [Real.cos_arccos (curvature_div_density_bounds g).1
    (curvature_div_density_bounds g).2]

private theorem sqrt_one_sub_upperExteriorComponent_sq :
    √(1 - g.upperExteriorComponent ^ 2) =
      sin g.exteriorHalfAngle := by
  rw [upperExteriorComponent_eq_cos_exteriorHalfAngle g]
  symm
  have h := g.toRawFourArcCoordinates_satisfiesClosedSnell
  exact Real.sin_eq_sqrt_one_sub_cos_sq h.exteriorHalfAngle_pos.le
    (le_trans h.exteriorHalfAngle_lt_pi_div_two.le
      (by linarith [Real.pi_pos]))

/-- The actual upper supporting-circle center is the horizontal placement of
the raw upper center. -/
theorem upperCenter_eq_placedUpperCenter :
    g.upperCenter =
      RawFourArcCoordinates.placedUpperCenter g.toRawFourArcCoordinates := by
  apply Prod.ext
  · simp only [RawFourArcCoordinates.placedUpperCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.upperCenter]
    simpa only [zero_add] using g.upper_center_on_axis
  · simp only [RawFourArcCoordinates.placedUpperCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.upperCenter]
    have hcomponent :
        (1 - g.upperCenter.2) / g.sourceRadius =
          cos g.exteriorHalfAngle := by
      change g.upperExteriorComponent = cos g.exteriorHalfAngle
      exact upperExteriorComponent_eq_cos_exteriorHalfAngle g
    field_simp [ne_of_gt g.sourceRadius_pos] at hcomponent
    nlinarith

/-- The actual lower supporting-circle center is the horizontal placement of
the raw lower center. -/
theorem lowerCenter_eq_placedLowerCenter :
    g.lowerCenter =
      RawFourArcCoordinates.placedLowerCenter g.toRawFourArcCoordinates := by
  apply Prod.ext
  · simp only [RawFourArcCoordinates.placedLowerCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.lowerCenter]
    simpa only [zero_add] using g.lower_center_on_axis
  · simp only [RawFourArcCoordinates.placedLowerCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.lowerCenter]
    have hu := congrArg Prod.snd (upperCenter_eq_placedUpperCenter g)
    simp only [RawFourArcCoordinates.placedUpperCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.upperCenter] at hu
    nlinarith [g.horizontal_center_symmetry.2.2]

/-- The actual upper-left Snell junction is the corresponding horizontally
placed raw target junction. -/
theorem upperLeft_eq_upperLeftJunction :
    g.upperLeft =
      RawFourArcCoordinates.upperLeftJunction g.toRawFourArcCoordinates := by
  apply Prod.ext
  · change g.upperLeft.1 =
      g.symmetryAxisX - g.sourceRadius * sin g.exteriorHalfAngle
    have hleft : g.upperLeft.1 ≤ g.upperCenter.1 := by
      rw [g.upper_center_on_axis]
      exact g.upperLeft_strictly_left_of_axis.le
    have hdistance := centerX_sub_pointX_eq_radius_mul_sqrt
      g.sourceRadius_pos g.upperLeft_mem_upper.1 hleft
    have hcomponent :
        (g.upperLeft.2 - g.upperCenter.2) / g.sourceRadius =
          g.upperExteriorComponent := by
      rw [g.upperLeft_height]
      rfl
    rw [hcomponent, sqrt_one_sub_upperExteriorComponent_sq g] at hdistance
    nlinarith [g.upper_center_on_axis]
  · change g.upperLeft.2 = 1
    exact g.upperLeft_height

private theorem lowerExteriorComponent_eq_upperExteriorComponent :
    g.lowerExteriorComponent = g.upperExteriorComponent := by
  unfold SourceGeometry.lowerExteriorComponent SourceGeometry.upperExteriorComponent
  rw [g.horizontal_center_symmetry.2.2]
  ring

/-- The actual lower-left Snell junction is the corresponding horizontally
placed raw target junction. -/
theorem lowerLeft_eq_lowerLeftJunction :
    g.lowerLeft =
      RawFourArcCoordinates.lowerLeftJunction g.toRawFourArcCoordinates := by
  apply Prod.ext
  · change g.lowerLeft.1 =
      g.symmetryAxisX - g.sourceRadius * sin g.exteriorHalfAngle
    have hleft : g.lowerLeft.1 ≤ g.lowerCenter.1 := by
      rw [g.lower_center_on_axis]
      exact g.lowerLeft_strictly_left_of_axis.le
    have hdistance := centerX_sub_pointX_eq_radius_mul_sqrt
      g.sourceRadius_pos g.lowerLeft_mem_lower.1 hleft
    have hcomponent :
        (g.lowerLeft.2 - g.lowerCenter.2) / g.sourceRadius =
          -g.lowerExteriorComponent := by
      rw [g.lowerLeft_height]
      unfold SourceGeometry.lowerExteriorComponent
      ring
    rw [hcomponent, neg_sq, lowerExteriorComponent_eq_upperExteriorComponent g,
      sqrt_one_sub_upperExteriorComponent_sq g] at hdistance
    nlinarith [g.lower_center_on_axis]
  · change g.lowerLeft.2 = -1
    exact g.lowerLeft_height

/-- Vertical reflection transports the two left-junction alignments to the
right source junctions. -/
theorem upperRight_eq_upperRightJunction :
    g.upperRight =
      RawFourArcCoordinates.upperRightJunction g.toRawFourArcCoordinates := by
  rw [g.upperRight_reflection, upperLeft_eq_upperLeftJunction g]
  apply Prod.ext
  all_goals
    simp [CMVFigureFour.verticalReflection,
      RawFourArcCoordinates.upperLeftJunction,
      RawFourArcCoordinates.upperRightJunction,
      SourceGeometry.toRawFourArcCoordinates] <;>
      ring

theorem lowerRight_eq_lowerRightJunction :
    g.lowerRight =
      RawFourArcCoordinates.lowerRightJunction g.toRawFourArcCoordinates := by
  rw [g.lowerRight_reflection, lowerLeft_eq_lowerLeftJunction g]
  apply Prod.ext
  all_goals
    simp [CMVFigureFour.verticalReflection,
      RawFourArcCoordinates.lowerLeftJunction,
      RawFourArcCoordinates.lowerRightJunction,
      SourceGeometry.toRawFourArcCoordinates] <;>
      ring

/-- The actual left strip-circle center is the horizontal placement of the raw
left center. -/
theorem leftStripCenter_eq_placedLeftCenter :
    g.leftStripCenter =
      RawFourArcCoordinates.placedLeftCenter g.toRawFourArcCoordinates := by
  apply Prod.ext
  · change g.leftStripCenter.1 =
      g.symmetryAxisX -
        g.sourceRadius *
          (sin g.exteriorHalfAngle -
            √(1 - (1 / g.sourceRadius) ^ 2))
    have hdistance := centerX_sub_pointX_eq_radius_mul_sqrt
      g.sourceRadius_pos g.upperLeft_mem_left.1
        g.upperLeft_mem_left.2.2
    have hcomponent :
        (g.upperLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
          g.upperStripComponent := by
      rw [g.upperLeft_height]
      rfl
    rw [hcomponent, g.scalar_reduction.2.1] at hdistance
    have hjunction := congrArg Prod.fst (upperLeft_eq_upperLeftJunction g)
    change g.upperLeft.1 =
      g.symmetryAxisX - g.sourceRadius * sin g.exteriorHalfAngle at hjunction
    nlinarith
  · simp only [RawFourArcCoordinates.placedLeftCenter,
      horizontalTranslation_apply, SourceGeometry.toRawFourArcCoordinates,
      RawFourArcCoordinates.leftCenter]
    exact g.horizontal_center_symmetry.1

/-- Vertical reflection transports left-center alignment to the right strip
supporting circle. -/
theorem rightStripCenter_eq_placedRightCenter :
    g.rightStripCenter =
      RawFourArcCoordinates.placedRightCenter g.toRawFourArcCoordinates := by
  rw [g.right_center_reflection, leftStripCenter_eq_placedLeftCenter g]
  apply Prod.ext
  all_goals
    simp [CMVFigureFour.verticalReflection,
      RawFourArcCoordinates.placedLeftCenter,
      RawFourArcCoordinates.placedRightCenter,
      RawFourArcCoordinates.leftCenter,
      RawFourArcCoordinates.rightCenter,
      SourceGeometry.toRawFourArcCoordinates,
      horizontalTranslation_apply] <;>
      ring

/-- All four actual centers and all four actual Snell junctions align exactly
with the horizontally placed literal raw target. -/
theorem centers_and_junctions_align :
    g.leftStripCenter =
        RawFourArcCoordinates.placedLeftCenter g.toRawFourArcCoordinates ∧
      g.rightStripCenter =
        RawFourArcCoordinates.placedRightCenter g.toRawFourArcCoordinates ∧
      g.upperCenter =
        RawFourArcCoordinates.placedUpperCenter g.toRawFourArcCoordinates ∧
      g.lowerCenter =
        RawFourArcCoordinates.placedLowerCenter g.toRawFourArcCoordinates ∧
      g.upperLeft =
        RawFourArcCoordinates.upperLeftJunction g.toRawFourArcCoordinates ∧
      g.upperRight =
        RawFourArcCoordinates.upperRightJunction g.toRawFourArcCoordinates ∧
      g.lowerLeft =
        RawFourArcCoordinates.lowerLeftJunction g.toRawFourArcCoordinates ∧
      g.lowerRight =
        RawFourArcCoordinates.lowerRightJunction g.toRawFourArcCoordinates := by
  exact ⟨leftStripCenter_eq_placedLeftCenter g,
    rightStripCenter_eq_placedRightCenter g,
    upperCenter_eq_placedUpperCenter g,
    lowerCenter_eq_placedLowerCenter g,
    upperLeft_eq_upperLeftJunction g,
    upperRight_eq_upperRightJunction g,
    lowerLeft_eq_lowerLeftJunction g,
    lowerRight_eq_lowerRightJunction g⟩

end SourceAlignment

namespace EndpointApplication

open CMVFigureFour
open CMVFigureFour.Examples
open CMVSourceClassification

/-- At placement zero the literal endpoint carrier is exactly its independently
defined centered five-piece carrier. -/
theorem endpointRaw_carrier_eq_centeredCarrier :
    endpointRaw.carrier = endpointRaw.centeredCarrier := by
  rw [RawFourArcCoordinates.carrier]
  change horizontalTranslation 0 '' endpointRaw.centeredCarrier =
    endpointRaw.centeredCarrier
  have hzero : (horizontalTranslation 0 : PlanePoint → PlanePoint) = id := by
    funext p
    apply Prod.ext <;> simp [horizontalTranslation_apply]
  rw [hzero, image_id]

/-- A literal regular point on the left strip-side circle of the radius-one
endpoint target. -/
def endpointRegularLeftPoint : PlanePoint :=
  (endpointRaw.leftCenter.1 - endpointRaw.sourceRadius, 0)

/-- The literal upper cap pole of the radius-one endpoint target. -/
def endpointUpperPole : PlanePoint :=
  (endpointRaw.upperCenter.1,
    endpointRaw.upperCenter.2 + endpointRaw.sourceRadius)

private theorem endpoint_sideCenterOffset_eq_outerHalfWidth :
    endpointRaw.sideCenterOffset = endpointRaw.outerHalfWidth := by
  simp [endpointRaw, RawFourArcCoordinates.sideCenterOffset,
    RawFourArcCoordinates.outerHalfWidth,
    RawFourArcCoordinates.innerRadial,
    RawFourArcCoordinates.curvature]

private theorem endpoint_outerHalfWidth_pos :
    0 < endpointRaw.outerHalfWidth := by
  unfold RawFourArcCoordinates.outerHalfWidth
  exact mul_pos (by norm_num [endpointRaw])
    (Real.sin_pos_of_pos_of_lt_pi
      endpointRaw_satisfiesClosedSnell.exteriorHalfAngle_pos
      (lt_trans endpointRaw_satisfiesClosedSnell.exteriorHalfAngle_lt_pi_div_two
        (by linarith [Real.pi_pos])))

/-- The selected strip test point really lies on the literal endpoint's left
supporting circle. -/
theorem endpointRegularLeftPoint_circle :
    circleValue endpointRaw.leftCenter endpointRaw.sourceRadius
      endpointRegularLeftPoint = 0 := by
  unfold circleValue endpointRegularLeftPoint
  simp only [endpointRaw_sourceRadius, one_pow,
    RawFourArcCoordinates.leftCenter]
  ring

/-- Radius one is exercised on a regular strip-side point of the literal closed
raw target.  In a neighborhood strictly beyond the rectangle attachment and
strictly inside the strip, target membership off the supporting circle is
exactly its inside-circle label. -/
theorem endpointRegularLeftPoint_locallyInside :
    LocallyOnCircleSideAway endpointRaw.carrier endpointRaw.leftCenter
      endpointRaw.sourceRadius .inside endpointRegularLeftPoint := by
  let V : Set PlanePoint :=
    {q | q.1 < -endpointRaw.outerHalfWidth ∧ |q.2| < 1}
  refine ⟨V, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  · change (endpointRaw.leftCenter.1 - endpointRaw.sourceRadius <
        -endpointRaw.outerHalfWidth) ∧ |(0 : ℝ)| < 1
    rw [show endpointRaw.leftCenter.1 =
      -endpointRaw.sideCenterOffset by rfl,
      endpoint_sideCenterOffset_eq_outerHalfWidth]
    norm_num [endpointRaw]
  · intro q hq hcircle
    rw [endpointRaw_carrier_eq_centeredCarrier]
    simp only [RawFourArcCoordinates.centeredCarrier,
      RawFourArcCoordinates.rectangleCarrier,
      RawFourArcCoordinates.leftSegmentCarrier,
      RawFourArcCoordinates.rightSegmentCarrier,
      RawFourArcCoordinates.upperCapCarrier,
      RawFourArcCoordinates.lowerCapCarrier,
      mem_union, mem_ofPred_eq, CMVFigureFour.CircleSide.sign, one_mul]
    constructor
    · rintro ((((hrectangle | hleft) | hright) | hupper) | hlower)
      · exact False.elim ((not_le_of_gt hq.1) hrectangle.1)
      · unfold circleValue at hcircle ⊢
        have hle := hleft.1
        have hradius : endpointRaw.sourceRadius = 1 := rfl
        rw [hradius] at hle hcircle ⊢
        have hle0 :
            (q.1 - endpointRaw.leftCenter.1) ^ 2 +
                (q.2 - endpointRaw.leftCenter.2) ^ 2 - 1 ^ 2 ≤ 0 := by
          linarith
        exact lt_of_le_of_ne hle0 hcircle
      · exact False.elim ((not_le_of_gt
          (lt_trans hq.1 (by linarith [endpoint_outerHalfWidth_pos])))
            hright.2.1)
      · exact False.elim ((not_le_of_gt (abs_lt.mp hq.2).2) hupper.2)
      · exact False.elim ((not_le_of_gt (abs_lt.mp hq.2).1) hlower.2)
    · intro hinside
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      have hx : q.1 ≤ -endpointRaw.outerHalfWidth := hq.1.le
      have hy : |q.2| ≤ 1 := hq.2.le
      refine ⟨?_, hx, hy⟩
      unfold circleValue at hinside
      have hradius : endpointRaw.sourceRadius = 1 := rfl
      rw [hradius] at hinside ⊢
      nlinarith

/-- The selected cap-pole test point really lies on the literal endpoint's upper
supporting circle. -/
theorem endpointUpperPole_circle :
    circleValue endpointRaw.upperCenter endpointRaw.sourceRadius
      endpointUpperPole = 0 := by
  unfold circleValue endpointUpperPole
  simp [endpointRaw]

/-- Radius one is also exercised at the literal upper cap pole.  The proof uses
the full two-dimensional circle equation and the strict upper half-plane; it
never invokes horizontal transversality. -/
theorem endpointUpperPole_locallyInside :
    LocallyOnCircleSideAway endpointRaw.carrier endpointRaw.upperCenter
      endpointRaw.sourceRadius .inside endpointUpperPole := by
  let V : Set PlanePoint := {q | 1 < q.2}
  refine ⟨V, isOpen_lt continuous_const continuous_snd, ?_, ?_⟩
  · change 1 < endpointRaw.upperCenter.2 + endpointRaw.sourceRadius
    have hcos : Real.cos endpointRaw.exteriorHalfAngle = 1 / 2 := by
      change Real.cos (Real.arccos (1 / 2)) = 1 / 2
      rw [Real.cos_arccos] <;> norm_num
    unfold RawFourArcCoordinates.upperCenter
    dsimp only
    rw [hcos]
    norm_num [endpointRaw]
  · intro q hq hcircle
    rw [endpointRaw_carrier_eq_centeredCarrier]
    simp only [RawFourArcCoordinates.centeredCarrier,
      RawFourArcCoordinates.rectangleCarrier,
      RawFourArcCoordinates.leftSegmentCarrier,
      RawFourArcCoordinates.rightSegmentCarrier,
      RawFourArcCoordinates.upperCapCarrier,
      RawFourArcCoordinates.lowerCapCarrier,
      mem_union, mem_ofPred_eq, CMVFigureFour.CircleSide.sign, one_mul]
    constructor
    · rintro ((((hrectangle | hleft) | hright) | hupper) | hlower)
      · exact False.elim ((not_le_of_gt hq)
          (le_trans (le_abs_self q.2) hrectangle.2.2))
      · exact False.elim ((not_le_of_gt hq)
          (le_trans (le_abs_self q.2) hleft.2.2))
      · exact False.elim ((not_le_of_gt hq)
          (le_trans (le_abs_self q.2) hright.2.2))
      · unfold circleValue at hcircle ⊢
        have hle := hupper.1
        have hle0 :
            (q.1 - endpointRaw.upperCenter.1) ^ 2 +
                (q.2 - endpointRaw.upperCenter.2) ^ 2 -
                  endpointRaw.sourceRadius ^ 2 ≤ 0 := by
          linarith
        exact lt_of_le_of_ne hle0 hcircle
      · exact False.elim ((not_le_of_gt (lt_trans (by norm_num) hq)) hlower.2)
    · intro hinside
      refine Or.inl (Or.inr ?_)
      refine ⟨?_, hq.le⟩
      unfold circleValue at hinside
      nlinarith

end EndpointApplication

end CMVFigureFourTargetGeometry
