/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourBilateralIncidence

/-!
# Scalar reduction from actual CMV Figure 4 incidence

The declarations here derive the scalar inputs of
`CMVSourceClassification.figure4_scalar_reduction` from the frozen actual
circle endpoints.  No scalar height, radical alignment, horizontal-axis
symmetry, radius bound, or principal angle is added to the source signature.
-/

open Set
open Real

noncomputable section

namespace CMVFigureFour

/-- Circle incidence bounds a signed normalized vertical component by one. -/
theorem normalizedVertical_mem_Icc
    {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius)
    (hcircle : circleValue center radius p = 0) :
    (p.2 - center.2) / radius ∈ Icc (-1 : ℝ) 1 := by
  have hverticalSq : (p.2 - center.2) ^ 2 ≤ radius ^ 2 := by
    unfold circleValue at hcircle
    nlinarith [sq_nonneg (p.1 - center.1)]
  have hnormalizedSq : ((p.2 - center.2) / radius) ^ 2 ≤ 1 := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hradius)).2
    simpa only [one_mul] using hverticalSq
  constructor <;> nlinarith

/-- On the left branch, circle incidence identifies the horizontal radial
length with the principal square root of the remaining normalized square. -/
theorem centerX_sub_pointX_eq_radius_mul_sqrt
    {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius)
    (hcircle : circleValue center radius p = 0)
    (hleft : p.1 ≤ center.1) :
    center.1 - p.1 =
      radius * √(1 - ((p.2 - center.2) / radius) ^ 2) := by
  have hcomponent := normalizedVertical_mem_Icc hradius hcircle
  have hcomponentSq : ((p.2 - center.2) / radius) ^ 2 ≤ 1 := by
    rcases hcomponent with ⟨hlo, hhi⟩
    nlinarith
  have hsqrtSq :
      (√(1 - ((p.2 - center.2) / radius) ^ 2)) ^ 2 =
        1 - ((p.2 - center.2) / radius) ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hrightNonneg :
      0 ≤ radius * √(1 - ((p.2 - center.2) / radius) ^ 2) :=
    mul_nonneg hradius.le (Real.sqrt_nonneg _)
  have hsquares :
      (center.1 - p.1) ^ 2 =
        (radius * √(1 - ((p.2 - center.2) / radius) ^ 2)) ^ 2 := by
    calc
      (center.1 - p.1) ^ 2 = (p.1 - center.1) ^ 2 := by ring
      _ = radius ^ 2 - (p.2 - center.2) ^ 2 := by
        unfold circleValue at hcircle
        linarith
      _ = radius ^ 2 *
          (1 - ((p.2 - center.2) / radius) ^ 2) := by
        rw [div_pow]
        field_simp [ne_of_gt hradius]
      _ = (radius *
          √(1 - ((p.2 - center.2) / radius) ^ 2)) ^ 2 := by
        rw [mul_pow, hsqrtSq]
  nlinarith


namespace SourceGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- All four signed components are bounded from actual common-circle
incidence, including negative pre-reduction strip components. -/
theorem scalar_component_bounds :
    (-1 ≤ g.upperStripComponent ∧ g.upperStripComponent ≤ 1) ∧
    (-1 ≤ g.lowerStripComponent ∧ g.lowerStripComponent ≤ 1) ∧
    (-1 ≤ g.upperExteriorComponent ∧ g.upperExteriorComponent ≤ 1) ∧
    (-1 ≤ g.lowerExteriorComponent ∧ g.lowerExteriorComponent ≤ 1) := by
  have ha := normalizedVertical_mem_Icc g.sourceRadius_pos
    g.upperLeft_mem_left.1
  have hb := normalizedVertical_mem_Icc g.sourceRadius_pos
    g.lowerLeft_mem_left.1
  have hc := normalizedVertical_mem_Icc g.sourceRadius_pos
    g.upperLeft_mem_upper.1
  have hd := normalizedVertical_mem_Icc g.sourceRadius_pos
    g.lowerLeft_mem_lower.1
  have haEq :
      (g.upperLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
        g.upperStripComponent := by
    rw [g.upperLeft_height]
    rfl
  have hbEq :
      (g.lowerLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
        -g.lowerStripComponent := by
    rw [g.lowerLeft_height]
    unfold lowerStripComponent
    ring
  have hcEq :
      (g.upperLeft.2 - g.upperCenter.2) / g.sourceRadius =
        g.upperExteriorComponent := by
    rw [g.upperLeft_height]
    rfl
  have hdEq :
      (g.lowerLeft.2 - g.lowerCenter.2) / g.sourceRadius =
        -g.lowerExteriorComponent := by
    rw [g.lowerLeft_height]
    unfold lowerExteriorComponent
    ring
  rw [haEq] at ha
  rw [hbEq] at hb
  rw [hcEq] at hc
  rw [hdEq] at hd
  rcases ha with ⟨haLo, haHi⟩
  rcases hb with ⟨hbLo, hbHi⟩
  rcases hc with ⟨hcLo, hcHi⟩
  rcases hd with ⟨hdLo, hdHi⟩
  constructor
  · exact ⟨haLo, haHi⟩
  constructor
  · constructor <;> linarith
  constructor
  · exact ⟨hcLo, hcHi⟩
  · constructor <;> linarith

/-- Equation (24)'s strip-height identity is an algebraic consequence of the
two actual interface heights, not a primitive source field. -/
theorem scalar_height :
    g.sourceRadius *
      (g.upperStripComponent + g.lowerStripComponent) = 2 := by
  unfold upperStripComponent lowerStripComponent
  field_simp [ne_of_gt g.sourceRadius_pos]
  ring

/-- Equality of the two actual exterior-center abscissae, together with the
four circle incidences and selected left branches, derives Step 2's radical
alignment equation. -/
theorem scalar_radical_alignment :
    √(1 - g.upperStripComponent ^ 2) -
        √(1 - g.upperExteriorComponent ^ 2) =
      √(1 - g.lowerStripComponent ^ 2) -
        √(1 - g.lowerExteriorComponent ^ 2) := by
  have haEq :
      (g.upperLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
        g.upperStripComponent := by
    rw [g.upperLeft_height]
    rfl
  have hbEq :
      (g.lowerLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
        -g.lowerStripComponent := by
    rw [g.lowerLeft_height]
    unfold lowerStripComponent
    ring
  have hcEq :
      (g.upperLeft.2 - g.upperCenter.2) / g.sourceRadius =
        g.upperExteriorComponent := by
    rw [g.upperLeft_height]
    rfl
  have hdEq :
      (g.lowerLeft.2 - g.lowerCenter.2) / g.sourceRadius =
        -g.lowerExteriorComponent := by
    rw [g.lowerLeft_height]
    unfold lowerExteriorComponent
    ring
  have hOA := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.upperLeft_mem_left.1
      g.upperLeft_mem_left.2.2
  rw [haEq] at hOA
  have hOB := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.lowerLeft_mem_left.1
      g.lowerLeft_mem_left.2.2
  rw [hbEq] at hOB
  simp only [neg_sq] at hOB
  have hAP : g.upperLeft.1 ≤ g.upperCenter.1 := by
    rw [g.upper_center_on_axis]
    exact g.upperLeft_strictly_left_of_axis.le
  have hPA := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.upperLeft_mem_upper.1 hAP
  rw [hcEq] at hPA
  have hBQ : g.lowerLeft.1 ≤ g.lowerCenter.1 := by
    rw [g.lower_center_on_axis]
    exact g.lowerLeft_strictly_left_of_axis.le
  have hQB := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.lowerLeft_mem_lower.1 hBQ
  rw [hdEq] at hQB
  simp only [neg_sq] at hQB
  have hPQ : g.upperCenter.1 = g.lowerCenter.1 := by
    rw [g.upper_center_on_axis, g.lower_center_on_axis]
  have hscaled :
      g.sourceRadius *
          (√(1 - g.upperStripComponent ^ 2) -
            √(1 - g.upperExteriorComponent ^ 2)) =
        g.sourceRadius *
          (√(1 - g.lowerStripComponent ^ 2) -
            √(1 - g.lowerExteriorComponent ^ 2)) := by
    nlinarith
  exact mul_left_cancel₀ (ne_of_gt g.sourceRadius_pos) hscaled

/-- The retained Step-2 scalar theorem now consumes only conclusions derived
from actual source incidence. -/
theorem scalar_reduction :
    g.upperStripComponent = g.lowerStripComponent ∧
      g.upperStripComponent = 1 / g.sourceRadius ∧
      g.lowerStripComponent = 1 / g.sourceRadius := by
  rcases g.scalar_component_bounds with
    ⟨ha, hb, hc, hd⟩
  exact CMVSourceClassification.figure4_scalar_reduction
    g.density_jump g.sourceRadius_pos
    ha.1 ha.2 hb.1 hb.2 hc.1 hc.2 hd.1 hd.2
    g.signed_snell_components.1 g.signed_snell_components.2
    g.scalar_height g.scalar_radical_alignment

/-- Horizontal-axis symmetry of all four supporting-circle centers is derived:
the strip-side centers lie on `y = 0`, while the exterior centers have opposite
vertical coordinates. -/
theorem horizontal_center_symmetry :
    g.leftStripCenter.2 = 0 ∧
      g.rightStripCenter.2 = 0 ∧
      g.lowerCenter.2 = -g.upperCenter.2 := by
  have hab := g.scalar_reduction.1
  have hleft : g.leftStripCenter.2 = 0 := by
    unfold upperStripComponent lowerStripComponent at hab
    field_simp [ne_of_gt g.sourceRadius_pos] at hab
    linarith
  have hright : g.rightStripCenter.2 = 0 := by
    have href := congrArg Prod.snd g.right_center_reflection
    simp only [verticalReflection] at href
    linarith
  have hcd :
      g.upperExteriorComponent = g.lowerExteriorComponent := by
    have hsnellUpper := g.signed_snell_components.1
    have hsnellLower := g.signed_snell_components.2
    have hlam0 : 0 < lam := lt_trans zero_lt_one g.density_jump
    rw [hab] at hsnellUpper
    nlinarith
  have hcaps : g.lowerCenter.2 = -g.upperCenter.2 := by
    unfold upperExteriorComponent lowerExteriorComponent at hcd
    field_simp [ne_of_gt g.sourceRadius_pos] at hcd
    linarith
  exact ⟨hleft, hright, hcaps⟩

/-- The common source radius is at least one; this is a conclusion of the
actual incidence reduction and retains the literal `R = 1` branch. -/
theorem sourceRadius_ge_one : 1 ≤ g.sourceRadius := by
  have haHi := g.scalar_component_bounds.1.2
  rw [g.scalar_reduction.2.1] at haHi
  have hscaled :=
    (div_le_iff₀ g.sourceRadius_pos).1 haHi
  simpa only [one_mul] using hscaled

/-- The actual upper exterior signed component is the closed-Snell ratio. -/
theorem upperExteriorComponent_eq_curvature_div_density :
    g.upperExteriorComponent = (1 / g.sourceRadius) / lam := by
  have hsnell := g.signed_snell_components.1
  rw [g.scalar_reduction.2.1] at hsnell
  have hlam0 : 0 < lam := lt_trans zero_lt_one g.density_jump
  exact (eq_div_iff (ne_of_gt hlam0)).2 (by
    simpa only [mul_comm] using hsnell.symm)

/-- The selected left strip circle really lies to the left of the source
vertical axis.  This order is derived from density jump and actual circle
incidence, not supplied as normalized geometry. -/
theorem leftStripCenter_lt_axis :
    g.leftStripCenter.1 < g.symmetryAxisX := by
  have haPos : 0 < g.upperStripComponent := by
    rw [g.scalar_reduction.2.1]
    exact one_div_pos.mpr g.sourceRadius_pos
  have hcPos : 0 < g.upperExteriorComponent := by
    rw [g.upperExteriorComponent_eq_curvature_div_density]
    exact div_pos (one_div_pos.mpr g.sourceRadius_pos)
      (lt_trans zero_lt_one g.density_jump)
  have hcLtHa : g.upperExteriorComponent < g.upperStripComponent := by
    have hsnell := g.signed_snell_components.1
    nlinarith [g.density_jump]
  have haBounds := g.scalar_component_bounds.1
  have hradA : 0 ≤ 1 - g.upperStripComponent ^ 2 := by
    nlinarith
  have hrootLt :
      √(1 - g.upperStripComponent ^ 2) <
        √(1 - g.upperExteriorComponent ^ 2) := by
    apply Real.sqrt_lt_sqrt hradA
    nlinarith
  have haEq :
      (g.upperLeft.2 - g.leftStripCenter.2) / g.sourceRadius =
        g.upperStripComponent := by
    rw [g.upperLeft_height]
    rfl
  have hcEq :
      (g.upperLeft.2 - g.upperCenter.2) / g.sourceRadius =
        g.upperExteriorComponent := by
    rw [g.upperLeft_height]
    rfl
  have hOA := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.upperLeft_mem_left.1
      g.upperLeft_mem_left.2.2
  rw [haEq] at hOA
  have hAP : g.upperLeft.1 ≤ g.upperCenter.1 := by
    rw [g.upper_center_on_axis]
    exact g.upperLeft_strictly_left_of_axis.le
  have hPA := centerX_sub_pointX_eq_radius_mul_sqrt
    g.sourceRadius_pos g.upperLeft_mem_upper.1 hAP
  rw [hcEq] at hPA
  rw [← g.upper_center_on_axis]
  have hscaledRoot : 0 < g.sourceRadius *
      (√(1 - g.upperExteriorComponent ^ 2) -
        √(1 - g.upperStripComponent ^ 2)) :=
    mul_pos g.sourceRadius_pos (sub_pos.mpr hrootLt)
  nlinarith

/-- Principal exterior half-angle derived from actual source incidence. -/
def exteriorHalfAngle : ℝ :=
  arccos ((1 / g.sourceRadius) / lam)

/-- Raw closed-Snell coordinates derived from the actual, unnormalized source
geometry.  The only placement parameter is the permitted vertical-axis
abscissa. -/
def toRawFourArcCoordinates :
    CMVSourceClassification.RawFourArcCoordinates where
  sourceRadius := g.sourceRadius
  exteriorHalfAngle := g.exteriorHalfAngle
  horizontalPlacement := g.symmetryAxisX

/-- Actual Figure-4 incidence yields the checked closed-Snell interface over
the full source-radius range, including `R = 1`. -/
theorem toRawFourArcCoordinates_satisfiesClosedSnell :
    g.toRawFourArcCoordinates.SatisfiesClosedSnell lam := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one g.density_jump
  have hcurvaturePos : 0 < 1 / g.sourceRadius :=
    one_div_pos.mpr g.sourceRadius_pos
  have hcurvatureLe : 1 / g.sourceRadius ≤ 1 := by
    exact (div_le_iff₀ g.sourceRadius_pos).2 (by
      simpa only [one_mul] using g.sourceRadius_ge_one)
  have hratioPos : 0 < (1 / g.sourceRadius) / lam :=
    div_pos hcurvaturePos hlam0
  have hratioLt : (1 / g.sourceRadius) / lam < 1 := by
    exact (div_lt_one hlam0).2 (lt_of_le_of_lt hcurvatureLe g.density_jump)
  constructor
  · exact g.density_jump
  · exact g.sourceRadius_ge_one
  · exact Real.arccos_pos.mpr hratioLt
  · exact Real.arccos_lt_pi_div_two.mpr hratioPos
  · change lam * cos (arccos ((1 / g.sourceRadius) / lam)) =
      1 / g.sourceRadius
    rw [Real.cos_arccos (by linarith) (by linarith)]
    field_simp [ne_of_gt hlam0]

/-- Derived left endpoint of the two actual strip-circle intersections at
height `y`. -/
def leftStripBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.leftStripCenter.1 - √(g.sourceRadius ^ 2 - y ^ 2), y)

/-- Derived right endpoint of the two actual strip-circle intersections at
height `y`. -/
def rightStripBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.rightStripCenter.1 + √(g.sourceRadius ^ 2 - y ^ 2), y)

theorem leftStripBoundaryPoint_mem_trace {y : ℝ} (hy : |y| < 1) :
    g.leftStripBoundaryPoint y ∈
      stripCircleTrace .left g.leftStripCenter g.sourceRadius := by
  have hySq : y ^ 2 < 1 := by
    rcases abs_lt.mp hy with ⟨hyLo, hyHi⟩
    nlinarith
  have hrad : 0 ≤ g.sourceRadius ^ 2 - y ^ 2 := by
    nlinarith [g.sourceRadius_ge_one]
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - y ^ 2 :=
    Real.sq_sqrt hrad
  change circleValue g.leftStripCenter g.sourceRadius
      (g.leftStripBoundaryPoint y) = 0 ∧
    |(g.leftStripBoundaryPoint y).2| ≤ 1 ∧
    HorizontalCircleBranch.left.Holds g.leftStripCenter
      (g.leftStripBoundaryPoint y)
  constructor
  · unfold circleValue leftStripBoundaryPoint
    rw [g.horizontal_center_symmetry.1]
    dsimp only
    nlinarith
  constructor
  · exact hy.le
  · unfold HorizontalCircleBranch.Holds leftStripBoundaryPoint
    dsimp only
    exact sub_le_self _ (Real.sqrt_nonneg _)

theorem rightStripBoundaryPoint_mem_trace {y : ℝ} (hy : |y| < 1) :
    g.rightStripBoundaryPoint y ∈
      stripCircleTrace .right g.rightStripCenter g.sourceRadius := by
  have hySq : y ^ 2 < 1 := by
    rcases abs_lt.mp hy with ⟨hyLo, hyHi⟩
    nlinarith
  have hrad : 0 ≤ g.sourceRadius ^ 2 - y ^ 2 := by
    nlinarith [g.sourceRadius_ge_one]
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - y ^ 2 :=
    Real.sq_sqrt hrad
  change circleValue g.rightStripCenter g.sourceRadius
      (g.rightStripBoundaryPoint y) = 0 ∧
    |(g.rightStripBoundaryPoint y).2| ≤ 1 ∧
    HorizontalCircleBranch.right.Holds g.rightStripCenter
      (g.rightStripBoundaryPoint y)
  constructor
  · unfold circleValue rightStripBoundaryPoint
    rw [g.horizontal_center_symmetry.2.1]
    dsimp only
    nlinarith
  constructor
  · exact hy.le
  · unfold HorizontalCircleBranch.Holds rightStripBoundaryPoint
    dsimp only
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- The selected left branch of the actual strip circle has only the derived
left abscissa at a strict strip height. -/
theorem leftStripTrace_abscissa_eq
    {x y : ℝ} (hy : |y| < 1)
    (hp : (x, y) ∈
      stripCircleTrace .left g.leftStripCenter g.sourceRadius) :
    x = (g.leftStripBoundaryPoint y).1 := by
  have hySq : y ^ 2 < 1 := by
    rcases abs_lt.mp hy with ⟨hyLo, hyHi⟩
    nlinarith
  have hrad : 0 < g.sourceRadius ^ 2 - y ^ 2 := by
    nlinarith [g.sourceRadius_ge_one]
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  have hcircle := hp.1
  have hbranch := hp.2.2
  change
    (x - g.leftStripCenter.1) ^ 2 +
        (y - g.leftStripCenter.2) ^ 2 - g.sourceRadius ^ 2 = 0
      at hcircle
  change x ≤ g.leftStripCenter.1 at hbranch
  rw [g.horizontal_center_symmetry.1] at hcircle
  simp only [sub_zero] at hcircle
  unfold leftStripBoundaryPoint
  dsimp only
  nlinarith [Real.sqrt_nonneg (g.sourceRadius ^ 2 - y ^ 2)]

/-- The selected right branch of the actual strip circle has only the derived
right abscissa at a strict strip height. -/
theorem rightStripTrace_abscissa_eq
    {x y : ℝ} (hy : |y| < 1)
    (hp : (x, y) ∈
      stripCircleTrace .right g.rightStripCenter g.sourceRadius) :
    x = (g.rightStripBoundaryPoint y).1 := by
  have hySq : y ^ 2 < 1 := by
    rcases abs_lt.mp hy with ⟨hyLo, hyHi⟩
    nlinarith
  have hrad : 0 < g.sourceRadius ^ 2 - y ^ 2 := by
    nlinarith [g.sourceRadius_ge_one]
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  have hcircle := hp.1
  have hbranch := hp.2.2
  change
    (x - g.rightStripCenter.1) ^ 2 +
        (y - g.rightStripCenter.2) ^ 2 - g.sourceRadius ^ 2 = 0
      at hcircle
  change g.rightStripCenter.1 ≤ x at hbranch
  rw [g.horizontal_center_symmetry.2.1] at hcircle
  simp only [sub_zero] at hcircle
  unfold rightStripBoundaryPoint
  dsimp only
  nlinarith [Real.sqrt_nonneg (g.sourceRadius ^ 2 - y ^ 2)]

/-- The two derived strip-circle points are strictly ordered around the source
vertical axis. -/
theorem stripBoundaryPoint_order (y : ℝ) :
    (g.leftStripBoundaryPoint y).1 <
      (g.rightStripBoundaryPoint y).1 := by
  have hrightCenter :
      g.rightStripCenter.1 =
        2 * g.symmetryAxisX - g.leftStripCenter.1 := by
    have href := congrArg Prod.fst g.right_center_reflection
    simpa [verticalReflection] using href
  have hroot := Real.sqrt_nonneg (g.sourceRadius ^ 2 - y ^ 2)
  unfold leftStripBoundaryPoint rightStripBoundaryPoint
  dsimp only
  nlinarith [g.leftStripCenter_lt_axis]

/-- On every nonexceptional strict strip height, the derived intersections of
the two actual source circles are actual boundary points of the representative
section. -/
theorem stripBoundaryPoints_mem_actualSection_frontier
    {y : ℝ} (hy : |y| < 1) (hyExceptional : y ∉ g.exceptionalHeights) :
    (g.leftStripBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) ∧
      (g.rightStripBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) := by
  constructor
  · apply g.leftTrace_abscissa_mem_frontier_horizontalSection
      (g.leftStripBoundaryPoint_mem_trace hy)
    simpa [leftStripBoundaryPoint] using hyExceptional
  · apply g.rightTrace_abscissa_mem_frontier_horizontalSection
      (g.rightStripBoundaryPoint_mem_trace hy)
    simpa [rightStripBoundaryPoint] using hyExceptional

/-- On every nonexceptional strict strip height, the complete frontier of the
actual representative section consists exactly of the two transverse
strip-circle intersections. -/
theorem frontier_actual_stripSection_eq_pair
    {y : ℝ} (hy : |y| < 1) (hyExceptional : y ∉ g.exceptionalHeights) :
    frontier
        (CMVSourceClassification.horizontalSection g.representative y) =
      {(g.leftStripBoundaryPoint y).1, (g.rightStripBoundaryPoint y).1} := by
  have hknown :=
    g.stripBoundaryPoints_mem_actualSection_frontier hy hyExceptional
  apply Set.Subset.antisymm
  · intro x hx
    have hplane :=
      CMVSourceClassification.frontier_horizontalSection_subset
        g.representative y hx
    rw [g.frontier_eq_four_circles] at hplane
    rcases hplane with hrest | hright
    · rcases hrest with hrest | hleft
      · rcases hrest with hupper | hlower
        · change circleValue g.upperCenter g.sourceRadius (x, y) = 0 ∧
              1 ≤ y at hupper
          exact False.elim ((not_le_of_gt (abs_lt.mp hy).2) hupper.2)
        · change circleValue g.lowerCenter g.sourceRadius (x, y) = 0 ∧
              y ≤ -1 at hlower
          exact False.elim ((not_le_of_gt (abs_lt.mp hy).1) hlower.2)
      · exact Or.inl (g.leftStripTrace_abscissa_eq hy hleft)
    · exact Or.inr (g.rightStripTrace_abscissa_eq hy hright)
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact hknown.1
    · subst x
      exact hknown.2

/-- Bounded openness, the complete four-circle frontier, and transverse local
one-sidedness determine the actual strict-strip section.  No interval,
connected-section, or target-frontier premise is supplied. -/
theorem actual_stripSection
    {y : ℝ} (hy : |y| < 1) (hyExceptional : y ∉ g.exceptionalHeights) :
    CMVSourceClassification.horizontalSection g.representative y =
      Ioo ((g.leftStripBoundaryPoint y).1)
        ((g.rightStripBoundaryPoint y).1) := by
  exact CMVSourceClassification.IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    (CMVSourceClassification.isOpen_horizontalSection
      g.sourceRepresentative.representative_open y)
    (CMVSourceClassification.isBounded_horizontalSection
      g.sourceRepresentative.representative_bounded y)
    (g.stripBoundaryPoint_order y)
    (g.frontier_actual_stripSection_eq_pair hy hyExceptional)

/-- After the scalar reduction the two exterior circle centers lie strictly on
the strip side of their respective interfaces. -/
theorem exterior_center_interface_bounds :
    g.upperCenter.2 < 1 ∧ -1 < g.lowerCenter.2 := by
  have hcPos : 0 < g.upperExteriorComponent := by
    rw [g.upperExteriorComponent_eq_curvature_div_density]
    exact div_pos (one_div_pos.mpr g.sourceRadius_pos)
      (lt_trans zero_lt_one g.density_jump)
  have hcScale :
      g.upperExteriorComponent * g.sourceRadius =
        1 - g.upperCenter.2 := by
    unfold upperExteriorComponent
    field_simp [ne_of_gt g.sourceRadius_pos]
  have hupper : g.upperCenter.2 < 1 := by
    nlinarith [mul_pos hcPos g.sourceRadius_pos]
  have hlower := g.horizontal_center_symmetry.2.2
  exact ⟨hupper, by linarith⟩

/-- Derived left intersection of the actual upper exterior circle at height
`y`. -/
def upperLeftBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.upperCenter.1 -
    √(g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2), y)

/-- Derived right intersection of the actual upper exterior circle at height
`y`. -/
def upperRightBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.upperCenter.1 +
    √(g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2), y)

theorem upperBoundaryPoints_mem_trace
    {y : ℝ} (hbase : 1 < y)
    (hpole : y < g.upperCenter.2 + g.sourceRadius) :
    g.upperLeftBoundaryPoint y ∈
        exteriorCircleTrace .upper g.upperCenter g.sourceRadius ∧
      g.upperRightBoundaryPoint y ∈
        exteriorCircleTrace .upper g.upperCenter g.sourceRadius := by
  have hdiffPos : 0 < y - g.upperCenter.2 := by
    linarith [g.exterior_center_interface_bounds.1]
  have hdiffLt : y - g.upperCenter.2 < g.sourceRadius := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  constructor
  · change circleValue g.upperCenter g.sourceRadius
        (g.upperLeftBoundaryPoint y) = 0 ∧
      1 ≤ (g.upperLeftBoundaryPoint y).2
    constructor
    · unfold circleValue upperLeftBoundaryPoint
      dsimp only
      nlinarith
    · exact hbase.le
  · change circleValue g.upperCenter g.sourceRadius
        (g.upperRightBoundaryPoint y) = 0 ∧
      1 ≤ (g.upperRightBoundaryPoint y).2
    constructor
    · unfold circleValue upperRightBoundaryPoint
      dsimp only
      nlinarith
    · exact hbase.le

theorem upperBoundaryPoint_order
    {y : ℝ}
    (hrad : 0 <
      g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2) :
    (g.upperLeftBoundaryPoint y).1 <
      (g.upperRightBoundaryPoint y).1 := by
  have hroot :
      0 < √(g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2) :=
    Real.sqrt_pos.2 hrad
  unfold upperLeftBoundaryPoint upperRightBoundaryPoint
  dsimp only
  linarith

/-- The actual upper-cap circle determines both endpoints of every generic
nonexceptional transverse exterior section. -/
theorem actual_upperSection_endpoints
    {y left right : ℝ}
    (hbase : 1 < y)
    (hpole : y < g.upperCenter.2 + g.sourceRadius)
    (hyExceptional : y ∉ g.exceptionalHeights)
    (hleft_le_right : left ≤ right)
    (hsection :
      CMVSourceClassification.horizontalSection g.representative y =
        Ioo left right) :
    left = (g.upperLeftBoundaryPoint y).1 ∧
      right = (g.upperRightBoundaryPoint y).1 := by
  have htrace := g.upperBoundaryPoints_mem_trace hbase hpole
  have hleftFrontier :=
    g.upperTrace_abscissa_mem_frontier_horizontalSection htrace.1
      (by simpa [upperLeftBoundaryPoint] using hyExceptional)
  have hrightFrontier :=
    g.upperTrace_abscissa_mem_frontier_horizontalSection htrace.2
      (by simpa [upperRightBoundaryPoint] using hyExceptional)
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - g.upperCenter.2) ^ 2 := by
    have hdiffPos : 0 < y - g.upperCenter.2 := by
      linarith [g.exterior_center_interface_bounds.1]
    have hdiffLt : y - g.upperCenter.2 < g.sourceRadius := by linarith
    nlinarith
  exact openInterval_endpoints_of_ordered_frontier
    hleft_le_right hsection hleftFrontier hrightFrontier
      (g.upperBoundaryPoint_order hrad)

/-- Derived left intersection of the actual lower exterior circle at height
`y`. -/
def lowerLeftBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.lowerCenter.1 -
    √(g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2), y)

/-- Derived right intersection of the actual lower exterior circle at height
`y`. -/
def lowerRightBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.lowerCenter.1 +
    √(g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2), y)

theorem lowerBoundaryPoints_mem_trace
    {y : ℝ} (hbase : y < -1)
    (hpole : g.lowerCenter.2 - g.sourceRadius < y) :
    g.lowerLeftBoundaryPoint y ∈
        exteriorCircleTrace .lower g.lowerCenter g.sourceRadius ∧
      g.lowerRightBoundaryPoint y ∈
        exteriorCircleTrace .lower g.lowerCenter g.sourceRadius := by
  have hdiffNeg : -g.sourceRadius < y - g.lowerCenter.2 := by linarith
  have hdiffLt : y - g.lowerCenter.2 < 0 := by
    linarith [g.exterior_center_interface_bounds.2]
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2)) ^ 2 =
        g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  constructor
  · change circleValue g.lowerCenter g.sourceRadius
        (g.lowerLeftBoundaryPoint y) = 0 ∧
      (g.lowerLeftBoundaryPoint y).2 ≤ -1
    constructor
    · unfold circleValue lowerLeftBoundaryPoint
      dsimp only
      nlinarith
    · exact hbase.le
  · change circleValue g.lowerCenter g.sourceRadius
        (g.lowerRightBoundaryPoint y) = 0 ∧
      (g.lowerRightBoundaryPoint y).2 ≤ -1
    constructor
    · unfold circleValue lowerRightBoundaryPoint
      dsimp only
      nlinarith
    · exact hbase.le

theorem lowerBoundaryPoint_order
    {y : ℝ}
    (hrad : 0 <
      g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2) :
    (g.lowerLeftBoundaryPoint y).1 <
      (g.lowerRightBoundaryPoint y).1 := by
  have hroot :
      0 < √(g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2) :=
    Real.sqrt_pos.2 hrad
  unfold lowerLeftBoundaryPoint lowerRightBoundaryPoint
  dsimp only
  linarith

/-- The actual lower-cap circle determines both endpoints of every generic
nonexceptional transverse exterior section. -/
theorem actual_lowerSection_endpoints
    {y left right : ℝ}
    (hbase : y < -1)
    (hpole : g.lowerCenter.2 - g.sourceRadius < y)
    (hyExceptional : y ∉ g.exceptionalHeights)
    (hleft_le_right : left ≤ right)
    (hsection :
      CMVSourceClassification.horizontalSection g.representative y =
        Ioo left right) :
    left = (g.lowerLeftBoundaryPoint y).1 ∧
      right = (g.lowerRightBoundaryPoint y).1 := by
  have htrace := g.lowerBoundaryPoints_mem_trace hbase hpole
  have hleftFrontier :=
    g.lowerTrace_abscissa_mem_frontier_horizontalSection htrace.1
      (by simpa [lowerLeftBoundaryPoint] using hyExceptional)
  have hrightFrontier :=
    g.lowerTrace_abscissa_mem_frontier_horizontalSection htrace.2
      (by simpa [lowerRightBoundaryPoint] using hyExceptional)
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - g.lowerCenter.2) ^ 2 := by
    have hdiffNeg : -g.sourceRadius < y - g.lowerCenter.2 := by linarith
    have hdiffLt : y - g.lowerCenter.2 < 0 := by
      linarith [g.exterior_center_interface_bounds.2]
    nlinarith
  exact openInterval_endpoints_of_ordered_frontier
    hleft_le_right hsection hleftFrontier hrightFrontier
      (g.lowerBoundaryPoint_order hrad)

end SourceGeometry

namespace BilateralSourceIncidence

variable {lam : ℝ} (g : BilateralSourceIncidence lam)

/-- The symmetry-free incidence producer feeds the existing Step-2 scalar
reduction without a caller-supplied axis or reflection. -/
theorem derived_scalar_reduction :
    g.toSourceGeometry.upperStripComponent =
        g.toSourceGeometry.lowerStripComponent ∧
      g.toSourceGeometry.upperStripComponent = 1 / g.sourceRadius ∧
      g.toSourceGeometry.lowerStripComponent = 1 / g.sourceRadius :=
  g.toSourceGeometry.scalar_reduction

/-- The existing radius conclusion applies to the unchanged source radius. -/
theorem derived_sourceRadius_ge_one : 1 ≤ g.sourceRadius :=
  g.toSourceGeometry.sourceRadius_ge_one

/-- The raw closed-Snell output produced from bilateral source incidence. -/
def toRawFourArcCoordinates :
    CMVSourceClassification.RawFourArcCoordinates :=
  g.toSourceGeometry.toRawFourArcCoordinates

/-- Bilateral source incidence reaches the unchanged closed-Snell consumer,
including the radius-one branch. -/
theorem toRawFourArcCoordinates_satisfiesClosedSnell :
    g.toRawFourArcCoordinates.SatisfiesClosedSnell lam :=
  g.toSourceGeometry.toRawFourArcCoordinates_satisfiesClosedSnell

/-- The strict-strip section theorem consumes the same actual representative
carried by the symmetry-free incidence input. -/
theorem actual_stripSection
    {y : ℝ} (hy : |y| < 1)
    (hyExceptional :
      y ∉ g.toSourceGeometry.exceptionalHeights) :
    CMVSourceClassification.horizontalSection g.representative y =
      Ioo ((g.toSourceGeometry.leftStripBoundaryPoint y).1)
        ((g.toSourceGeometry.rightStripBoundaryPoint y).1) :=
  g.toSourceGeometry.actual_stripSection hy hyExceptional

end BilateralSourceIncidence

namespace Examples

/-- Explicit strict-radius closed-Snell data.  This witnesses that the derived
scalar interface is nonempty away from the endpoint branch. -/
def strictRaw : CMVSourceClassification.RawFourArcCoordinates where
  sourceRadius := 2
  exteriorHalfAngle := arccos (1 / 4)
  horizontalPlacement := 0

theorem strictRaw_satisfiesClosedSnell :
    strictRaw.SatisfiesClosedSnell 2 := by
  constructor
  · norm_num
  · norm_num [strictRaw]
  · exact Real.arccos_pos.mpr (by norm_num)
  · exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
  · change 2 * cos (arccos (1 / 4)) = 1 / 2
    rw [Real.cos_arccos] <;> norm_num

theorem strictRaw_satisfiesRegularSnell :
    strictRaw.SatisfiesRegularSnell 2 where
  density_jump := by norm_num
  radius_gt_one := by norm_num [strictRaw]
  exteriorHalfAngle_pos := strictRaw_satisfiesClosedSnell.exteriorHalfAngle_pos
  exteriorHalfAngle_lt_pi_div_two :=
    strictRaw_satisfiesClosedSnell.exteriorHalfAngle_lt_pi_div_two
  snell_incidence := strictRaw_satisfiesClosedSnell.snell_incidence

@[simp] theorem strictRaw_sourceRadius :
    strictRaw.sourceRadius = 2 := rfl

/-- Explicit `R = 1` closed-Snell data.  It is a literal endpoint instance,
not a limiting argument. -/
def endpointRaw : CMVSourceClassification.RawFourArcCoordinates where
  sourceRadius := 1
  exteriorHalfAngle := arccos (1 / 2)
  horizontalPlacement := 0

theorem endpointRaw_satisfiesClosedSnell :
    endpointRaw.SatisfiesClosedSnell 2 := by
  constructor
  · norm_num
  · norm_num [endpointRaw]
  · exact Real.arccos_pos.mpr (by norm_num)
  · exact Real.arccos_lt_pi_div_two.mpr (by norm_num)
  · unfold endpointRaw CMVSourceClassification.RawFourArcCoordinates.curvature
    dsimp only
    rw [Real.cos_arccos] <;> norm_num

@[simp] theorem endpointRaw_sourceRadius :
    endpointRaw.sourceRadius = 1 := rfl

end Examples

end CMVFigureFour
