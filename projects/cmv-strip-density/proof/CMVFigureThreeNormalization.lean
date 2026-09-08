/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureThreeIncidence

/-!
# Source-derived normalization for CMV Figure 3

This file derives the type-(iii) curvature, principal exterior angle, and both
strip-side tangencies from the independent `SourceIncidence` geometry.  No
assembly, width identity, carrier equality, or chord containment is assumed by
the source-facing structure.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

namespace VerticalOrientation

/-- Reflect the lower-primary orientation across the horizontal axis while
leaving the upper-primary orientation fixed. -/
def normalizePoint (o : VerticalOrientation) (p : PlanePoint) : PlanePoint :=
  (p.1, o.sign * p.2)

@[simp] theorem normalizePoint_fst (o : VerticalOrientation) (p : PlanePoint) :
    (o.normalizePoint p).1 = p.1 := rfl

@[simp] theorem normalizePoint_tangentInterfaceY (o : VerticalOrientation) :
    o.sign * o.tangentInterfaceY = -1 := by
  cases o <;> norm_num [sign, tangentInterfaceY]

end VerticalOrientation

namespace SourceIncidence

variable {lam : ℝ} (s : SourceIncidence lam)

/-- On the strict-radius Figure-3 branch, the source curvature gives an actual
branch-complete type-(iii) assembly. -/
def strictAssembly (hR : 1 < s.sourceRadius) : _root_.TypeThreeAssembly lam where
  h := 1 / s.sourceRadius
  density_jump := s.density_jump
  h_pos := one_div_pos.mpr (lt_trans zero_lt_one hR)
  h_lt_one := (div_lt_one (lt_trans zero_lt_one hR)).2 hR

@[simp] theorem strictAssembly_h (hR : 1 < s.sourceRadius) :
    (s.strictAssembly hR).h = 1 / s.sourceRadius := rfl

/-- The constructed assembly has exactly the source circle radius. -/
theorem strictAssembly_radius (hR : 1 < s.sourceRadius) :
    (s.strictAssembly hR).radius = s.sourceRadius := by
  rw [_root_.TypeThreeAssembly.radius, strictAssembly_h]
  field_simp [ne_of_gt (lt_trans zero_lt_one hR)]

/-- The oriented vertical radial component at the primary interface is
`2 - R`, in both vertical orientations. -/
theorem primary_signed_vertical_offset :
    s.orientation.sign *
        (s.primaryLeft.2 - s.leftStripCenter.2) = 2 - s.sourceRadius := by
  rw [s.primary_left_interface, s.left_center_tangency_coordinate]
  cases s.orientation <;>
    simp [VerticalOrientation.sign, VerticalOrientation.primaryInterfaceY,
      VerticalOrientation.tangentInterfaceY] <;> ring

/-- The right primary endpoint has the same oriented vertical radial
component. -/
theorem primary_right_signed_vertical_offset :
    s.orientation.sign *
        (s.primaryRight.2 - s.rightStripCenter.2) = 2 - s.sourceRadius := by
  rw [s.primary_right_interface, s.right_center_tangency_coordinate]
  cases s.orientation <;>
    simp [VerticalOrientation.sign, VerticalOrientation.primaryInterfaceY,
      VerticalOrientation.tangentInterfaceY] <;> ring

/-- Signed Snell incidence and the literal source coordinates select exactly
the assembly's principal exterior angle, without a minor-cap restriction. -/
theorem primary_theta_eq_strictAssembly_outerAngle
    (hR : 1 < s.sourceRadius) :
    s.primaryExterior.theta = (s.strictAssembly hR).outerAngle := by
  let a := s.strictAssembly hR
  have hRpos : 0 < s.sourceRadius := lt_trans zero_lt_one hR
  have hsource :
      lam * cos s.primaryExterior.theta = 2 / s.sourceRadius - 1 := by
    rw [s.primary_signed_snell, s.primary_signed_vertical_offset]
    field_simp [ne_of_gt hRpos]
  have hassembly :
      lam * cos a.outerAngle = 2 / s.sourceRadius - 1 := by
    rw [a.snell_incidence, a.cos_innerAngle]
    simp only [_root_.TypeThreeAssembly.shapeParameter, a, strictAssembly_h]
    ring
  have hlamPos : 0 < lam := lt_trans zero_lt_one s.density_jump
  have hcos : cos s.primaryExterior.theta = cos a.outerAngle := by
    nlinarith
  calc
    s.primaryExterior.theta = arccos (cos s.primaryExterior.theta) := by
      symm
      exact Real.arccos_cos s.primaryExterior.theta_pos.le
        s.primaryExterior.theta_lt_pi.le
    _ = arccos (cos a.outerAngle) := by rw [hcos]
    _ = a.outerAngle := Real.arccos_cos a.outerAngle_pos.le
      a.outerAngle_lt_pi.le

private theorem strictAssembly_radius_mul_cos_innerAngle
    (hR : 1 < s.sourceRadius) :
    s.sourceRadius * cos (s.strictAssembly hR).innerAngle =
      2 - s.sourceRadius := by
  have hRpos : 0 < s.sourceRadius := lt_trans zero_lt_one hR
  rw [(s.strictAssembly hR).cos_innerAngle,
    _root_.TypeThreeAssembly.shapeParameter, strictAssembly_h]
  field_simp [ne_of_gt hRpos]

private theorem primary_left_horizontal_square
    (hR : 1 < s.sourceRadius) :
    (s.primaryLeft.1 - s.leftStripCenter.1) ^ 2 =
      (s.sourceRadius * sin (s.strictAssembly hR).innerAngle) ^ 2 := by
  let a := s.strictAssembly hR
  have hoff := s.primary_signed_vertical_offset
  have hoffSq := congrArg (fun z : ℝ => z ^ 2) hoff
  have hsignSq : s.orientation.sign ^ 2 = 1 := by
    cases s.orientation <;> norm_num [VerticalOrientation.sign]
  have hy :
      (s.primaryLeft.2 - s.leftStripCenter.2) ^ 2 =
        (2 - s.sourceRadius) ^ 2 := by
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq a.innerAngle
  have hcos := s.strictAssembly_radius_mul_cos_innerAngle hR
  have hcosSq := congrArg (fun z : ℝ => z ^ 2) hcos
  have hscaledTrig := congrArg (fun z : ℝ => s.sourceRadius ^ 2 * z) htrig
  have hcircle := s.primary_left_on_circle
  dsimp only [a] at htrig hscaledTrig
  nlinarith

private theorem primary_right_horizontal_square
    (hR : 1 < s.sourceRadius) :
    (s.primaryRight.1 - s.rightStripCenter.1) ^ 2 =
      (s.sourceRadius * sin (s.strictAssembly hR).innerAngle) ^ 2 := by
  let a := s.strictAssembly hR
  have hoff := s.primary_right_signed_vertical_offset
  have hoffSq := congrArg (fun z : ℝ => z ^ 2) hoff
  have hsignSq : s.orientation.sign ^ 2 = 1 := by
    cases s.orientation <;> norm_num [VerticalOrientation.sign]
  have hy :
      (s.primaryRight.2 - s.rightStripCenter.2) ^ 2 =
        (2 - s.sourceRadius) ^ 2 := by
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq a.innerAngle
  have hcos := s.strictAssembly_radius_mul_cos_innerAngle hR
  have hcosSq := congrArg (fun z : ℝ => z ^ 2) hcos
  have hscaledTrig := congrArg (fun z : ℝ => s.sourceRadius ^ 2 * z) htrig
  have hcircle := s.primary_right_on_circle
  dsimp only [a] at htrig hscaledTrig
  nlinarith

private theorem primary_left_abscissa
    (hR : 1 < s.sourceRadius) :
    s.primaryLeft.1 = s.symmetryAxisX -
      s.sourceRadius * sin (s.strictAssembly hR).outerAngle := by
  have hmul := s.primaryExterior.radius_mul_sin
  rw [s.primary_radius,
    s.primary_theta_eq_strictAssembly_outerAngle hR] at hmul
  rw [s.primary_left_endpoint, OneSidedCircularCap.leftEndpoint,
    s.primary_midpoint]
  nlinarith

private theorem primary_right_abscissa
    (hR : 1 < s.sourceRadius) :
    s.primaryRight.1 = s.symmetryAxisX +
      s.sourceRadius * sin (s.strictAssembly hR).outerAngle := by
  have hmul := s.primaryExterior.radius_mul_sin
  rw [s.primary_radius,
    s.primary_theta_eq_strictAssembly_outerAngle hR] at hmul
  rw [s.primary_right_endpoint, OneSidedCircularCap.rightEndpoint,
    s.primary_midpoint]
  nlinarith

/-- The left source circle center is the translated assembly center.  The
outward-side inequality selects the signed square root. -/
theorem leftStripCenter_fst_eq
    (hR : 1 < s.sourceRadius) :
    s.leftStripCenter.1 =
      s.symmetryAxisX - (s.strictAssembly hR).sideHalfWidth := by
  let a := s.strictAssembly hR
  have hsq := s.primary_left_horizontal_square hR
  have hsinPos : 0 < s.sourceRadius * sin a.innerAngle :=
    mul_pos (lt_trans zero_lt_one hR) a.innerSin_pos
  have hdelta :
      s.leftStripCenter.1 - s.primaryLeft.1 =
        s.sourceRadius * sin a.innerAngle := by
    nlinarith [s.primary_left_outward]
  have hprimary := s.primary_left_abscissa hR
  rw [_root_.TypeThreeAssembly.sideHalfWidth,
    s.strictAssembly_radius hR]
  dsimp only [a] at hdelta
  nlinarith

/-- The right source circle center is the translated assembly center. -/
theorem rightStripCenter_fst_eq
    (hR : 1 < s.sourceRadius) :
    s.rightStripCenter.1 =
      s.symmetryAxisX + (s.strictAssembly hR).sideHalfWidth := by
  let a := s.strictAssembly hR
  have hsq := s.primary_right_horizontal_square hR
  have hsinPos : 0 < s.sourceRadius * sin a.innerAngle :=
    mul_pos (lt_trans zero_lt_one hR) a.innerSin_pos
  have hdelta :
      s.primaryRight.1 - s.rightStripCenter.1 =
        s.sourceRadius * sin a.innerAngle := by
    nlinarith [s.primary_right_outward]
  have hprimary := s.primary_right_abscissa hR
  rw [_root_.TypeThreeAssembly.sideHalfWidth,
    s.strictAssembly_radius hR]
  dsimp only [a] at hdelta
  nlinarith

/-- The actual left tangency abscissa is the translated assembly endpoint. -/
theorem tangentLeft_fst_eq
    (hR : 1 < s.sourceRadius) :
    s.tangentLeft.1 =
      s.symmetryAxisX - (s.strictAssembly hR).sideHalfWidth := by
  rw [s.tangent_left_coordinate]
  exact s.leftStripCenter_fst_eq hR

/-- The actual right tangency abscissa is the translated assembly endpoint. -/
theorem tangentRight_fst_eq
    (hR : 1 < s.sourceRadius) :
    s.tangentRight.1 =
      s.symmetryAxisX + (s.strictAssembly hR).sideHalfWidth := by
  rw [s.tangent_right_coordinate]
  exact s.rightStripCenter_fst_eq hR

/-- Both coordinates of the orientation-normalized left tangency agree with
the translated assembly endpoint. -/
theorem normalizePoint_tangentLeft_eq
    (hR : 1 < s.sourceRadius) :
    s.orientation.normalizePoint s.tangentLeft =
      (s.symmetryAxisX - (s.strictAssembly hR).sideHalfWidth, -1) := by
  apply Prod.ext
  · exact s.tangentLeft_fst_eq hR
  · change s.orientation.sign * s.tangentLeft.2 = -1
    have hy := congrArg Prod.snd s.tangent_left_coordinate
    simp only at hy
    rw [hy]
    exact s.orientation.normalizePoint_tangentInterfaceY

/-- Both coordinates of the orientation-normalized right tangency agree with
the translated assembly endpoint. -/
theorem normalizePoint_tangentRight_eq
    (hR : 1 < s.sourceRadius) :
    s.orientation.normalizePoint s.tangentRight =
      (s.symmetryAxisX + (s.strictAssembly hR).sideHalfWidth, -1) := by
  apply Prod.ext
  · exact s.tangentRight_fst_eq hR
  · change s.orientation.sign * s.tangentRight.2 = -1
    have hy := congrArg Prod.snd s.tangent_right_coordinate
    simp only at hy
    rw [hy]
    exact s.orientation.normalizePoint_tangentInterfaceY

/-- The literal closed interval between the two actual source tangencies. -/
def tangentInterval : Set PlanePoint :=
  {p | p.2 = s.orientation.tangentInterfaceY ∧
    s.tangentLeft.1 ≤ p.1 ∧ p.1 ≤ s.tangentRight.1}

/-- After the orientation reflection, the actual source tangent interval is
exactly the literal `y = -1` section of the horizontally translated assembly
carrier. -/
theorem normalizePoint_image_tangentInterval_eq_horizontalSection
    (hR : 1 < s.sourceRadius) :
    s.orientation.normalizePoint '' s.tangentInterval =
      horizontalSection
        (horizontalTranslation s.symmetryAxisX ''
          (s.strictAssembly hR).carrier) (-1) := by
  rw [TypeThreeAssembly.horizontalSection_horizontalTranslation]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.2 = s.orientation.tangentInterfaceY ∧
      s.tangentLeft.1 ≤ q.1 ∧ q.1 ≤ s.tangentRight.1 at hq
    refine ⟨(q.1 - s.symmetryAxisX, -1), ?_, ?_⟩
    · change (-1 : ℝ) = -1 ∧
        |q.1 - s.symmetryAxisX| ≤ (s.strictAssembly hR).sideHalfWidth
      refine ⟨rfl, abs_le.mpr ?_⟩
      rw [s.tangentLeft_fst_eq hR, s.tangentRight_fst_eq hR] at hq
      constructor <;> linarith
    · apply Prod.ext
      · simp [horizontalTranslation_apply,
          VerticalOrientation.normalizePoint]
      · simp only [horizontalTranslation_apply,
          VerticalOrientation.normalizePoint]
        rw [hq.1, s.orientation.normalizePoint_tangentInterfaceY]
  · rintro ⟨q, hq, rfl⟩
    change q.2 = (-1 : ℝ) ∧
      |q.1| ≤ (s.strictAssembly hR).sideHalfWidth at hq
    let r : PlanePoint :=
      (q.1 + s.symmetryAxisX, s.orientation.tangentInterfaceY)
    refine ⟨r, ?_, ?_⟩
    · change r.2 = s.orientation.tangentInterfaceY ∧
        s.tangentLeft.1 ≤ r.1 ∧ r.1 ≤ s.tangentRight.1
      refine ⟨rfl, ?_⟩
      rw [s.tangentLeft_fst_eq hR, s.tangentRight_fst_eq hR]
      have hbounds := abs_le.mp hq.2
      dsimp only [r]
      constructor <;> linarith
    · apply Prod.ext
      · simp [r, horizontalTranslation_apply,
          VerticalOrientation.normalizePoint]
      · simp only [r, horizontalTranslation_apply,
          VerticalOrientation.normalizePoint]
        rw [s.orientation.normalizePoint_tangentInterfaceY, hq.1]

end SourceIncidence

end CMVFigureThree
