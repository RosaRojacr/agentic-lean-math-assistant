/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FrontierPerimeter

/-!
# Explicit CMV type-(iv) four-arc candidates

A candidate contains only geometric parameters and their nondegenerate domains.
Its coordinate core, two reflected exterior caps, area, and four boundary arcs
are derived definitions.  `SatisfiesCMVTypeIVHypotheses` adds the density jump
and source Snell/incidence equation; it contains no replacement, comparison,
minimality, area formula, or perimeter formula assumption.
-/

open Set
open Real

noncomputable section

/-- Geometric parameters for a genuine four-arc region.  Curvature `h = 1/R`
includes the source's unresolved endpoint `h = 1`. -/
structure FourArcCandidate (lam : ℝ) where
  h : ℝ
  alpha : ℝ
  h_pos : 0 < h
  h_le_one : h ≤ 1
  alpha_pos : 0 < alpha
  alpha_lt_pi_div_two : alpha < π / 2

namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Radius shared by the four source arcs. -/
def radius : ℝ := 1 / candidate.h

/-- Source `β = π/2 - arcsin h`. -/
def beta : ℝ := π / 2 - arcsin candidate.h

/-- Common horizontal chord length of the two exterior caps. -/
def capChord : ℝ := 2 * sin candidate.alpha / candidate.h

/-- Euclidean area of either original exterior cap. -/
def capArea : ℝ :=
  (candidate.alpha - sin candidate.alpha * cos candidate.alpha) /
    candidate.h ^ 2

/-- Scale-free cap area passed to Morgan's arc function. -/
def capX : ℝ := candidate.capArea / candidate.capChord ^ 2

/-- The retained central strip region. -/
def stripCore : StripCore where
  chord := candidate.capChord
  curvature := candidate.h
  chord_pos := by
    exact div_pos (mul_pos (by norm_num)
      (sin_pos_of_pos_of_lt_pi candidate.alpha_pos
        (lt_trans candidate.alpha_lt_pi_div_two
          (by linarith [Real.pi_pos])))) candidate.h_pos
  curvature_pos := candidate.h_pos
  curvature_le_one := candidate.h_le_one

/-- Candidate assembled from the retained strip core and reflected upper/lower
caps. -/
def assembly : FourArcAssembly where
  core := candidate.stripCore
  outerAngle := candidate.alpha
  outerAngle_pos := candidate.alpha_pos
  outerAngle_lt_pi_div_two := candidate.alpha_lt_pi_div_two

/-- The candidate as an admissible regular coordinate region. -/
def region : AdmissibleCompetitor lam := .fourArc candidate.assembly

/-- Candidate weighted area, computed from its region constructor. -/
def WeightedArea : ℝ := candidate.region.WeightedArea

/-- Candidate weighted perimeter, computed from its four boundary arcs. -/
def WeightedPerimeter : ℝ := candidate.region.WeightedPerimeter

/-- Source-specific hypotheses not already enforced by the geometric
constructor.  The equation is CMV (27), equivalently
`alpha = arccos (h / lam)` on the recorded angle domain. -/
structure SatisfiesCMVTypeIVHypotheses : Prop where
  density_jump : 1 < lam
  snell_incidence : lam * cos candidate.alpha = candidate.h

/-- General minimization semantics: comparison is against every admissible
regular competitor, not merely another four-arc candidate. -/
def IsWeightedPerimeterMinimizer : Prop :=
  ∀ competitor : AdmissibleCompetitor lam,
    competitor.WeightedArea = candidate.WeightedArea →
      candidate.WeightedPerimeter ≤ competitor.WeightedPerimeter

theorem sin_alpha_pos : 0 < sin candidate.alpha :=
  sin_pos_of_pos_of_lt_pi candidate.alpha_pos
    (lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos]))

theorem capChord_pos : 0 < candidate.capChord := by
  exact div_pos (mul_pos (by norm_num) candidate.sin_alpha_pos) candidate.h_pos

theorem capChord_ne : candidate.capChord ≠ 0 := ne_of_gt candidate.capChord_pos

theorem capArea_eq_chord_sq_mul_area :
    candidate.capArea = candidate.capChord ^ 2 * area candidate.alpha := by
  rw [capArea, capChord, area]
  field_simp [ne_of_gt candidate.h_pos, ne_of_gt candidate.sin_alpha_pos]
  ring

theorem capArea_pos : 0 < candidate.capArea := by
  rw [candidate.capArea_eq_chord_sq_mul_area]
  exact mul_pos (sq_pos_of_pos candidate.capChord_pos)
    (area_pos candidate.alpha_pos
      (lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos])))

theorem capX_eq_area : candidate.capX = area candidate.alpha := by
  rw [capX, candidate.capArea_eq_chord_sq_mul_area]
  field_simp [candidate.capChord_ne]

theorem capX_pos : 0 < candidate.capX := by
  rw [candidate.capX_eq_area]
  exact area_pos candidate.alpha_pos
    (lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos]))

/-- The normalized area of each original minor cap lies in CMV's strict
geometric interval `(0, π/8)`. -/
theorem capX_lt_pi_div_eight : candidate.capX < π / 8 := by
  rw [candidate.capX_eq_area]
  have hpiHalf : π / 2 ∈ Ioo (0 : ℝ) π := by
    constructor <;> linarith [Real.pi_pos]
  have hlt := area_strictMonoOn
    ⟨candidate.alpha_pos,
      lt_trans candidate.alpha_lt_pi_div_two hpiHalf.2⟩
    hpiHalf candidate.alpha_lt_pi_div_two
  have hareaHalf : area (π / 2) = π / 8 := by
    rw [area, sin_pi_div_two, cos_pi_div_two]
    ring
  rw [hareaHalf] at hlt
  exact hlt

theorem capX_mem : candidate.capX ∈ Ioo 0 (π / 8) :=
  ⟨candidate.capX_pos, candidate.capX_lt_pi_div_eight⟩

/-- Each original cap is on the minor branch. -/
theorem original_cap_minor : candidate.alpha < π / 2 :=
  candidate.alpha_lt_pi_div_two

@[simp] theorem assembly_core : candidate.assembly.core = candidate.stripCore := rfl
@[simp] theorem assembly_outerAngle : candidate.assembly.outerAngle = candidate.alpha := rfl

/-- The upper cap's constructor area is the source cap area; no scalar area is
stored in the candidate. -/
theorem upperCap_euclideanArea :
    candidate.assembly.upperCap.euclideanArea = candidate.capArea := by
  rw [OneSidedCircularCap.euclideanArea,
    candidate.capArea_eq_chord_sq_mul_area]
  rfl

theorem lowerCap_euclideanArea :
    candidate.assembly.lowerCap.euclideanArea = candidate.capArea := by
  rw [OneSidedCircularCap.euclideanArea,
    candidate.capArea_eq_chord_sq_mul_area]
  rfl

/-- The endpoint-incidence definition forces the exterior and strip radii to
agree. -/
theorem four_arcs_common_radius :
    candidate.assembly.upperCap.radius = candidate.stripCore.radius ∧
    candidate.assembly.lowerCap.radius = candidate.stripCore.radius := by
  have hinc : candidate.stripCore.chord * candidate.stripCore.curvature =
      2 * sin candidate.assembly.outerAngle := by
    simp only [stripCore, assembly, capChord]
    field_simp [ne_of_gt candidate.h_pos]
  constructor
  · exact candidate.assembly.outer_radius_eq_core_radius hinc
  · simpa [FourArcAssembly.lowerCap, FourArcAssembly.upperCap,
      OneSidedCircularCap.radius] using
      candidate.assembly.outer_radius_eq_core_radius hinc

/-- Reflection in the horizontal axis exchanges the upper and lower cap arcs,
including the `h = 1` endpoint. -/
theorem exterior_horizontal_reflection (t : ℝ) :
    let reflectHorizontal : PlanePoint → PlanePoint := fun p => (p.1, -p.2)
    reflectHorizontal (candidate.assembly.upperCap.arcPoint t) =
      candidate.assembly.lowerCap.arcPoint t := by
  simp [FourArcAssembly.upperCap, FourArcAssembly.lowerCap,
    OneSidedCircularCap.arcPoint, OneSidedCircularCap.radius, assembly]
  ring_nf

/-- Reflection in the vertical axis reverses either exterior arc parameter. -/
theorem upper_vertical_reflection (t : ℝ) :
    let reflectVertical : PlanePoint → PlanePoint := fun p => (-p.1, p.2)
    reflectVertical (candidate.assembly.upperCap.arcPoint t) =
      candidate.assembly.upperCap.arcPoint (-t) := by
  simp [FourArcAssembly.upperCap, OneSidedCircularCap.arcPoint,
    assembly, sin_neg]

/-- The source incidence equation gives the accepted principal arccos
parameterization. -/
theorem alpha_eq_arccos (h : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.alpha = arccos (candidate.h / lam) := by
  have hlam_pos : 0 < lam := lt_trans zero_lt_one h.density_jump
  have hratio_nonneg : 0 ≤ candidate.h / lam :=
    (div_pos candidate.h_pos hlam_pos).le
  have hratio_le_one : candidate.h / lam ≤ 1 := by
    apply (div_le_one hlam_pos).2
    exact le_trans candidate.h_le_one h.density_jump.le
  symm
  apply Real.arccos_eq_of_eq_cos candidate.alpha_pos.le
    (le_trans candidate.alpha_lt_pi_div_two.le
      (by linarith [Real.pi_pos]))
  exact (div_eq_iff (ne_of_gt hlam_pos)).2 (by
    simpa [mul_comm] using h.snell_incidence.symm)

/-- A concrete `h = 1` constructor proves that the geometric hypothesis
predicate is consistent for every strip density `lam > 1`. -/
theorem hypotheses_nonempty {lam : ℝ} (hlam : 1 < lam) :
    ∃ candidate : FourArcCandidate lam,
      candidate.SatisfiesCMVTypeIVHypotheses := by
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam
  have hxpos : 0 < (1 : ℝ) / lam := one_div_pos.mpr hlam_pos
  have hxlt : (1 : ℝ) / lam < 1 := (div_lt_one hlam_pos).2 hlam
  let candidate : FourArcCandidate lam :=
    { h := 1
      alpha := arccos (1 / lam)
      h_pos := by norm_num
      h_le_one := le_rfl
      alpha_pos := Real.arccos_pos.mpr hxlt
      alpha_lt_pi_div_two := Real.arccos_lt_pi_div_two.mpr hxpos }
  refine ⟨candidate, ?_⟩
  refine { density_jump := hlam, snell_incidence := ?_ }
  dsimp [candidate]
  rw [Real.cos_arccos (by linarith) hxlt.le]
  field_simp [ne_of_gt hlam_pos]

/-- The strip side-segment formula obtained from the coordinate constructor. -/
theorem side_caps_area_formula :
    8 * area candidate.stripCore.sideAngle =
      2 * (arcsin candidate.h -
        candidate.h * √(1 - candidate.h ^ 2)) / candidate.h ^ 2 := by
  change 8 * area (arcsin candidate.h) =
    2 * (arcsin candidate.h -
      candidate.h * √(1 - candidate.h ^ 2)) / candidate.h ^ 2
  rw [area, Real.sin_arcsin (by linarith [candidate.h_pos])
    candidate.h_le_one, Real.cos_arcsin]
  field_simp [ne_of_gt candidate.h_pos]
  ring

/-- Candidate area as the sum of the actual core and cap constructors. -/
theorem weightedArea_components :
    candidate.WeightedArea = candidate.stripCore.euclideanArea +
      2 * lam * candidate.capArea := by
  change candidate.assembly.weightedArea lam =
    candidate.stripCore.euclideanArea + 2 * lam * candidate.capArea
  rw [FourArcAssembly.weightedArea_formula, assembly_core,
    candidate.upperCap_euclideanArea, candidate.lowerCap_euclideanArea]
  ring

/-- Candidate perimeter as the sum of its four actual arc constructors. -/
theorem weightedPerimeter_components :
    candidate.WeightedPerimeter = candidate.stripCore.boundaryArcLength +
      2 * lam * candidate.capChord * ell candidate.alpha := by
  rw [FourArcCandidate.WeightedPerimeter, region,
    AdmissibleCompetitor.WeightedPerimeter]
  change _root_.WeightedPerimeter lam
      (FrontierMeasure candidate.assembly.carrier) =
    candidate.stripCore.boundaryArcLength +
      2 * lam * candidate.capChord * ell candidate.alpha
  rw [← fourArc_frontier_weightedPerimeter_eq,
    FourArcAssembly.weightedPerimeter_formula]
  simp only [StripCore.boundaryArcLength,
    OneSidedCircularCap.arcLength, FourArcAssembly.upperCap,
    FourArcAssembly.lowerCap, assembly, stripCore]
  ring

/-- CMV equation (27), derived from the boundary pieces. -/
theorem candidate_perimeter_formula
    (_h : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedPerimeter =
      4 * lam * candidate.alpha / candidate.h +
        4 * arcsin candidate.h / candidate.h := by
  rw [candidate.weightedPerimeter_components,
    StripCore.boundaryArcLength]
  change 4 * (arcsin candidate.h / sin (arcsin candidate.h)) +
      2 * lam * (2 * sin candidate.alpha / candidate.h) *
        (candidate.alpha / sin candidate.alpha) =
    4 * lam * candidate.alpha / candidate.h +
      4 * arcsin candidate.h / candidate.h
  rw [Real.sin_arcsin (by linarith [candidate.h_pos])
    candidate.h_le_one]
  field_simp [ne_of_gt candidate.h_pos, ne_of_gt candidate.sin_alpha_pos]
  ring

/-- CMV's area display following equation (27), derived from the rectangle and
three cap pieces. -/
theorem candidate_area_formula
    (h : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedArea =
      4 * sin candidate.alpha / candidate.h +
      2 * (lam * candidate.alpha -
        sin candidate.alpha * cos candidate.beta) / candidate.h ^ 2 +
      2 * (arcsin candidate.h -
        candidate.h * √(1 - candidate.h ^ 2)) / candidate.h ^ 2 := by
  rw [candidate.weightedArea_components, StripCore.euclideanArea,
    candidate.side_caps_area_formula]
  simp only [stripCore, capChord]
  have hcosBeta : cos candidate.beta = candidate.h := by
    rw [beta, Real.cos_pi_div_two_sub]
    exact Real.sin_arcsin (by linarith [candidate.h_pos]) candidate.h_le_one
  rw [hcosBeta, capArea]
  field_simp [ne_of_gt candidate.h_pos]
  have hsnell_mul := congrArg (fun z : ℝ => sin candidate.alpha * z)
    h.snell_incidence
  nlinarith [hsnell_mul]

end FourArcCandidate
