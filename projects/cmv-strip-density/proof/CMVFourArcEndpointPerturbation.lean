/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcChordVariation

/-!
# Strict-curvature realization of endpoint chord descent

A fixed improving chord variation at strip curvature one is moved to curvature
strictly below one.  The two cap areas are corrected exactly for the change in
strip-core area, and Morgan's inverse recovers the positive minor caps.  Only
one-sided continuity at curvature one is used.
-/

open Set
open Real
open Filter

noncomputable section
open scoped Topology

namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Per-cap area after changing both the attachment chord and strip curvature.
The second term exactly compensates half of the strip-core area change. -/
def curvatureAdjustedCapArea (q k : ℝ) : ℝ :=
  candidate.chordAdjustedCapArea q +
    4 * (area (arcsin candidate.h) - area (arcsin k)) / lam

/-- Morgan-normalized area for the curvature-adjusted exterior caps. -/
def curvatureAdjustedX (q k : ℝ) : ℝ :=
  candidate.curvatureAdjustedCapArea q k / q ^ 2

/-- Domain for a positive strip curvature and positive minor adjusted caps. -/
def ChordCurvatureVariationValid (q k : ℝ) : Prop :=
  0 < q ∧ 0 < k ∧ k ≤ 1 ∧
    0 < candidate.curvatureAdjustedX q k ∧
    candidate.curvatureAdjustedX q k < π / 8

@[simp] theorem curvatureAdjustedCapArea_self (q : ℝ) :
    candidate.curvatureAdjustedCapArea q candidate.h =
      candidate.chordAdjustedCapArea q := by
  simp [curvatureAdjustedCapArea]

@[simp] theorem curvatureAdjustedX_self (q : ℝ) :
    candidate.curvatureAdjustedX q candidate.h =
      candidate.chordAdjustedX q := by
  simp [curvatureAdjustedX, chordAdjustedX]

/-- Every valid fixed-curvature chord variation is the base point of the
curvature-adjusted family. -/
theorem chordCurvatureVariationValid_self
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    candidate.ChordCurvatureVariationValid q candidate.h := by
  exact ⟨hq.1, candidate.h_pos, candidate.h_le_one,
    by simpa using hq.2.1, by simpa using hq.2.2⟩

/-- Strip core with independently prescribed chord and curvature. -/
def curvatureVariedCore (q k : ℝ)
    (hv : candidate.ChordCurvatureVariationValid q k) : StripCore where
  chord := q
  curvature := k
  chord_pos := hv.1
  curvature_pos := hv.2.1
  curvature_le_one := hv.2.2.1

/-- Exact-area curvature-adjusted assembly. -/
def curvatureVariedAssembly (q k : ℝ)
    (hv : candidate.ChordCurvatureVariationValid q k) : FourArcAssembly where
  core := candidate.curvatureVariedCore q k hv
  outerAngle := θOf (candidate.curvatureAdjustedX q k)
  outerAngle_pos := (θOf_mem hv.2.2.2.1).1
  outerAngle_lt_pi_div_two :=
    θOf_lt_pi_div_two hv.2.2.2.1 hv.2.2.2.2

@[simp] theorem curvatureVariedAssembly_core_chord
    (q k : ℝ) (hv : candidate.ChordCurvatureVariationValid q k) :
    (candidate.curvatureVariedAssembly q k hv).core.chord = q := rfl

@[simp] theorem curvatureVariedAssembly_core_curvature
    (q k : ℝ) (hv : candidate.ChordCurvatureVariationValid q k) :
    (candidate.curvatureVariedAssembly q k hv).core.curvature = k := rfl

/-- Each adjusted upper cap has the prescribed corrected area. -/
theorem curvatureVariedAssembly_upperCap_area
    (q k : ℝ) (hv : candidate.ChordCurvatureVariationValid q k) :
    (candidate.curvatureVariedAssembly q k hv).upperCap.euclideanArea =
      candidate.curvatureAdjustedCapArea q k := by
  change q ^ 2 * area (θOf (candidate.curvatureAdjustedX q k)) =
    candidate.curvatureAdjustedCapArea q k
  rw [area_θOf hv.2.2.2.1]
  unfold curvatureAdjustedX
  field_simp [ne_of_gt hv.1]

/-- The lower cap has the same corrected area. -/
theorem curvatureVariedAssembly_lowerCap_area
    (q k : ℝ) (hv : candidate.ChordCurvatureVariationValid q k) :
    (candidate.curvatureVariedAssembly q k hv).lowerCap.euclideanArea =
      candidate.curvatureAdjustedCapArea q k := by
  change q ^ 2 * area (θOf (candidate.curvatureAdjustedX q k)) =
    candidate.curvatureAdjustedCapArea q k
  rw [area_θOf hv.2.2.2.1]
  unfold curvatureAdjustedX
  field_simp [ne_of_gt hv.1]

/-- The cap correction preserves the original candidate's actual weighted area
exactly, for every valid perturbed curvature. -/
theorem curvatureVariedAssembly_weightedArea
    (hlam : 0 < lam) (q k : ℝ)
    (hv : candidate.ChordCurvatureVariationValid q k) :
    (candidate.curvatureVariedAssembly q k hv).weightedArea lam =
      candidate.WeightedArea := by
  rw [FourArcAssembly.weightedArea_formula,
    candidate.weightedArea_components,
    candidate.curvatureVariedAssembly_upperCap_area q k hv,
    candidate.curvatureVariedAssembly_lowerCap_area q k hv]
  simp only [curvatureVariedAssembly, curvatureVariedCore,
    StripCore.euclideanArea, StripCore.sideAngle,
    FourArcCandidate.stripCore]
  unfold curvatureAdjustedCapArea chordAdjustedCapArea
  field_simp [ne_of_gt hlam]
  ring

/-- Scalar complete-frontier perimeter along the curvature-adjusted family. -/
def curvatureFrontierPerimeter (q k : ℝ) : ℝ :=
  4 * ell (arcsin k) +
    2 * lam * q * arc (candidate.curvatureAdjustedX q k)

/-- The scalar expression is the actual complete-frontier weighted perimeter. -/
theorem curvatureVariedAssembly_frontierPerimeter
    (q k : ℝ) (hv : candidate.ChordCurvatureVariationValid q k) :
    _root_.WeightedPerimeter lam
        (FrontierMeasure (candidate.curvatureVariedAssembly q k hv).carrier) =
      candidate.curvatureFrontierPerimeter q k := by
  rw [← fourArc_frontier_weightedPerimeter_eq,
    FourArcAssembly.weightedPerimeter_formula]
  simp only [curvatureFrontierPerimeter, curvatureVariedAssembly,
    curvatureVariedCore, StripCore.boundaryArcLength, StripCore.sideAngle,
    FourArcAssembly.upperCap, FourArcAssembly.lowerCap,
    OneSidedCircularCap.arcLength, arc_eq]
  ring

/-- At the original curvature this scalar family is exactly the fixed-curvature
chord-perimeter family. -/
@[simp] theorem curvatureFrontierPerimeter_self (q : ℝ) :
    candidate.curvatureFrontierPerimeter q candidate.h =
      candidate.chordFrontierPerimeter q := by
  simp [curvatureFrontierPerimeter, chordFrontierPerimeter,
    StripCore.boundaryArcLength, StripCore.sideAngle,
    FourArcCandidate.stripCore]

private theorem arcsin_h_mem :
    arcsin candidate.h ∈ Ioo (0 : ℝ) π := by
  exact ⟨Real.arcsin_pos.mpr candidate.h_pos,
    lt_of_le_of_lt (Real.arcsin_le_pi_div_two candidate.h)
      (by linarith [Real.pi_pos])⟩

/-- The normalized corrected cap area is continuous at the original
curvature. -/
theorem curvatureAdjustedX_continuousAt_self (q : ℝ) :
    ContinuousAt (candidate.curvatureAdjustedX q) candidate.h := by
  have harea : ContinuousAt (fun k : ℝ => area (arcsin k)) candidate.h :=
    (hasDerivAt_area candidate.arcsin_h_mem.1
      candidate.arcsin_h_mem.2).continuousAt.comp
        Real.continuousAt_arcsin
  unfold curvatureAdjustedX curvatureAdjustedCapArea
  fun_prop

/-- The actual scalar frontier perimeter is continuous at the original
curvature, including one-sided use when that curvature is one. -/
theorem curvatureFrontierPerimeter_continuousAt_self
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    ContinuousAt (candidate.curvatureFrontierPerimeter q) candidate.h := by
  have hside : ContinuousAt (fun k : ℝ => ell (arcsin k)) candidate.h :=
    (hasDerivAt_ell candidate.arcsin_h_mem.1
      candidate.arcsin_h_mem.2).continuousAt.comp
        Real.continuousAt_arcsin
  have hx := candidate.curvatureAdjustedX_continuousAt_self q
  have harc : ContinuousAt arc (candidate.curvatureAdjustedX q candidate.h) := by
    apply HasDerivAt.continuousAt
    apply hasDerivAt_arc
    simpa using hq.2.1
  have hcomposed : ContinuousAt
      (fun k : ℝ => arc (candidate.curvatureAdjustedX q k)) candidate.h :=
    harc.comp hx
  unfold curvatureFrontierPerimeter
  fun_prop

/-- An improving fixed-chord endpoint variation can be moved to strictly
subunit strip curvature.  Exact area is restored by the cap correction, while
positive minor caps and the strict complete-frontier gap persist by continuity.
No derivative at curvature one is used. -/
theorem exists_strictCurvatureAssembly_frontierPerimeter_lt
    (hlam : 0 < lam) (hh : candidate.h = 1)
    (hdefect : lam * cos candidate.alpha - candidate.h ≠ 0) :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      a.weightedArea lam = candidate.WeightedArea ∧
      _root_.WeightedPerimeter lam (FrontierMeasure a.carrier) <
        candidate.WeightedPerimeter := by
  rcases candidate.exists_chordVariedAssembly_frontierPerimeter_lt
      hlam hdefect with ⟨q, hq, harea, hfrontier⟩
  have hscalar : candidate.curvatureFrontierPerimeter q candidate.h <
      candidate.WeightedPerimeter := by
    rw [candidate.curvatureFrontierPerimeter_self]
    rw [← candidate.chordVariedAssembly_frontierPerimeter q hq]
    exact hfrontier
  have hperimeter : ∀ᶠ k in 𝓝 candidate.h,
      candidate.curvatureFrontierPerimeter q k <
        candidate.WeightedPerimeter :=
    (candidate.curvatureFrontierPerimeter_continuousAt_self q hq).tendsto.eventually_lt_const
      hscalar
  have hx := candidate.curvatureAdjustedX_continuousAt_self q
  have hxpos : ∀ᶠ k in 𝓝 candidate.h,
      0 < candidate.curvatureAdjustedX q k :=
    hx.tendsto.eventually_const_lt (by simpa using hq.2.1)
  have hxminor : ∀ᶠ k in 𝓝 candidate.h,
      candidate.curvatureAdjustedX q k < π / 8 :=
    hx.tendsto.eventually_lt_const (by simpa using hq.2.2)
  have hkpos : ∀ᶠ k in 𝓝 candidate.h, 0 < k :=
    eventually_gt_nhds candidate.h_pos
  rw [hh] at hperimeter hxpos hxminor hkpos
  have hgood : ∀ᶠ k in 𝓝[<] (1 : ℝ),
      0 < k ∧
      0 < candidate.curvatureAdjustedX q k ∧
      candidate.curvatureAdjustedX q k < π / 8 ∧
      candidate.curvatureFrontierPerimeter q k <
        candidate.WeightedPerimeter :=
    (hkpos.and (hxpos.and (hxminor.and hperimeter))).filter_mono
      nhdsWithin_le_nhds
  have hklt : ∀ᶠ k in 𝓝[<] (1 : ℝ), k < 1 := by
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact hk
  rcases (hgood.and hklt).exists with
    ⟨k, ⟨hkpos', ⟨hxpos', ⟨hxminor', hperimeter'⟩⟩⟩, hklt'⟩
  have hv : candidate.ChordCurvatureVariationValid q k :=
    ⟨hq.1, hkpos', hklt'.le, hxpos', hxminor'⟩
  let a := candidate.curvatureVariedAssembly q k hv
  refine ⟨a, ?_, candidate.curvatureVariedAssembly_weightedArea hlam q k hv, ?_⟩
  · simpa [a] using hklt'
  · rw [candidate.curvatureVariedAssembly_frontierPerimeter q k hv]
    exact hperimeter'

end FourArcCandidate
