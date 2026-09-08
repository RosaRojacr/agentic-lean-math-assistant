/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FourArcCandidate
import GFunction

/-!
# Exact-area chord variations of four-arc assemblies

The strip curvature is fixed while the common attachment chord varies.  The
exterior angle is recovered from Morgan's area inverse.  This construction does
not assume that the exterior and strip radii agree and does not assume a Snell
contact law.
-/

open Set
open Real
open Filter

noncomputable section
open scoped Topology


namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Per-cap Euclidean area forced by preserving total weighted area while the
strip chord changes from `candidate.capChord` to `q`. -/
def chordAdjustedCapArea (q : ℝ) : ℝ :=
  candidate.capArea + (candidate.capChord - q) / lam

/-- Morgan-normalized area of either adjusted exterior cap. -/
def chordAdjustedX (q : ℝ) : ℝ :=
  candidate.chordAdjustedCapArea q / q ^ 2

/-- Open domain on which the adjusted caps are positive minor circular caps. -/
def ChordVariationValid (q : ℝ) : Prop :=
  0 < q ∧ 0 < candidate.chordAdjustedX q ∧
    candidate.chordAdjustedX q < π / 8

@[simp] theorem chordAdjustedCapArea_self :
    candidate.chordAdjustedCapArea candidate.capChord = candidate.capArea := by
  simp [chordAdjustedCapArea]

@[simp] theorem chordAdjustedX_self :
    candidate.chordAdjustedX candidate.capChord = candidate.capX := by
  simp [chordAdjustedX, FourArcCandidate.capX]

/-- The fixed-curvature strip core with a freely prescribed positive chord. -/
def chordVariedCore (q : ℝ) (hq : 0 < q) : StripCore where
  chord := q
  curvature := candidate.h
  chord_pos := hq
  curvature_pos := candidate.h_pos
  curvature_le_one := candidate.h_le_one

/-- The exact-area four-arc assembly on the open valid-chord domain.  Its
exterior radius is deliberately independent of the fixed strip radius. -/
def chordVariedAssembly (q : ℝ) (hq : candidate.ChordVariationValid q) :
    FourArcAssembly where
  core := candidate.chordVariedCore q hq.1
  outerAngle := θOf (candidate.chordAdjustedX q)
  outerAngle_pos := (θOf_mem hq.2.1).1
  outerAngle_lt_pi_div_two := θOf_lt_pi_div_two hq.2.1 hq.2.2

@[simp] theorem chordVariedAssembly_core_chord
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).core.chord = q := rfl

@[simp] theorem chordVariedAssembly_core_curvature
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).core.curvature = candidate.h := rfl

@[simp] theorem chordVariedAssembly_outerAngle
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).outerAngle =
      θOf (candidate.chordAdjustedX q) := rfl

/-- The original attachment chord lies in the open variation domain. -/
theorem chordVariationValid_self :
    candidate.ChordVariationValid candidate.capChord := by
  exact ⟨candidate.capChord_pos, by simpa using candidate.capX_pos,
    by simpa using candidate.capX_lt_pi_div_eight⟩

/-- The positive minor-cap domain contains a full neighborhood of the original
attachment chord. -/
theorem eventually_chordVariationValid (_hlam : 0 < lam) :
    ∀ᶠ q in 𝓝 candidate.capChord, candidate.ChordVariationValid q := by
  have hcap : ContinuousAt candidate.chordAdjustedCapArea candidate.capChord := by
    unfold chordAdjustedCapArea
    fun_prop
  have hx : ContinuousAt candidate.chordAdjustedX candidate.capChord := by
    unfold chordAdjustedX
    exact hcap.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 candidate.capChord_ne)
  have hxpos : ∀ᶠ q in 𝓝 candidate.capChord,
      0 < candidate.chordAdjustedX q :=
    hx.eventually_const_lt (by simpa using candidate.capX_pos)
  have hxminor : ∀ᶠ q in 𝓝 candidate.capChord,
      candidate.chordAdjustedX q < π / 8 :=
    hx.eventually_lt_const (by simpa using candidate.capX_lt_pi_div_eight)
  filter_upwards [Ioi_mem_nhds candidate.capChord_pos, hxpos, hxminor]
    with q hq hqpos hqminor
  exact ⟨hq, hqpos, hqminor⟩

/-- Each adjusted upper cap has exactly the prescribed cap area. -/
theorem chordVariedAssembly_upperCap_area
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).upperCap.euclideanArea =
      candidate.chordAdjustedCapArea q := by
  change q ^ 2 * area (θOf (candidate.chordAdjustedX q)) =
    candidate.chordAdjustedCapArea q
  rw [area_θOf hq.2.1]
  unfold chordAdjustedX
  field_simp [ne_of_gt hq.1]

/-- Each adjusted lower cap has exactly the prescribed cap area. -/
theorem chordVariedAssembly_lowerCap_area
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).lowerCap.euclideanArea =
      candidate.chordAdjustedCapArea q := by
  change q ^ 2 * area (θOf (candidate.chordAdjustedX q)) =
    candidate.chordAdjustedCapArea q
  rw [area_θOf hq.2.1]
  unfold chordAdjustedX
  field_simp [ne_of_gt hq.1]

/-- The varied assembly has exactly the original ambient weighted area. -/
theorem chordVariedAssembly_weightedArea
    (hlam : 0 < lam) (q : ℝ) (hq : candidate.ChordVariationValid q) :
    (candidate.chordVariedAssembly q hq).weightedArea lam =
      candidate.WeightedArea := by
  rw [FourArcAssembly.weightedArea_formula,
    candidate.weightedArea_components,
    candidate.chordVariedAssembly_upperCap_area q hq,
    candidate.chordVariedAssembly_lowerCap_area q hq]
  simp only [chordVariedAssembly, chordVariedCore,
    StripCore.euclideanArea, StripCore.sideAngle,
    FourArcCandidate.stripCore]
  unfold chordAdjustedCapArea
  field_simp [ne_of_gt hlam]
  ring

/-- Scalar expression for the complete-frontier weighted perimeter of every
valid varied assembly. -/
def chordFrontierPerimeter (q : ℝ) : ℝ :=
  candidate.stripCore.boundaryArcLength +
    2 * lam * q * arc (candidate.chordAdjustedX q)

/-- The scalar variation is the actual density integral on the complete
frontier of the varied carrier. -/
theorem chordVariedAssembly_frontierPerimeter
    (q : ℝ) (hq : candidate.ChordVariationValid q) :
    _root_.WeightedPerimeter lam
        (FrontierMeasure (candidate.chordVariedAssembly q hq).carrier) =
      candidate.chordFrontierPerimeter q := by
  rw [← fourArc_frontier_weightedPerimeter_eq,
    FourArcAssembly.weightedPerimeter_formula]
  simp only [chordFrontierPerimeter, chordVariedAssembly, chordVariedCore,
    StripCore.boundaryArcLength, StripCore.sideAngle,
    FourArcAssembly.upperCap, FourArcAssembly.lowerCap,
    OneSidedCircularCap.arcLength, arc_eq,
    FourArcCandidate.stripCore]
  ring

/-- At the original chord the scalar perimeter is the candidate's actual
complete-frontier perimeter. -/
@[simp] theorem chordFrontierPerimeter_self :
    candidate.chordFrontierPerimeter candidate.capChord =
      candidate.WeightedPerimeter := by
  rw [candidate.weightedPerimeter_components]
  have halpha : candidate.alpha ∈ Ioo (0 : ℝ) π :=
    ⟨candidate.alpha_pos,
      lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos])⟩
  simp only [chordFrontierPerimeter, chordAdjustedX_self,
    candidate.capX_eq_area, arc_eq, θOf_area halpha]

/-- Derivative of the adjusted normalized cap area at the original chord. -/
theorem chordAdjustedX_hasDerivAt_self (_hlam : 0 < lam) :
    HasDerivAt candidate.chordAdjustedX
      (((-1 / lam) * candidate.capChord ^ 2 -
          candidate.capArea * (2 * candidate.capChord)) /
        (candidate.capChord ^ 2) ^ 2)
      candidate.capChord := by
  have hcap : HasDerivAt candidate.chordAdjustedCapArea (-1 / lam)
      candidate.capChord := by
    have hraw := (hasDerivAt_const candidate.capChord candidate.capArea).add
      (((hasDerivAt_const candidate.capChord candidate.capChord).sub
        (hasDerivAt_id candidate.capChord)).div_const lam)
    simpa only [chordAdjustedCapArea, id_eq] using!
      hraw.congr_deriv (by ring)
  have hden : HasDerivAt (fun q : ℝ => q ^ 2)
      (2 * candidate.capChord) candidate.capChord := by
    have h := (hasDerivAt_id candidate.capChord).mul
      (hasDerivAt_id candidate.capChord)
    apply (h.congr_deriv (by
      simp only [id_eq, one_mul, mul_one]
      ring)).congr_of_eventuallyEq
    filter_upwards
    intro q
    simp only [Pi.mul_apply, id_eq, pow_two]
  have hquot := hcap.div hden (pow_ne_zero 2 candidate.capChord_ne)
  simpa only [chordAdjustedX] using!
    hquot.congr_deriv (by
      rw [candidate.chordAdjustedCapArea_self]
    )

/-- The constrained first variation of the actual four-arc perimeter is twice
the signed contact defect.  No derivative in the strip curvature is taken, so
the statement includes `candidate.h = 1`. -/
theorem chordFrontierPerimeter_hasDerivAt (hlam : 0 < lam) :
    HasDerivAt candidate.chordFrontierPerimeter
      (2 * (lam * cos candidate.alpha - candidate.h))
      candidate.capChord := by
  let dx : ℝ :=
    (((-1 / lam) * candidate.capChord ^ 2 -
        candidate.capArea * (2 * candidate.capChord)) /
      (candidate.capChord ^ 2) ^ 2)
  have hx : HasDerivAt candidate.chordAdjustedX dx candidate.capChord := by
    simpa only [dx] using candidate.chordAdjustedX_hasDerivAt_self hlam
  have halpha : candidate.alpha ∈ Ioo (0 : ℝ) π :=
    ⟨candidate.alpha_pos,
      lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos])⟩
  have htheta : θOf (candidate.chordAdjustedX candidate.capChord) =
      candidate.alpha := by
    rw [candidate.chordAdjustedX_self, candidate.capX_eq_area,
      θOf_area halpha]
  have hthetaCap : θOf candidate.capX = candidate.alpha := by
    rw [candidate.capX_eq_area, θOf_area halpha]
  have harc : HasDerivAt arc (2 * sin candidate.alpha)
      (candidate.chordAdjustedX candidate.capChord) := by
    have h := hasDerivAt_arc candidate.capX_pos
    rw [hthetaCap] at h
    simpa only [candidate.chordAdjustedX_self] using h
  have hcomposed : HasDerivAt (arc ∘ candidate.chordAdjustedX)
      ((2 * sin candidate.alpha) * dx) candidate.capChord :=
    harc.comp candidate.capChord hx
  have hproduct : HasDerivAt
      (fun q => q * arc (candidate.chordAdjustedX q))
      (arc (candidate.chordAdjustedX candidate.capChord) +
        candidate.capChord * (2 * sin candidate.alpha * dx))
      candidate.capChord := by
    have h := (hasDerivAt_id candidate.capChord).mul hcomposed
    have h' : HasDerivAt (id * arc ∘ candidate.chordAdjustedX)
        (arc (candidate.chordAdjustedX candidate.capChord) +
          candidate.capChord * (2 * sin candidate.alpha * dx))
        candidate.capChord := by
      simpa only [Function.comp_apply, id_eq, one_mul] using h
    apply h'.congr_of_eventuallyEq
    filter_upwards
    intro q
    rfl
  have hscaled : HasDerivAt
      (fun q => 2 * lam * (q * arc (candidate.chordAdjustedX q)))
      (2 * lam *
        (arc (candidate.chordAdjustedX candidate.capChord) +
          candidate.capChord * (2 * sin candidate.alpha * dx)))
      candidate.capChord := by
    simpa only using hproduct.const_mul (2 * lam)
  have hraw : HasDerivAt candidate.chordFrontierPerimeter
      (2 * lam *
        (arc (candidate.chordAdjustedX candidate.capChord) +
          candidate.capChord * (2 * sin candidate.alpha * dx)))
      candidate.capChord := by
    have h := (hasDerivAt_const candidate.capChord
      candidate.stripCore.boundaryArcLength).add hscaled
    apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards
    intro q
    simp only [chordFrontierPerimeter, Pi.add_apply]
    ring
  apply hraw.congr_deriv
  rw [arc_eq, htheta]
  dsimp only [dx]
  unfold ell FourArcCandidate.capChord FourArcCandidate.capArea
  field_simp [ne_of_gt hlam, ne_of_gt candidate.h_pos,
    ne_of_gt candidate.sin_alpha_pos]
  ring

/-- A total real-indexed family, equal to the exact varied assembly on its open
domain and to the original assembly elsewhere.  The fallback is irrelevant to
the local derivative but makes the actual carrier perimeter a total function. -/
noncomputable def localChordAssembly
    (candidate : FourArcCandidate lam) (q : ℝ) : FourArcAssembly := by
  classical
  exact if hq : candidate.ChordVariationValid q then
    candidate.chordVariedAssembly q hq
  else
    candidate.assembly

/-- The total family follows the genuine chord variation near the original
chord. -/
theorem localChordAssembly_eq_varied_eventually (hlam : 0 < lam) :
    ∀ᶠ q in 𝓝 candidate.capChord,
      ∃ hq : candidate.ChordVariationValid q,
        candidate.localChordAssembly q = candidate.chordVariedAssembly q hq := by
  filter_upwards [candidate.eventually_chordVariationValid hlam] with q hq
  exact ⟨hq, by simp [localChordAssembly, hq]⟩

/-- Every member of the total family has the original weighted area: on the
valid branch by exact cancellation, and on the fallback branch definitionally. -/
theorem localChordAssembly_weightedArea (hlam : 0 < lam) (q : ℝ) :
    (candidate.localChordAssembly q).weightedArea lam = candidate.WeightedArea := by
  by_cases hq : candidate.ChordVariationValid q
  · rw [localChordAssembly, dif_pos hq]
    exact candidate.chordVariedAssembly_weightedArea hlam q hq
  · rw [localChordAssembly, dif_neg hq]
    rfl

/-- Near the original chord, the total family's actual frontier cost is the
scalar chord-perimeter function. -/
theorem localChordAssembly_frontierPerimeter_eventually (hlam : 0 < lam) :
    (fun q => _root_.WeightedPerimeter lam
      (FrontierMeasure (candidate.localChordAssembly q).carrier)) =ᶠ[
        𝓝 candidate.capChord] candidate.chordFrontierPerimeter := by
  filter_upwards [candidate.eventually_chordVariationValid hlam] with q hq
  rw [localChordAssembly, dif_pos hq]
  exact candidate.chordVariedAssembly_frontierPerimeter q hq

/-- Literal derivative theorem for the actual complete-frontier perimeter of
the total local assembly family. -/
theorem localChordAssembly_frontierPerimeter_hasDerivAt (hlam : 0 < lam) :
    HasDerivAt
      (fun q => _root_.WeightedPerimeter lam
        (FrontierMeasure (candidate.localChordAssembly q).carrier))
      (2 * (lam * cos candidate.alpha - candidate.h))
      candidate.capChord := by
  exact (candidate.chordFrontierPerimeter_hasDerivAt hlam).congr_of_eventuallyEq
    (candidate.localChordAssembly_frontierPerimeter_eventually hlam)

/-- The complete checkpoint package: a neighborhood of actual exact-area
assemblies with positive caps and minor angles, their exact complete-frontier
cost, and the constrained perimeter derivative. -/
theorem exact_area_chord_descent (hlam : 0 < lam) :
    (∀ᶠ q in 𝓝 candidate.capChord,
      ∃ hq : candidate.ChordVariationValid q,
        let a := candidate.chordVariedAssembly q hq
        a.core.chord = q ∧
        a.core.curvature = candidate.h ∧
        a.upperCap.euclideanArea = candidate.chordAdjustedCapArea q ∧
        0 < a.upperCap.euclideanArea ∧
        0 < a.outerAngle ∧ a.outerAngle < π / 2 ∧
        a.weightedArea lam = candidate.WeightedArea ∧
        _root_.WeightedPerimeter lam (FrontierMeasure a.carrier) =
          candidate.chordFrontierPerimeter q) ∧
      HasDerivAt
        (fun q => _root_.WeightedPerimeter lam
          (FrontierMeasure (candidate.localChordAssembly q).carrier))
        (2 * (lam * cos candidate.alpha - candidate.h))
        candidate.capChord := by
  constructor
  · filter_upwards [candidate.eventually_chordVariationValid hlam] with q hq
    refine ⟨hq, rfl, rfl,
      candidate.chordVariedAssembly_upperCap_area q hq, ?_, ?_, ?_,
      candidate.chordVariedAssembly_weightedArea hlam q hq,
      candidate.chordVariedAssembly_frontierPerimeter q hq⟩
    · rw [candidate.chordVariedAssembly_upperCap_area q hq]
      rw [← show q ^ 2 * candidate.chordAdjustedX q =
          candidate.chordAdjustedCapArea q by
        unfold chordAdjustedX
        field_simp [ne_of_gt hq.1]]
      exact mul_pos (sq_pos_of_pos hq.1) hq.2.1
    · exact (θOf_mem hq.2.1).1
    · exact θOf_lt_pi_div_two hq.2.1 hq.2.2
  · exact candidate.localChordAssembly_frontierPerimeter_hasDerivAt hlam

/-- Every nonzero signed contact defect gives a genuine nearby exact-area
four-arc assembly with strictly lower complete-frontier perimeter. -/
theorem exists_chordVariedAssembly_frontierPerimeter_lt
    (hlam : 0 < lam)
    (hdefect : lam * cos candidate.alpha - candidate.h ≠ 0) :
    ∃ q, ∃ hq : candidate.ChordVariationValid q,
      (candidate.chordVariedAssembly q hq).weightedArea lam =
          candidate.WeightedArea ∧
        _root_.WeightedPerimeter lam
            (FrontierMeasure (candidate.chordVariedAssembly q hq).carrier) <
          candidate.WeightedPerimeter := by
  have hderiv := candidate.chordFrontierPerimeter_hasDerivAt hlam
  have hnotmin : ¬ IsLocalMin candidate.chordFrontierPerimeter
      candidate.capChord := by
    intro hmin
    have hzero := hmin.hasDerivAt_eq_zero hderiv
    apply hdefect
    linarith
  by_contra hexists
  have hge : ∀ q, candidate.ChordVariationValid q →
      candidate.chordFrontierPerimeter candidate.capChord ≤
        candidate.chordFrontierPerimeter q := by
    intro q hq
    exact le_of_not_gt (fun hlt => hexists ⟨q, hq,
      candidate.chordVariedAssembly_weightedArea hlam q hq, by
        rw [candidate.chordVariedAssembly_frontierPerimeter q hq,
          ← candidate.chordFrontierPerimeter_self]
        exact hlt⟩)
  apply hnotmin
  unfold IsLocalMin IsMinFilter
  filter_upwards [candidate.eventually_chordVariationValid hlam] with q hq
  exact hge q hq

/-- A simple `h = 1`, `alpha = pi/3` geometry used to exercise both signs of
the constrained first variation without differentiating at the endpoint. -/
def chordDefectSpecimen (lam : ℝ) : FourArcCandidate lam where
  h := 1
  alpha := π / 3
  h_pos := by norm_num
  h_le_one := le_rfl
  alpha_pos := by linarith [Real.pi_pos]
  alpha_lt_pi_div_two := by linarith [Real.pi_pos]

/-- At density three the endpoint specimen has positive signed contact defect. -/
theorem chordDefectSpecimen_positive :
    (0 : ℝ) < 3 * cos (chordDefectSpecimen 3).alpha -
      (chordDefectSpecimen 3).h := by
  simp [chordDefectSpecimen]
  norm_num

/-- At density three-halves the same endpoint geometry has negative signed
contact defect. -/
theorem chordDefectSpecimen_negative :
    (3 / 2 : ℝ) * cos (chordDefectSpecimen (3 / 2)).alpha -
      (chordDefectSpecimen (3 / 2)).h < 0 := by
  simp [chordDefectSpecimen]
  norm_num

/-- Compiled positive-defect endpoint descent application. -/
theorem chordDefectSpecimen_positive_descent :
    ∃ q, ∃ hq : (chordDefectSpecimen 3).ChordVariationValid q,
      ((chordDefectSpecimen 3).chordVariedAssembly q hq).weightedArea 3 =
          (chordDefectSpecimen 3).WeightedArea ∧
        _root_.WeightedPerimeter 3
            (FrontierMeasure
              ((chordDefectSpecimen 3).chordVariedAssembly q hq).carrier) <
          (chordDefectSpecimen 3).WeightedPerimeter := by
  exact (chordDefectSpecimen 3).exists_chordVariedAssembly_frontierPerimeter_lt
    (by norm_num) (ne_of_gt chordDefectSpecimen_positive)

/-- Compiled negative-defect endpoint descent application. -/
theorem chordDefectSpecimen_negative_descent :
    ∃ q, ∃ hq : (chordDefectSpecimen (3 / 2)).ChordVariationValid q,
      ((chordDefectSpecimen (3 / 2)).chordVariedAssembly q hq).weightedArea
          (3 / 2) = (chordDefectSpecimen (3 / 2)).WeightedArea ∧
        _root_.WeightedPerimeter (3 / 2)
            (FrontierMeasure
              ((chordDefectSpecimen (3 / 2)).chordVariedAssembly q hq).carrier) <
          (chordDefectSpecimen (3 / 2)).WeightedPerimeter := by
  exact (chordDefectSpecimen (3 / 2)).exists_chordVariedAssembly_frontierPerimeter_lt
    (by norm_num) (ne_of_lt chordDefectSpecimen_negative)

end FourArcCandidate
