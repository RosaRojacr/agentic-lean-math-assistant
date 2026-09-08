/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcEndpointPerturbation
import CMVFourArcSharpRecovery
import CMVCanonicalLowerBound

/-!
# Source competitors for nonstationary four-arc candidates

A nonzero signed contact defect gives an exact-area chord descent.  Interior
candidates use that assembly directly; endpoint candidates first move the
improving assembly to strict strip curvature with exact cap-area correction.
The assembly-level sharp recovery then produces an actual source-admissible
competitor and a strict comparison of extended relaxed perimeters.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

namespace CMVRelaxation.FourArcSourceCompetitor

private theorem assembly_frontierWeightedPerimeter_nonneg
    {lam : ℝ} (hlam : 1 < lam) (a : FourArcAssembly) :
    0 ≤ _root_.WeightedPerimeter lam (FrontierMeasure a.carrier) := by
  unfold _root_.WeightedPerimeter
  apply integral_nonneg
  intro p
  unfold StripDensity
  split_ifs
  · norm_num
  · exact le_trans (by norm_num) hlam.le

private theorem exists_source_competitor_of_strict_frontier
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam)
    (a : FourArcAssembly) (hcurvature : a.core.curvature < 1)
    (harea : a.weightedArea lam = candidate.WeightedArea)
    (hfrontier :
      _root_.WeightedPerimeter lam (FrontierMeasure a.carrier) <
        candidate.WeightedPerimeter) :
    (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam candidate.assembly.carrier ∧
      relaxedPerimeter lam a.carrier <
        relaxedPerimeter lam candidate.assembly.carrier := by
  have hadmissible := FourArcSharpRecovery.assembly_sourceAdmissible
    a hcurvature hlam
  have hequalArea : _root_.WeightedArea lam a.carrier =
      _root_.WeightedArea lam candidate.assembly.carrier := by
    calc
      _root_.WeightedArea lam a.carrier = a.weightedArea lam := rfl
      _ = candidate.WeightedArea := harea
      _ = _root_.WeightedArea lam candidate.assembly.carrier := by
        simpa only [FourArcCandidate.WeightedArea, FourArcCandidate.region,
          AdmissibleCompetitor.carrier] using
          candidate.region.weightedArea_eq_carrier
  have hcandidatePerimeterPos :
      0 < _root_.WeightedPerimeter lam
        (FrontierMeasure candidate.assembly.carrier) :=
    lt_of_le_of_lt
      (assembly_frontierWeightedPerimeter_nonneg hlam a) hfrontier
  refine ⟨hadmissible, hequalArea, ?_⟩
  calc
    relaxedPerimeter lam a.carrier ≤
        ENNReal.ofReal
          (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) :=
      FourArcSharpRecovery.assembly_relaxedPerimeter_le_frontierCost
        a hcurvature hlam
    _ < ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) :=
      (ENNReal.ofReal_lt_ofReal_iff hcandidatePerimeterPos).2 hfrontier
    _ ≤ relaxedPerimeter lam candidate.assembly.carrier :=
      CandidateFourArc.frontierCost_le_relaxedPerimeter candidate hlam

/-- Every four-arc candidate with nonzero signed contact defect has an actual
source-admissible, exactly equal-area competitor with strictly smaller extended
relaxed perimeter.  Both defect signs and both original curvature branches
`h < 1` and `h = 1` are covered.  No source incidence law is assumed. -/
theorem exists_source_competitor_relaxedPerimeter_lt_of_defect
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam)
    (hdefect : lam * Real.cos candidate.alpha - candidate.h ≠ 0) :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam candidate.assembly.carrier ∧
      relaxedPerimeter lam a.carrier <
        relaxedPerimeter lam candidate.assembly.carrier := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  rcases lt_or_eq_of_le candidate.h_le_one with hh | hh
  · rcases candidate.exists_chordVariedAssembly_frontierPerimeter_lt
        hlam0 hdefect with ⟨q, hq, harea, hfrontier⟩
    let a := candidate.chordVariedAssembly q hq
    have hcurvature : a.core.curvature < 1 := by
      simpa [a] using hh
    rcases exists_source_competitor_of_strict_frontier
        candidate hlam a hcurvature harea hfrontier with
      ⟨hadmissible, hequalArea, hstrict⟩
    exact ⟨a, hcurvature, hadmissible, hequalArea, hstrict⟩
  · rcases candidate.exists_strictCurvatureAssembly_frontierPerimeter_lt
        hlam0 hh hdefect with ⟨a, hcurvature, harea, hfrontier⟩
    rcases exists_source_competitor_of_strict_frontier
        candidate hlam a hcurvature harea hfrontier with
      ⟨hadmissible, hequalArea, hstrict⟩
    exact ⟨a, hcurvature, hadmissible, hequalArea, hstrict⟩

/-- Interior test geometry for compiled positive- and negative-defect
applications. -/
def interiorDefectSpecimen (lam : ℝ) : FourArcCandidate lam where
  h := 3 / 4
  alpha := Real.pi / 3
  h_pos := by norm_num
  h_le_one := by norm_num
  alpha_pos := by linarith [Real.pi_pos]
  alpha_lt_pi_div_two := by linarith [Real.pi_pos]

theorem interiorDefectSpecimen_positive :
    (0 : ℝ) < 2 * Real.cos (interiorDefectSpecimen 2).alpha -
      (interiorDefectSpecimen 2).h := by
  simp [interiorDefectSpecimen]
  norm_num

theorem interiorDefectSpecimen_negative :
    (6 / 5 : ℝ) * Real.cos (interiorDefectSpecimen (6 / 5)).alpha -
      (interiorDefectSpecimen (6 / 5)).h < 0 := by
  simp [interiorDefectSpecimen]
  norm_num

/-- Compiled interior positive-defect source competitor. -/
theorem interiorDefectSpecimen_positive_source_competitor :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics 2).IsAdmissible a.carrier ∧
      _root_.WeightedArea 2 a.carrier =
        _root_.WeightedArea 2 (interiorDefectSpecimen 2).assembly.carrier ∧
      relaxedPerimeter 2 a.carrier <
        relaxedPerimeter 2 (interiorDefectSpecimen 2).assembly.carrier := by
  exact exists_source_competitor_relaxedPerimeter_lt_of_defect
    (interiorDefectSpecimen 2) (by norm_num)
      (ne_of_gt interiorDefectSpecimen_positive)

/-- Compiled interior negative-defect source competitor. -/
theorem interiorDefectSpecimen_negative_source_competitor :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics (6 / 5)).IsAdmissible a.carrier ∧
      _root_.WeightedArea (6 / 5) a.carrier =
        _root_.WeightedArea (6 / 5)
          (interiorDefectSpecimen (6 / 5)).assembly.carrier ∧
      relaxedPerimeter (6 / 5) a.carrier <
        relaxedPerimeter (6 / 5)
          (interiorDefectSpecimen (6 / 5)).assembly.carrier := by
  exact exists_source_competitor_relaxedPerimeter_lt_of_defect
    (interiorDefectSpecimen (6 / 5)) (by norm_num)
      (ne_of_lt interiorDefectSpecimen_negative)

/-- Compiled endpoint positive-defect source competitor. -/
theorem endpointDefectSpecimen_positive_source_competitor :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics 3).IsAdmissible a.carrier ∧
      _root_.WeightedArea 3 a.carrier =
        _root_.WeightedArea 3
          (FourArcCandidate.chordDefectSpecimen 3).assembly.carrier ∧
      relaxedPerimeter 3 a.carrier <
        relaxedPerimeter 3
          (FourArcCandidate.chordDefectSpecimen 3).assembly.carrier := by
  exact exists_source_competitor_relaxedPerimeter_lt_of_defect
    (FourArcCandidate.chordDefectSpecimen 3) (by norm_num)
      (ne_of_gt FourArcCandidate.chordDefectSpecimen_positive)

/-- Compiled endpoint negative-defect source competitor. -/
theorem endpointDefectSpecimen_negative_source_competitor :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics (3 / 2)).IsAdmissible a.carrier ∧
      _root_.WeightedArea (3 / 2) a.carrier =
        _root_.WeightedArea (3 / 2)
          (FourArcCandidate.chordDefectSpecimen (3 / 2)).assembly.carrier ∧
      relaxedPerimeter (3 / 2) a.carrier <
        relaxedPerimeter (3 / 2)
          (FourArcCandidate.chordDefectSpecimen (3 / 2)).assembly.carrier := by
  exact exists_source_competitor_relaxedPerimeter_lt_of_defect
    (FourArcCandidate.chordDefectSpecimen (3 / 2)) (by norm_num)
      (ne_of_lt FourArcCandidate.chordDefectSpecimen_negative)

end CMVRelaxation.FourArcSourceCompetitor
