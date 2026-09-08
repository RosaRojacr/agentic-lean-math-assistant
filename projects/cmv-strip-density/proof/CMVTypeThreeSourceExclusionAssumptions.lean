import CMVTypeThreeSourceExclusion
import CMVFigureFourBilateralExamples

namespace CMVRelaxation.TypeThreeSourceExclusion

open CMVSourceClassification.RawFourArcCoordinates

#print axioms exists_typeThree_source_competitor_frontier_lt
#print axioms exists_typeThree_source_competitor_relaxedPerimeter_lt
#print axioms exists_source_competitor_relaxedPerimeter_lt
#print axioms candidateCarrier_not_isMinimizer
#print axioms sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
#print axioms sourceCarrier_not_isMinimizer_of_horizontalCongruence_candidate
#print axioms endpointCarrier_not_isMinimizer
#print axioms endpointSourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
#print axioms endpointSourceCarrier_not_isMinimizer_of_horizontalCongruence
#print axioms rawFourArcCarrier_not_isMinimizer
#print axioms sourceCarrier_not_isMinimizer_of_ae_rawFourArcCoordinates
#print axioms sourceCarrier_not_isMinimizer_of_horizontalSections
#print axioms sourceCarrier_not_isMinimizer_of_centeredIntervals_of_measure_eq
#print axioms
  CMVSourceClassification.RawFourArcCoordinates.horizontalSection_eq_Icc_of_abs_lt_one
#print axioms
  CMVSourceClassification.RawFourArcCoordinates.ae_horizontalSection_empty_or_centered_interval
#print axioms
  CMVSourceClassification.RawFourArcCoordinates.hasCenteredHorizontalIntervalSections
#print axioms
  CMVSourceClassification.hasTypeIVHorizontalSections_of_centeredIntervals_of_measure_eq
#print axioms SatisfiesRegularSnell.toClosedGeometry
#print axioms SatisfiesClosedSnell.toGeometry
#print axioms exteriorHalfAngle_eq_arccos_curvature
#print axioms toFourArcCandidate_satisfiesCMVTypeIVHypotheses
#print axioms centeredCarrier_eq_candidate_assembly
#print axioms horizontallyCongruent_candidate
#print axioms almostEverywhereHorizontallyCongruent_candidate_of_ae
#print axioms toFourArcCandidate_eq_endpoint_of_sourceRadius_eq_one
#print axioms toFourArcCandidate_eq_regular_toCandidate
#print axioms exists_typeThree_source_competitor_lt
#print axioms profile_not_isMinimizer
#print axioms sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
#print axioms sourceCarrier_not_isMinimizer_of_horizontalCongruence

open CMVRelaxation.FourArcSourceCompetitor

/-- Compiled zero-defect contract on the literal closed-curvature candidate. -/
example :
    2 * Real.cos (FourArcCandidate.endpoint (lam := 2) (by norm_num)).alpha -
          (FourArcCandidate.endpoint (lam := 2) (by norm_num)).h = 0 ∧
      ¬ (relaxedSourceSemantics 2).IsMinimizer
        (FourArcCandidate.endpoint (lam := 2) (by norm_num)).assembly.carrier := by
  constructor
  · have hincidence :=
      (FourArcCandidate.endpoint_satisfiesCMVTypeIVHypotheses
        (lam := 2) (by norm_num)).snell_incidence
    linarith
  · exact endpointCarrier_not_isMinimizer (lam := 2) (by norm_num)

/-- Compiled positive-defect contract on an original interior candidate. -/
example :
    0 < 2 * Real.cos (interiorDefectSpecimen 2).alpha -
          (interiorDefectSpecimen 2).h ∧
      ¬ (relaxedSourceSemantics 2).IsMinimizer
        (interiorDefectSpecimen 2).assembly.carrier :=
  ⟨interiorDefectSpecimen_positive,
    candidateCarrier_not_isMinimizer (interiorDefectSpecimen 2) (by norm_num)⟩

/-- Compiled negative-defect contract on an original interior candidate. -/
example :
    (6 / 5 : ℝ) * Real.cos (interiorDefectSpecimen (6 / 5)).alpha -
          (interiorDefectSpecimen (6 / 5)).h < 0 ∧
      ¬ (relaxedSourceSemantics (6 / 5)).IsMinimizer
        (interiorDefectSpecimen (6 / 5)).assembly.carrier :=
  ⟨interiorDefectSpecimen_negative,
    candidateCarrier_not_isMinimizer
      (interiorDefectSpecimen (6 / 5)) (by norm_num)⟩

/-- Compiled positive-defect contract on an original `h = 1` candidate. -/
example :
    0 < 3 * Real.cos (FourArcCandidate.chordDefectSpecimen 3).alpha -
          (FourArcCandidate.chordDefectSpecimen 3).h ∧
      ¬ (relaxedSourceSemantics 3).IsMinimizer
        (FourArcCandidate.chordDefectSpecimen 3).assembly.carrier :=
  ⟨FourArcCandidate.chordDefectSpecimen_positive,
    candidateCarrier_not_isMinimizer
      (FourArcCandidate.chordDefectSpecimen 3) (by norm_num)⟩

/-- Compiled negative-defect contract on an original `h = 1` candidate. -/
example :
    (3 / 2 : ℝ) *
          Real.cos (FourArcCandidate.chordDefectSpecimen (3 / 2)).alpha -
          (FourArcCandidate.chordDefectSpecimen (3 / 2)).h < 0 ∧
      ¬ (relaxedSourceSemantics (3 / 2)).IsMinimizer
        (FourArcCandidate.chordDefectSpecimen (3 / 2)).assembly.carrier :=
  ⟨FourArcCandidate.chordDefectSpecimen_negative,
    candidateCarrier_not_isMinimizer
      (FourArcCandidate.chordDefectSpecimen (3 / 2)) (by norm_num)⟩

/-- The nonzero-defect path still exposes an actual strict-curvature recovered
assembly, rather than only a scalar comparison. -/
example :
    ∃ a : FourArcAssembly,
      a.core.curvature < 1 ∧
      (relaxedSourceSemantics 3).IsAdmissible a.carrier ∧
      _root_.WeightedArea 3 a.carrier =
        _root_.WeightedArea 3
          (FourArcCandidate.chordDefectSpecimen 3).assembly.carrier ∧
      relaxedPerimeter 3 a.carrier <
        relaxedPerimeter 3
          (FourArcCandidate.chordDefectSpecimen 3).assembly.carrier :=
  endpointDefectSpecimen_positive_source_competitor

/-- Exact-horizontal transport requires only density and representative
geometry. -/
example {sourceCarrier : Set PlanePoint}
    (hcongruent : HorizontallyCongruent sourceCarrier
      (interiorDefectSpecimen 2).assembly.carrier) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_horizontalCongruence_candidate
    (interiorDefectSpecimen 2) (by norm_num) hcongruent

/-- Almost-everywhere transport has the same contact-law-free contract. -/
example {sourceCarrier : Set PlanePoint}
    (hcongruent : AlmostEverywhereHorizontallyCongruent sourceCarrier
      (interiorDefectSpecimen 2).assembly.carrier) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
    (interiorDefectSpecimen 2) (by norm_num) hcongruent

/-- Raw-coordinate exclusion exposes only density and the closed geometric
domain; no Snell/contact premise is present. -/
example (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hgeometry : raw.SatisfiesClosedGeometry) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer raw.carrier :=
  rawFourArcCarrier_not_isMinimizer raw (by norm_num) hgeometry

/-- Raw-coordinate almost-everywhere transport likewise adds only the actual
representative relation. -/
example (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hgeometry : raw.SatisfiesClosedGeometry)
    {sourceCarrier : Set PlanePoint}
    (hsource : sourceCarrier =ᵐ[MeasureTheory.volume] raw.carrier) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_ae_rawFourArcCoordinates
    raw (by norm_num) hgeometry hsource

/-- Sectionwise classification exposes only closed geometry and slice equality
at the direct all-density consumer. -/
example (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hgeometry : raw.SatisfiesClosedGeometry)
    {sourceCarrier : Set PlanePoint}
    (hsections :
      CMVSourceClassification.HasTypeIVHorizontalSections sourceCarrier raw) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_horizontalSections
    raw (by norm_num) hgeometry hsections

/-- The centered-interval equality-case interface also includes the literal
radius-one endpoint without a contact-law premise in the consumer. -/
example {sourceCarrier : Set PlanePoint}
    (hsource :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections
        CMVFigureFour.Examples.endpointRaw.horizontalPlacement sourceCarrier)
    (hmeasure : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      MeasureTheory.volume
          (CMVSourceClassification.horizontalSection sourceCarrier y) =
        MeasureTheory.volume
          (CMVSourceClassification.horizontalSection
            CMVFigureFour.Examples.endpointRaw.carrier y)) :
    ¬ (relaxedSourceSemantics 2).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_centeredIntervals_of_measure_eq
    CMVFigureFour.Examples.endpointRaw (by norm_num)
      CMVFigureFour.Examples.endpointRaw_satisfiesClosedSnell.toGeometry
      hsource hmeasure

/-- The raw centered-section theorem itself evaluates at `sourceRadius = 1`. -/
example :
    CMVSourceClassification.HasCenteredHorizontalIntervalSections
      CMVFigureFour.Examples.endpointRaw.horizontalPlacement
      CMVFigureFour.Examples.endpointRaw.carrier :=
  CMVFigureFour.Examples.endpointRaw.hasCenteredHorizontalIntervalSections
    CMVFigureFour.Examples.endpointRaw_satisfiesClosedSnell.toGeometry

end CMVRelaxation.TypeThreeSourceExclusion
