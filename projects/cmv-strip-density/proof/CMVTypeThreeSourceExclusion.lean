/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTypeThreeSharpRecovery
import CMVProfileSourceSemantics
import CMVSourceSectionClassification
import CMVFourArcSourceCompetitor

/-!
# Direct source exclusion by recovered competitors

The universal scalar equal-area witness remains available on the zero-defect
branch. Exact-area chord variation handles either nonzero defect. Both
routes produce an actual source-admissible competitor with strictly smaller
extended relaxed perimeter for every literal four-arc candidate, including
`h = 1`.  Source minimality supplies the only required candidate finiteness
inside the contradiction.  No contact law, arbitrary-competitor coverage, or
`CompatibleWithModel` premise is used by the universal consumer.
-/

noncomputable section

namespace CMVRelaxation.TypeThreeSourceExclusion

/-- Every geometric type-(iv) candidate satisfying the source incidence law
has an actual source-admissible type-(iii) carrier with the same weighted area
and strictly smaller literal complete-frontier perimeter.  The statement
includes the closed-curvature endpoint `h = 1`. -/
theorem exists_typeThree_source_competitor_frontier_lt
    {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ∃ a : TypeThreeAssembly lam,
      (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam candidate.assembly.carrier ∧
      a.WeightedPerimeter <
        _root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier) := by
  rcases
      LeanSuffixAnalytic.stationaryEqualAreaPair_strictImprovement_exists
        hcandidate.density_jump with
    ⟨pair, hfoldThree, hperimeter, -⟩
  rcases pair.allCurvature_typeThreeImprovement
      hcandidate.density_jump hfoldThree hperimeter
      candidate.h_pos candidate.h_le_one with
    ⟨h₃, hh₃, hh₃_one, hequalArea, hstrictPerimeter⟩
  let a : TypeThreeAssembly lam :=
    { h := h₃
      density_jump := hcandidate.density_jump
      h_pos := hh₃
      h_lt_one := hh₃_one }
  refine ⟨a, TypeThreeRecovery.isAdmissible_typeThree a, ?_, ?_⟩
  · calc
      _root_.WeightedArea lam a.carrier =
          LeanSuffixAnalytic.typeThreeArea lam h₃ := by
        change a.WeightedArea = _
        rw [a.weightedArea_formula,
          CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea]
      _ = LeanSuffixAnalytic.typeFourArea lam candidate.h := hequalArea
      _ = candidate.WeightedArea :=
        (CMVSuffixModel.FourArcCandidate.weightedArea_eq_typeFourArea
          candidate hcandidate).symm
      _ = _root_.WeightedArea lam candidate.assembly.carrier := by
        simpa only [FourArcCandidate.WeightedArea, FourArcCandidate.region,
          AdmissibleCompetitor.carrier] using
          candidate.region.weightedArea_eq_carrier
  · calc
      a.WeightedPerimeter = a.scalarWeightedPerimeter :=
        a.weightedPerimeter_formula
      _ = LeanSuffixAnalytic.typeThreePerimeter lam h₃ :=
        CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter a
      _ < LeanSuffixAnalytic.typeFourPerimeter lam candidate.h :=
        hstrictPerimeter
      _ = candidate.WeightedPerimeter :=
        (CMVSuffixModel.FourArcCandidate.weightedPerimeter_eq_typeFourPerimeter
          candidate hcandidate).symm
      _ = _root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier) := rfl

/-- The recovered type-(iii) carrier is strictly cheaper in the extended
relaxation.  No finiteness or recovery hypothesis is imposed on the type-(iv)
carrier: the candidate-level projection lower bound supplies the last step. -/
theorem exists_typeThree_source_competitor_relaxedPerimeter_lt
    {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ∃ a : TypeThreeAssembly lam,
      (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam candidate.assembly.carrier ∧
      relaxedPerimeter lam a.carrier <
        relaxedPerimeter lam candidate.assembly.carrier := by
  rcases exists_typeThree_source_competitor_frontier_lt
      candidate hcandidate with ⟨a, hadmissible, hequalArea, hfrontier⟩
  have hcandidatePerimeterPos :
      0 < _root_.WeightedPerimeter lam
        (FrontierMeasure candidate.assembly.carrier) :=
    lt_of_le_of_lt
      (TypeThreeRecovery.assemblyWeightedPerimeter_nonneg a) hfrontier
  refine ⟨a, hadmissible, hequalArea, ?_⟩
  calc
    relaxedPerimeter lam a.carrier ≤ ENNReal.ofReal a.WeightedPerimeter :=
      TypeThreeRecovery.relaxedPerimeter_le_frontierCost_typeThree a
    _ < ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) :=
      (ENNReal.ofReal_lt_ofReal_iff hcandidatePerimeterPos).2 hfrontier
    _ ≤ relaxedPerimeter lam candidate.assembly.carrier :=
      CandidateFourArc.frontierCost_le_relaxedPerimeter
        candidate hcandidate.density_jump

/-- Every literal four-arc candidate at an admissible density has an actual
source-admissible equal-area competitor with strictly smaller extended relaxed
perimeter. A zero signed chord defect uses the stronger recovered type-(iii)
witness; either nonzero sign uses exact-area chord variation. -/
theorem exists_source_competitor_relaxedPerimeter_lt
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam) :
    ∃ competitor : Set PlanePoint,
      (relaxedSourceSemantics lam).IsAdmissible competitor ∧
      _root_.WeightedArea lam competitor =
        _root_.WeightedArea lam candidate.assembly.carrier ∧
      relaxedPerimeter lam competitor <
        relaxedPerimeter lam candidate.assembly.carrier := by
  by_cases hdefect : lam * Real.cos candidate.alpha - candidate.h = 0
  · have hincidence :
        lam * Real.cos candidate.alpha = candidate.h :=
      sub_eq_zero.mp hdefect
    rcases exists_typeThree_source_competitor_relaxedPerimeter_lt
        candidate ⟨hlam, hincidence⟩ with
      ⟨a, hadmissible, hequalArea, hstrict⟩
    exact ⟨a.carrier, hadmissible, hequalArea, hstrict⟩
  · rcases
        FourArcSourceCompetitor.exists_source_competitor_relaxedPerimeter_lt_of_defect
          candidate hlam hdefect with
      ⟨a, -, hadmissible, hequalArea, hstrict⟩
    exact ⟨a.carrier, hadmissible, hequalArea, hstrict⟩

/-- No literal four-arc candidate can minimize the relaxed source perimeter at
an admissible density.  Candidate finiteness is obtained only inside the
contradiction from the alleged source minimizer. -/
theorem candidateCarrier_not_isMinimizer
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer
      candidate.assembly.carrier := by
  intro hmin
  rcases exists_source_competitor_relaxedPerimeter_lt candidate hlam with
    ⟨competitor, hadmissible, hequalArea, hstrict⟩
  have hsourceLe :=
    hmin.2 competitor hadmissible hequalArea
  have hextendedLe :
      relaxedPerimeter lam candidate.assembly.carrier ≤
        relaxedPerimeter lam competitor :=
    (relaxedSourceSemantics_perimeter_le_iff
      hmin.1.1 hadmissible.1).1 hsourceLe
  exact (not_lt_of_ge hextendedLe) hstrict

/-- Candidate exclusion transports through an almost-everywhere horizontal
placement without first proving source admissibility of the candidate
representative. The alleged minimizer supplies finiteness only for the actual
source representative; extended perimeter invariance closes the contradiction. -/
theorem sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam)
    {sourceCarrier : Set PlanePoint}
    (hcongruent : AlmostEverywhereHorizontallyCongruent sourceCarrier
      candidate.assembly.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  rcases exists_source_competitor_relaxedPerimeter_lt candidate hlam with
    ⟨competitor, hadmissible, hequalArea, hstrict⟩
  rcases hcongruent with ⟨t, hsource⟩
  have htargetArea :
      _root_.WeightedArea lam candidate.assembly.carrier =
        _root_.WeightedArea lam sourceCarrier := by
    calc
      _root_.WeightedArea lam candidate.assembly.carrier =
          _root_.WeightedArea lam
            (horizontalTranslation t '' candidate.assembly.carrier) :=
        (weightedArea_horizontalTranslation lam t
          candidate.assembly.carrier).symm
      _ = _root_.WeightedArea lam sourceCarrier :=
        (weightedArea_congr_ae lam hsource).symm
  have hsourceLeReal :=
    hmin.2 competitor hadmissible (hequalArea.trans htargetArea)
  have hsourceLe :
      relaxedPerimeter lam sourceCarrier ≤ relaxedPerimeter lam competitor :=
    (relaxedSourceSemantics_perimeter_le_iff
      hmin.1.1 hadmissible.1).1 hsourceLeReal
  have htargetPerimeter :
      relaxedPerimeter lam candidate.assembly.carrier =
        relaxedPerimeter lam sourceCarrier := by
    calc
      relaxedPerimeter lam candidate.assembly.carrier =
          relaxedPerimeter lam
            (horizontalTranslation t '' candidate.assembly.carrier) :=
        (relaxedPerimeter_horizontalTranslation lam t
          candidate.assembly.carrier).symm
      _ = relaxedPerimeter lam sourceCarrier :=
        (relaxedPerimeter_congr_ae lam hsource).symm
  exact (not_lt_of_ge (htargetPerimeter.trans_le hsourceLe)) hstrict

/-- Exact horizontal placement is the literal-set specialization of the
candidate representative exclusion. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalCongruence_candidate
    {lam : ℝ} (candidate : FourArcCandidate lam) (hlam : 1 < lam)
    {sourceCarrier : Set PlanePoint}
    (hcongruent : HorizontallyCongruent sourceCarrier
      candidate.assembly.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
    candidate hlam
      (almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
        hcongruent)

/-- The literal closed-curvature `h = 1` source carrier is not minimizing at
any density `lambda > 1`, without a supplied finiteness, recovery, comparison,
contact law, compatibility, or arbitrary-model-coverage premise. -/
theorem endpointCarrier_not_isMinimizer
    {lam : ℝ} (hlam : 1 < lam) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer
      (FourArcCandidate.endpoint hlam).assembly.carrier :=
  candidateCarrier_not_isMinimizer (FourArcCandidate.endpoint hlam) hlam

/-- Every almost-everywhere horizontal representative of the literal endpoint
carrier is excluded, without endpoint recovery or caller-supplied finiteness. -/
theorem endpointSourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
    {lam : ℝ} (hlam : 1 < lam) {sourceCarrier : Set PlanePoint}
    (hcongruent : AlmostEverywhereHorizontallyCongruent sourceCarrier
      (FourArcCandidate.endpoint hlam).assembly.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
    (FourArcCandidate.endpoint hlam) hlam hcongruent

/-- Exact horizontal endpoint representatives satisfy the same direct
source-minimality exclusion. -/
theorem endpointSourceCarrier_not_isMinimizer_of_horizontalCongruence
    {lam : ℝ} (hlam : 1 < lam) {sourceCarrier : Set PlanePoint}
    (hcongruent : HorizontallyCongruent sourceCarrier
      (FourArcCandidate.endpoint hlam).assembly.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  endpointSourceCarrier_not_isMinimizer_of_aeHorizontalCongruence hlam
    (almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
      hcongruent)

/-- A raw source-coordinate carrier in the closed geometric domain is excluded
at every admissible density.  Radius, angle, and horizontal placement are the
only raw-coordinate inputs; no contact law is assumed. -/
theorem rawFourArcCarrier_not_isMinimizer
    {lam : ℝ} (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hlam : 1 < lam) (hgeometry : raw.SatisfiesClosedGeometry) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer raw.carrier :=
  sourceCarrier_not_isMinimizer_of_horizontalCongruence_candidate
    (raw.toFourArcCandidate (lam := lam) hgeometry) hlam
    (raw.horizontallyCongruent_candidate hgeometry)

/-- Almost-everywhere source representatives of any raw closed-geometric
carrier feed the same contact-law-free direct exclusion. -/
theorem sourceCarrier_not_isMinimizer_of_ae_rawFourArcCoordinates
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hlam : 1 < lam) (hgeometry : raw.SatisfiesClosedGeometry)
    (hsource : sourceCarrier =ᵐ[MeasureTheory.volume] raw.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_candidate
    (raw.toFourArcCandidate (lam := lam) hgeometry) hlam
    (raw.almostEverywhereHorizontallyCongruent_candidate_of_ae
      hgeometry hsource)

/-- Sectionwise classification is sufficient for the same all-density source
exclusion.  Null measurability is obtained from the alleged minimizer, so the
caller supplies only closed raw geometry and almost-everywhere slice equality.
This includes the radius-one endpoint and uses no contact law or compatibility
premise. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalSections
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hlam : 1 < lam) (hgeometry : raw.SatisfiesClosedGeometry)
    (hsections :
      CMVSourceClassification.HasTypeIVHorizontalSections sourceCarrier raw) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  exact
    (sourceCarrier_not_isMinimizer_of_ae_rawFourArcCoordinates
      raw hlam hgeometry
        (CMVSourceClassification.sourceCarrier_ae_rawCarrier_of_horizontalSections
          raw hmin.1.1.1 hsections)) hmin

/-- CMV's centered-interval equality-case output and slice
equimeasurability feed the contact-law-free direct exclusion without first
assuming planar almost-everywhere equality.  The raw interval theorem is valid
on the full closed geometric domain `sourceRadius ≥ 1`. -/
theorem sourceCarrier_not_isMinimizer_of_centeredIntervals_of_measure_eq
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hlam : 1 < lam) (hgeometry : raw.SatisfiesClosedGeometry)
    (hsource :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections
        raw.horizontalPlacement sourceCarrier)
    (hmeasure : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      MeasureTheory.volume
          (CMVSourceClassification.horizontalSection sourceCarrier y) =
        MeasureTheory.volume
          (CMVSourceClassification.horizontalSection raw.carrier y)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_horizontalSections raw hlam hgeometry
    (CMVSourceClassification.hasTypeIVHorizontalSections_of_centeredIntervals_of_measure_eq
      raw hgeometry hsource hmeasure)

/-- Every canonical type-(iv) profile has an actual source-admissible,
equal-area type-(iii) carrier with strictly smaller relaxed source perimeter. -/
theorem exists_typeThree_source_competitor_lt
    {lam : ℝ} (profile : CanonicalTypeIVProfile lam) :
    ∃ a : TypeThreeAssembly lam,
      (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam profile.carrier ∧
      (relaxedSourceSemantics lam).perimeter a.carrier <
        (relaxedSourceSemantics lam).perimeter profile.carrier := by
  rcases exists_typeThree_source_competitor_frontier_lt
      profile.toCandidate
      profile.toCandidate_satisfiesCMVTypeIVHypotheses with
    ⟨a, hadmissible, hequalArea, hfrontier⟩
  refine ⟨a, hadmissible, ?_, ?_⟩
  · simpa only [profile.carrier_eq_candidate_assembly] using hequalArea
  · calc
      (relaxedSourceSemantics lam).perimeter a.carrier ≤
          a.WeightedPerimeter :=
        TypeThreeRecovery.typeThree_perimeter_le_frontier a
      _ < _root_.WeightedPerimeter lam
          (FrontierMeasure profile.toCandidate.assembly.carrier) :=
        hfrontier
      _ = _root_.WeightedPerimeter lam
          (FrontierMeasure profile.carrier) := by
        rw [profile.carrier_eq_candidate_assembly]
      _ = (relaxedSourceSemantics lam).perimeter profile.carrier :=
        (ProfileSourceSemantics.profile_perimeter_eq_frontier profile).symm

/-- A canonical regular type-(iv) source carrier is never a minimizer at any
admissible density.  The contradiction uses one actual type-(iii) source
competitor rather than arbitrary modeled-competitor coverage. -/
theorem profile_not_isMinimizer
    {lam : ℝ} (profile : CanonicalTypeIVProfile lam) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer profile.carrier := by
  intro hmin
  rcases exists_typeThree_source_competitor_lt profile with
    ⟨a, hadmissible, hequalArea, hstrict⟩
  exact (not_lt_of_ge (hmin.2 a.carrier hadmissible hequalArea)) hstrict

/-- Almost-everywhere horizontal classification transports source minimality
to the canonical representative and is therefore directly excluded, with no
compatibility or recovery premise supplied by the caller. -/
theorem sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
    {lam : ℝ} (profile : CanonicalTypeIVProfile lam)
    {sourceCarrier : Set PlanePoint}
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent sourceCarrier profile.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  have hnormalization :=
    relaxedSourceSemantics_normalizationWitness_of_almostEverywhereHorizontalCongruence
      profile hmin.1 hcongruent
  have hprofile :
      (relaxedSourceSemantics lam).IsMinimizer profile.carrier :=
    (relaxedSourceSemantics lam).isMinimizer_of_normalizationWitness
      hmin hnormalization
  exact profile_not_isMinimizer profile hprofile

/-- Exact horizontal classification is the literal-set specialization of the
almost-everywhere direct source exclusion. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalCongruence
    {lam : ℝ} (profile : CanonicalTypeIVProfile lam)
    {sourceCarrier : Set PlanePoint}
    (hcongruent : HorizontallyCongruent sourceCarrier profile.carrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence profile
    (almostEverywhereHorizontallyCongruent_of_horizontallyCongruent hcongruent)

end CMVRelaxation.TypeThreeSourceExclusion
