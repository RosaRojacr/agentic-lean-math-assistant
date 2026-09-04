/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FourArcCandidate

/-!
# CMV source-profile normalization bridge

This module separates two issues which the source treats with different boundary
semantics.  `CanonicalTypeIVProfile` is the raw closed coordinate carrier from
CMV's regular type-(iv) formulas (`lambda > 1`, `0 < h < 1`).  Its normalization
to `FourArcCandidate` is proved as an equality of sets, so the model's weighted
area and complete-frontier weighted perimeter follow from the carrier itself.
Conversely, every regular `FourArcCandidate` satisfying the CMV source laws
recovers a canonical source profile, and normalization returns the original
candidate exactly.  The image characterization keeps the excluded `h = 1`
endpoint explicit.


`SourcePerimeterSemantics` keeps the source's relaxed/reduced-boundary perimeter
abstract.  The transfer theorem states exactly the two remaining compatibility
facts needed to move source minimality into the complete-frontier model; it does
not identify those boundary notions by definition.
-/

open Set
open Real
open MeasureTheory

noncomputable section

/-- Horizontal translation through the Euclidean realization used by
`FrontierMeasure`.  This is the placement freedom left by the source's
classification up to density-preserving isometries. -/
noncomputable def horizontalTranslation (t : ℝ) :
    PlanePoint ≃ₜ PlanePoint :=
  planeEuclideanHomeomorph.trans
    ((IsometryEquiv.addLeft (WithLp.toLp 2 (t, 0))).toHomeomorph.trans
      planeEuclideanHomeomorph.symm)

@[simp] theorem horizontalTranslation_apply (t : ℝ) (p : PlanePoint) :
    horizontalTranslation t p = (p.1 + t, p.2) := by
  change WithLp.ofLp
      (WithLp.toLp 2 (t, 0) + WithLp.toLp 2 p) = (p.1 + t, p.2)
  rw [← WithLp.toLp_add]
  ext <;> simp [add_comm]

@[simp] theorem stripDensity_horizontalTranslation
    (lam t : ℝ) (p : PlanePoint) :
    StripDensity lam (horizontalTranslation t p) = StripDensity lam p := by
  simp [StripDensity]

/-- Horizontal translation preserves planar Lebesgue measure. -/
theorem measurePreserving_horizontalTranslation (t : ℝ) :
    MeasurePreserving (horizontalTranslation t)
      (volume : Measure PlanePoint) volume := by
  have hfun :
      (horizontalTranslation t : PlanePoint → PlanePoint) =
        Prod.map (fun x : ℝ ↦ x + t) id := by
    funext p
    exact horizontalTranslation_apply t p
  rw [Measure.volume_eq_prod, hfun]
  exact (measurePreserving_add_right (volume : Measure ℝ) t).prod
    (MeasurePreserving.id (volume : Measure ℝ))

/-- Weighted area is invariant under every horizontal placement, without
measurability or integrability side conditions on the carrier. -/
theorem weightedArea_horizontalTranslation (lam t : ℝ)
    (carrier : Set PlanePoint) :
    _root_.WeightedArea lam (horizontalTranslation t '' carrier) =
      _root_.WeightedArea lam carrier := by
  simp only [_root_.WeightedArea]
  simpa only [stripDensity_horizontalTranslation] using
    (measurePreserving_horizontalTranslation t).setIntegral_image_emb
      (horizontalTranslation t).measurableEmbedding (StripDensity lam) carrier

private theorem euclidean_image_horizontalTranslation (t : ℝ)
    (carrier : Set PlanePoint) :
    planeEuclideanHomeomorph '' (horizontalTranslation t '' carrier) =
      IsometryEquiv.addLeft (WithLp.toLp 2 (t, 0)) ''
        (planeEuclideanHomeomorph '' carrier) := by
  rw [Set.image_image, Set.image_image]
  rfl

private theorem hausdorff_restrict_isometry_image
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (s : Set EuclideanPlane) :
    (μH[1] : Measure EuclideanPlane).restrict (e '' s) =
      Measure.map e ((μH[1] : Measure EuclideanPlane).restrict s) := by
  calc
    (μH[1] : Measure EuclideanPlane).restrict (e '' s) =
        (Measure.map e (μH[1] : Measure EuclideanPlane)).restrict (e '' s) :=
      congrArg (fun μ : Measure EuclideanPlane => μ.restrict (e '' s))
        (e.map_hausdorffMeasure 1).symm
    _ = Measure.map e
        ((μH[1] : Measure EuclideanPlane).restrict (e ⁻¹' (e '' s))) := by
      simpa only [Homeomorph.toMeasurableEquiv_coe,
        IsometryEquiv.coe_toHomeomorph] using
          e.toHomeomorph.toMeasurableEquiv.restrict_map
            (μH[1] : Measure EuclideanPlane) (e '' s)
    _ = Measure.map e ((μH[1] : Measure EuclideanPlane).restrict s) := by
      rw [e.injective.preimage_image]

/-- The complete-frontier measure of a translated carrier is the pushforward
of the original complete-frontier measure. -/
theorem frontierMeasure_horizontalTranslation (t : ℝ)
    (carrier : Set PlanePoint) :
    FrontierMeasure (horizontalTranslation t '' carrier) =
      Measure.map (horizontalTranslation t) (FrontierMeasure carrier) := by
  let e : EuclideanPlane ≃ᵢ EuclideanPlane :=
    IsometryEquiv.addLeft (WithLp.toLp 2 (t, 0))
  have himage :
      planeEuclideanHomeomorph '' (horizontalTranslation t '' carrier) =
        e '' (planeEuclideanHomeomorph '' carrier) :=
    euclidean_image_horizontalTranslation t carrier
  have hfrontier :
      frontier (planeEuclideanHomeomorph ''
          (horizontalTranslation t '' carrier)) =
        e '' frontier (planeEuclideanHomeomorph '' carrier) := by
    rw [himage]
    simpa using (e.toHomeomorph.image_frontier
      (planeEuclideanHomeomorph '' carrier)).symm
  simp only [FrontierMeasure]
  rw [hfrontier,
    hausdorff_restrict_isometry_image e,
    Measure.map_map planeEuclideanHomeomorph.symm.measurable
      e.continuous.measurable,
    Measure.map_map (horizontalTranslation t).measurable
      planeEuclideanHomeomorph.symm.measurable]
  congr 1

/-- Complete-frontier weighted perimeter is invariant under every horizontal
placement. -/
theorem frontierWeightedPerimeter_horizontalTranslation (lam t : ℝ)
    (carrier : Set PlanePoint) :
    _root_.WeightedPerimeter lam
        (FrontierMeasure (horizontalTranslation t '' carrier)) =
      _root_.WeightedPerimeter lam (FrontierMeasure carrier) := by
  rw [frontierMeasure_horizontalTranslation, _root_.WeightedPerimeter,
    (horizontalTranslation t).measurableEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [] with p
  exact stripDensity_horizontalTranslation lam t p

/-- Two carriers differing only by a horizontal placement. -/
def HorizontallyCongruent
    (sourceCarrier canonicalCarrier : Set PlanePoint) : Prop :=
  ∃ t : ℝ, sourceCarrier = horizontalTranslation t '' canonicalCarrier

theorem weightedArea_eq_of_horizontallyCongruent
    {lam : ℝ} {sourceCarrier canonicalCarrier : Set PlanePoint}
    (hcongruent :
      HorizontallyCongruent sourceCarrier canonicalCarrier) :
    _root_.WeightedArea lam sourceCarrier =
      _root_.WeightedArea lam canonicalCarrier := by
  rcases hcongruent with ⟨t, rfl⟩
  exact weightedArea_horizontalTranslation lam t canonicalCarrier

theorem frontierWeightedPerimeter_eq_of_horizontallyCongruent
    {lam : ℝ} {sourceCarrier canonicalCarrier : Set PlanePoint}
    (hcongruent :
      HorizontallyCongruent sourceCarrier canonicalCarrier) :
    _root_.WeightedPerimeter lam (FrontierMeasure sourceCarrier) =
      _root_.WeightedPerimeter lam (FrontierMeasure canonicalCarrier) := by
  rcases hcongruent with ⟨t, rfl⟩
  exact frontierWeightedPerimeter_horizontalTranslation
    lam t canonicalCarrier


/-- Raw regular CMV type-(iv) parameters.  The scalar closure `h = 1` belongs to
the broader model, but not to this source-regular profile. -/
structure CanonicalTypeIVProfile (lam : ℝ) where
  h : ℝ
  density_jump : 1 < lam
  h_pos : 0 < h
  h_lt_one : h < 1

namespace CanonicalTypeIVProfile

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

/-- Common source radius `R = 1 / h`. -/
def radius : ℝ := 1 / profile.h

/-- Source exterior half-angle `a₄ = arccos (h / lambda)`. -/
def alpha : ℝ := arccos (profile.h / lam)

/-- The source quantity `sin b₄ = sqrt (1 - h²)`. -/
def innerRadial : ℝ := √(1 - profile.h ^ 2)

/-- Half-width of both interface chords. -/
def outerHalfWidth : ℝ := profile.radius * sin profile.alpha

/-- Horizontal displacement of either strip-side circle center. -/
def sideCenterOffset : ℝ :=
  profile.radius * (sin profile.alpha - profile.innerRadial)

/-- Left strip-side circle center. -/
def leftCenter : PlanePoint := (-profile.sideCenterOffset, 0)

/-- Right strip-side circle center. -/
def rightCenter : PlanePoint := (profile.sideCenterOffset, 0)

/-- Upper exterior circle center. -/
def upperCenter : PlanePoint :=
  (0, 1 - profile.radius * cos profile.alpha)

/-- Lower exterior circle center. -/
def lowerCenter : PlanePoint :=
  (0, -1 + profile.radius * cos profile.alpha)

/-- Raw central rectangle from the audited source coordinates. -/
def rectangleCarrier : Set PlanePoint :=
  {p | -profile.outerHalfWidth ≤ p.1 ∧
    p.1 ≤ profile.outerHalfWidth ∧ |p.2| ≤ 1}

/-- Raw left strip-side circular segment. -/
def leftSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - profile.leftCenter.1) ^ 2 +
      (p.2 - profile.leftCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧
    p.1 ≤ -profile.outerHalfWidth ∧ |p.2| ≤ 1}

/-- Raw right strip-side circular segment. -/
def rightSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - profile.rightCenter.1) ^ 2 +
      (p.2 - profile.rightCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧
    profile.outerHalfWidth ≤ p.1 ∧ |p.2| ≤ 1}

/-- Raw upper exterior circular cap. -/
def upperCapCarrier : Set PlanePoint :=
  {p | (p.1 - profile.upperCenter.1) ^ 2 +
      (p.2 - profile.upperCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧
    1 ≤ p.2}

/-- Raw lower exterior circular cap. -/
def lowerCapCarrier : Set PlanePoint :=
  {p | (p.1 - profile.lowerCenter.1) ^ 2 +
      (p.2 - profile.lowerCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧
    p.2 ≤ -1}

/-- The independent raw source-coordinate carrier `E₄`. -/
def carrier : Set PlanePoint :=
  ((profile.rectangleCarrier ∪ profile.leftSegmentCarrier ∪
      profile.rightSegmentCarrier) ∪ profile.upperCapCarrier) ∪
    profile.lowerCapCarrier

private theorem lam_pos (profile : CanonicalTypeIVProfile lam) : 0 < lam :=
  lt_trans zero_lt_one profile.density_jump

private theorem ratio_pos (profile : CanonicalTypeIVProfile lam) :
    0 < profile.h / lam :=
  div_pos profile.h_pos profile.lam_pos

private theorem ratio_lt_one (profile : CanonicalTypeIVProfile lam) :
    profile.h / lam < 1 :=
  (div_lt_one profile.lam_pos).2
    (lt_trans profile.h_lt_one profile.density_jump)

/-- The canonical model candidate obtained from the source parameters. -/
def toCandidate : FourArcCandidate lam where
  h := profile.h
  alpha := profile.alpha
  h_pos := profile.h_pos
  h_le_one := profile.h_lt_one.le
  alpha_pos := Real.arccos_pos.mpr profile.ratio_lt_one
  alpha_lt_pi_div_two := Real.arccos_lt_pi_div_two.mpr profile.ratio_pos

@[simp] theorem toCandidate_h : profile.toCandidate.h = profile.h := rfl

@[simp] theorem toCandidate_alpha :
    profile.toCandidate.alpha = profile.alpha := rfl

/-- Source regularity remains strict after normalization. -/
theorem toCandidate_h_lt_one : profile.toCandidate.h < 1 :=
  profile.h_lt_one

/-- The normalized candidate satisfies the source density and incidence laws. -/
theorem toCandidate_satisfiesCMVTypeIVHypotheses :
    profile.toCandidate.SatisfiesCMVTypeIVHypotheses := by
  refine {
    density_jump := profile.density_jump
    snell_incidence := ?_ }
  rw [toCandidate_alpha, alpha,
    Real.cos_arccos (le_trans (by norm_num) profile.ratio_pos.le)
      profile.ratio_lt_one.le]
  field_simp [ne_of_gt profile.lam_pos]
  rfl

/-- Recover the canonical regular source profile from a regular modeled
four-arc candidate satisfying the CMV source laws. -/
def ofCandidate (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) : CanonicalTypeIVProfile lam where
  h := candidate.h
  density_jump := hcandidate.density_jump
  h_pos := candidate.h_pos
  h_lt_one := hregular

@[simp] theorem ofCandidate_h
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) :
    (ofCandidate candidate hcandidate hregular).h = candidate.h := rfl

/-- Normalizing a recovered regular source profile returns the original
modeled candidate, including its principal-branch exterior angle. -/
@[simp] theorem toCandidate_ofCandidate
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) :
    (ofCandidate candidate hcandidate hregular).toCandidate = candidate := by
  have halpha := candidate.alpha_eq_arccos hcandidate
  cases candidate
  simp_all [ofCandidate, toCandidate, alpha]

/-- Recovering a source profile after normalization returns the original
profile. -/
@[simp] theorem ofCandidate_toCandidate
    (profile : CanonicalTypeIVProfile lam) :
    ofCandidate profile.toCandidate
      profile.toCandidate_satisfiesCMVTypeIVHypotheses
      profile.toCandidate_h_lt_one = profile := by
  cases profile
  rfl

/-- The regular CMV source profiles map onto exactly the modeled candidates
that satisfy the source laws and have strict curvature below the endpoint. -/
theorem exists_toCandidate_eq_iff (candidate : FourArcCandidate lam) :
    (∃ profile : CanonicalTypeIVProfile lam,
      profile.toCandidate = candidate) ↔
      candidate.SatisfiesCMVTypeIVHypotheses ∧ candidate.h < 1 := by
  constructor
  · rintro ⟨profile, rfl⟩
    exact ⟨profile.toCandidate_satisfiesCMVTypeIVHypotheses,
      profile.toCandidate_h_lt_one⟩
  · rintro ⟨hcandidate, hregular⟩
    exact ⟨ofCandidate candidate hcandidate hregular,
      toCandidate_ofCandidate candidate hcandidate hregular⟩


private theorem candidate_chord_half :
    profile.toCandidate.stripCore.chord / 2 = profile.outerHalfWidth := by
  simp only [FourArcCandidate.stripCore, FourArcCandidate.capChord,
    toCandidate_h, toCandidate_alpha, outerHalfWidth, radius]
  field_simp [ne_of_gt profile.h_pos]

private theorem candidate_neg_chord_half :
    -profile.toCandidate.stripCore.chord / 2 =
      -profile.outerHalfWidth := by
  rw [show -profile.toCandidate.stripCore.chord / 2 =
    -(profile.toCandidate.stripCore.chord / 2) by ring,
    profile.candidate_chord_half]

private theorem candidate_core_radius :
    profile.toCandidate.stripCore.radius = profile.radius := by
  rfl

private theorem candidate_core_cos_sideAngle :
    cos profile.toCandidate.stripCore.sideAngle = profile.innerRadial := by
  rw [StripCore.cos_sideAngle]
  rfl

private theorem candidate_leftCenter :
    profile.toCandidate.stripCore.leftCenterX = profile.leftCenter.1 := by
  rw [StripCore.leftCenterX,
    show -profile.toCandidate.stripCore.chord / 2 =
      -(profile.toCandidate.stripCore.chord / 2) by ring,
    profile.candidate_chord_half, profile.candidate_core_radius,
    profile.candidate_core_cos_sideAngle]
  simp only [leftCenter, sideCenterOffset, outerHalfWidth]
  ring

private theorem candidate_rightCenter :
    profile.toCandidate.stripCore.rightCenterX = profile.rightCenter.1 := by
  rw [StripCore.rightCenterX, profile.candidate_chord_half,
    profile.candidate_core_radius, profile.candidate_core_cos_sideAngle]
  simp only [rightCenter, sideCenterOffset, outerHalfWidth]
  ring

private theorem candidate_upperCap_radius :
    profile.toCandidate.assembly.upperCap.radius = profile.radius := by
  rw [(profile.toCandidate.four_arcs_common_radius).1,
    profile.candidate_core_radius]

private theorem candidate_lowerCap_radius :
    profile.toCandidate.assembly.lowerCap.radius = profile.radius := by
  rw [(profile.toCandidate.four_arcs_common_radius).2,
    profile.candidate_core_radius]

private theorem candidate_upperCenter :
    profile.toCandidate.assembly.upperCap.center = profile.upperCenter := by
  change (0, 1 - profile.toCandidate.assembly.upperCap.radius *
    cos profile.alpha) = profile.upperCenter
  rw [profile.candidate_upperCap_radius]
  rfl

private theorem candidate_lowerCenter :
    profile.toCandidate.assembly.lowerCap.center = profile.lowerCenter := by
  change (0, -1 + profile.toCandidate.assembly.lowerCap.radius *
    cos profile.alpha) = profile.lowerCenter
  rw [profile.candidate_lowerCap_radius]
  rfl

private theorem candidate_rectangleCarrier :
    profile.toCandidate.stripCore.rectangleCarrier =
      profile.rectangleCarrier := by
  ext p
  simp only [StripCore.rectangleCarrier, rectangleCarrier, mem_ofPred_eq]
  rw [profile.candidate_chord_half, profile.candidate_neg_chord_half]

private theorem candidate_leftSegmentCarrier :
    profile.toCandidate.stripCore.leftCapCarrier =
      profile.leftSegmentCarrier := by
  ext p
  simp only [StripCore.leftCapCarrier, leftSegmentCarrier, mem_ofPred_eq]
  rw [profile.candidate_leftCenter, profile.candidate_core_radius,
    profile.candidate_neg_chord_half]
  simp only [leftCenter, sub_zero]

private theorem candidate_rightSegmentCarrier :
    profile.toCandidate.stripCore.rightCapCarrier =
      profile.rightSegmentCarrier := by
  ext p
  simp only [StripCore.rightCapCarrier, rightSegmentCarrier, mem_ofPred_eq]
  rw [profile.candidate_rightCenter, profile.candidate_core_radius,
    profile.candidate_chord_half]
  simp only [rightCenter, sub_zero]

private theorem candidate_upperCapCarrier :
    profile.toCandidate.assembly.upperCap.carrier =
      profile.upperCapCarrier := by
  ext p
  change (profile.toCandidate.assembly.upperCap.radiusSquaredAt p ≤
      profile.toCandidate.assembly.upperCap.radius ^ 2 ∧ 1 ≤ p.2) ↔
    ((p.1 - profile.upperCenter.1) ^ 2 +
        (p.2 - profile.upperCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧ 1 ≤ p.2)
  rw [OneSidedCircularCap.radiusSquaredAt,
    profile.candidate_upperCenter, profile.candidate_upperCap_radius]

private theorem candidate_lowerCapCarrier :
    profile.toCandidate.assembly.lowerCap.carrier =
      profile.lowerCapCarrier := by
  ext p
  change (profile.toCandidate.assembly.lowerCap.radiusSquaredAt p ≤
      profile.toCandidate.assembly.lowerCap.radius ^ 2 ∧ p.2 ≤ -1) ↔
    ((p.1 - profile.lowerCenter.1) ^ 2 +
        (p.2 - profile.lowerCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧ p.2 ≤ -1)
  rw [OneSidedCircularCap.radiusSquaredAt,
    profile.candidate_lowerCenter, profile.candidate_lowerCap_radius]

/-- The source-coordinate `E₄` carrier is exactly the model carrier, not merely
an object with matching scalar formulas. -/
theorem carrier_eq_candidate_assembly :
    profile.carrier = profile.toCandidate.assembly.carrier := by
  rw [FourArcAssembly.carrier, StripCore.carrier,
    FourArcCandidate.assembly_core,
    profile.candidate_rectangleCarrier,
    profile.candidate_leftSegmentCarrier,
    profile.candidate_rightSegmentCarrier,
    profile.candidate_upperCapCarrier,
    profile.candidate_lowerCapCarrier]
  rfl

/-- Exact weighted-area identification induced by the carrier equality. -/
theorem weightedArea_eq_candidate :
    _root_.WeightedArea lam profile.carrier =
      profile.toCandidate.WeightedArea := by
  change _root_.WeightedArea lam profile.carrier =
    _root_.WeightedArea lam profile.toCandidate.assembly.carrier
  rw [profile.carrier_eq_candidate_assembly]

/-- Exact complete-frontier weighted-perimeter identification induced by the
carrier equality. -/
theorem frontierWeightedPerimeter_eq_candidate :
    _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier) =
      profile.toCandidate.WeightedPerimeter := by
  change _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier) =
    _root_.WeightedPerimeter lam
      (FrontierMeasure profile.toCandidate.assembly.carrier)
  rw [profile.carrier_eq_candidate_assembly]


/-- The recovered source carrier is exactly the assembly carrier of the
arbitrary regular modeled candidate. -/
theorem ofCandidate_carrier_eq_candidate_assembly
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) :
    (ofCandidate candidate hcandidate hregular).carrier =
      candidate.assembly.carrier := by
  simpa using
    (ofCandidate candidate hcandidate hregular).carrier_eq_candidate_assembly

/-- The recovered source carrier has the arbitrary candidate's weighted area. -/
theorem ofCandidate_weightedArea_eq_candidate
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) :
    _root_.WeightedArea lam
      (ofCandidate candidate hcandidate hregular).carrier =
      candidate.WeightedArea := by
  simpa using
    (ofCandidate candidate hcandidate hregular).weightedArea_eq_candidate

/-- The recovered source carrier has the arbitrary candidate's complete-
frontier weighted perimeter. -/
theorem ofCandidate_frontierWeightedPerimeter_eq_candidate
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1) :
    _root_.WeightedPerimeter lam
      (FrontierMeasure
        (ofCandidate candidate hcandidate hregular).carrier) =
      candidate.WeightedPerimeter := by
  simpa using
    (ofCandidate candidate hcandidate hregular).frontierWeightedPerimeter_eq_candidate

/-- The normalized source carrier is a canonical finite-perimeter region. -/
def asFinitePerimeterRegion : FinitePerimeterRegion lam :=
  profile.toCandidate.region.toFinitePerimeterRegion

@[simp] theorem asFinitePerimeterRegion_carrier :
    profile.asFinitePerimeterRegion.carrier = profile.carrier := by
  rw [asFinitePerimeterRegion,
    AdmissibleCompetitor.toFinitePerimeterRegion_carrier]
  exact profile.carrier_eq_candidate_assembly.symm

end CanonicalTypeIVProfile


/-- Abstract source perimeter semantics.  In CMV this is the relaxed weighted
perimeter, equivalently the reduced-boundary integral on finite-perimeter sets;
it is intentionally not definitionally identified with `FrontierMeasure`. -/
structure SourcePerimeterSemantics (lam : ℝ) where
  IsFinitePerimeter : Set PlanePoint → Prop
  perimeter : Set PlanePoint → ℝ

namespace SourcePerimeterSemantics

variable {lam : ℝ} (source : SourcePerimeterSemantics lam)

/-- Source minimization among every source-finite equal-area carrier. -/
def IsMinimizer (carrier : Set PlanePoint) : Prop :=
  source.IsFinitePerimeter carrier ∧
    ∀ competitor : Set PlanePoint,
      source.IsFinitePerimeter competitor →
      _root_.WeightedArea lam competitor =
        _root_.WeightedArea lam carrier →
      source.perimeter carrier ≤ source.perimeter competitor

/-- Compatibility needed between source reduced-boundary semantics and the
modeled complete-frontier comparison class. -/
structure CompatibleWithModel (profile : CanonicalTypeIVProfile lam) : Prop where
  profile_perimeter_eq :
    source.perimeter profile.carrier =
      _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier)
  model_covered : ∀ competitor : AdmissibleCompetitor lam,
    source.IsFinitePerimeter competitor.carrier ∧
      source.perimeter competitor.carrier ≤ competitor.WeightedPerimeter

/-- A witness that an arbitrary source representative has been normalized to
the canonical closed `E₄` carrier without changing source area or perimeter. -/
structure NormalizationWitness (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam) : Prop where
  normalized_finite : source.IsFinitePerimeter profile.carrier
  weightedArea_eq :
    _root_.WeightedArea lam sourceCarrier =
      _root_.WeightedArea lam profile.carrier
  perimeter_eq :
    source.perimeter sourceCarrier = source.perimeter profile.carrier

/-- Horizontal congruence supplies area and complete-frontier perimeter
invariance.  The only remaining source-side premise is local agreement between
the source perimeter and complete-frontier perimeter on the arbitrary
representative; compatibility supplies that agreement on the canonical
profile and its source-finiteness. -/
theorem normalizationWitness_of_horizontalCongruence
    {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility : source.CompatibleWithModel profile)
    (sourceCarrier_perimeter_eq_frontier :
      source.perimeter sourceCarrier =
        _root_.WeightedPerimeter lam
          (FrontierMeasure sourceCarrier)) :
    source.NormalizationWitness sourceCarrier profile := by
  constructor
  · rw [profile.carrier_eq_candidate_assembly]
    exact (compatibility.model_covered profile.toCandidate.region).1
  · exact weightedArea_eq_of_horizontallyCongruent hcongruent
  · calc
      source.perimeter sourceCarrier =
          _root_.WeightedPerimeter lam
            (FrontierMeasure sourceCarrier) :=
        sourceCarrier_perimeter_eq_frontier
      _ = _root_.WeightedPerimeter lam
          (FrontierMeasure profile.carrier) :=
        frontierWeightedPerimeter_eq_of_horizontallyCongruent
          hcongruent
      _ = source.perimeter profile.carrier :=
        compatibility.profile_perimeter_eq.symm


/-- Source minimality is invariant under a supplied exact normalization
witness.  Establishing this witness for every classified source profile is a
separate geometric/source theorem. -/
theorem isMinimizer_of_normalizationWitness
    {sourceCarrier : Set PlanePoint}
    {profile : CanonicalTypeIVProfile lam}
    (hsource : source.IsMinimizer sourceCarrier)
    (normalization : source.NormalizationWitness sourceCarrier profile) :
    source.IsMinimizer profile.carrier := by
  refine ⟨normalization.normalized_finite, ?_⟩
  intro competitor hfinite harea
  rw [← normalization.perimeter_eq]
  exact hsource.2 competitor hfinite
    (harea.trans normalization.weightedArea_eq.symm)

/-- A normalized source minimizer becomes a minimizer in the modeled
`AdmissibleCompetitor` class. -/
theorem candidate_isWeightedPerimeterMinimizer
    (profile : CanonicalTypeIVProfile lam)
    (compatibility : source.CompatibleWithModel profile)
    (hmin : source.IsMinimizer profile.carrier) :
    profile.toCandidate.IsWeightedPerimeterMinimizer := by
  intro competitor harea
  have hsourceArea :
      _root_.WeightedArea lam competitor.carrier =
        _root_.WeightedArea lam profile.carrier := by
    calc
      _root_.WeightedArea lam competitor.carrier =
          competitor.WeightedArea :=
        competitor.weightedArea_eq_carrier.symm
      _ = profile.toCandidate.WeightedArea := harea
      _ = _root_.WeightedArea lam profile.carrier :=
        profile.weightedArea_eq_candidate.symm
  have hsourceLe := hmin.2 competitor.carrier
    (compatibility.model_covered competitor).1 hsourceArea
  calc
    profile.toCandidate.WeightedPerimeter =
        _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier) :=
      profile.frontierWeightedPerimeter_eq_candidate.symm
    _ = source.perimeter profile.carrier :=
      compatibility.profile_perimeter_eq.symm
    _ ≤ source.perimeter competitor.carrier := hsourceLe
    _ ≤ competitor.WeightedPerimeter :=
      (compatibility.model_covered competitor).2

/-- Full arbitrary-representative bridge: exact normalization plus boundary
semantics compatibility transfer source minimality to the canonical candidate. -/
theorem candidate_isWeightedPerimeterMinimizer_of_sourceNormalization
    {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (normalization : source.NormalizationWitness sourceCarrier profile)
    (compatibility : source.CompatibleWithModel profile)
    (hsource : source.IsMinimizer sourceCarrier) :
    profile.toCandidate.IsWeightedPerimeterMinimizer :=
  source.candidate_isWeightedPerimeterMinimizer profile compatibility
    (source.isMinimizer_of_normalizationWitness hsource normalization)

/-- Source minimality transfers directly from any horizontally translated
representative once the source perimeter is known to equal the actual
complete-frontier perimeter on that representative. -/
theorem candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
    {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility : source.CompatibleWithModel profile)
    (sourceCarrier_perimeter_eq_frontier :
      source.perimeter sourceCarrier =
        _root_.WeightedPerimeter lam
          (FrontierMeasure sourceCarrier))
    (hsource : source.IsMinimizer sourceCarrier) :
    profile.toCandidate.IsWeightedPerimeterMinimizer :=
  source.candidate_isWeightedPerimeterMinimizer_of_sourceNormalization
    profile
    (source.normalizationWitness_of_horizontalCongruence
      profile hcongruent compatibility
        sourceCarrier_perimeter_eq_frontier)
    compatibility hsource


end SourcePerimeterSemantics


/-- The repository's canonical complete-frontier semantics, used to verify that
the new quantifier bridge is unconditional inside the current model. -/
def canonicalFrontierSemantics (lam : ℝ) : SourcePerimeterSemantics lam where
  IsFinitePerimeter := fun carrier =>
    ∃ region : FinitePerimeterRegion lam, region.carrier = carrier
  perimeter := fun carrier =>
    _root_.WeightedPerimeter lam (FrontierMeasure carrier)

namespace canonicalFrontierSemantics

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

/-- Complete-frontier semantics covers every modeled competitor because each
constructor now has a value-preserving finite-perimeter realization. -/
theorem compatibleWithModel :
    (canonicalFrontierSemantics lam).CompatibleWithModel profile := by
  constructor
  · rfl
  · intro competitor
    constructor
    · exact ⟨competitor.toFinitePerimeterRegion,
        competitor.toFinitePerimeterRegion_carrier⟩
    · rfl

/-- In canonical complete-frontier semantics, horizontal congruence alone
constructs the exact normalization witness. -/
theorem normalizationWitness_of_horizontalCongruence
    {sourceCarrier : Set PlanePoint}
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier) :
    (canonicalFrontierSemantics lam).NormalizationWitness
      sourceCarrier profile :=
  SourcePerimeterSemantics.normalizationWitness_of_horizontalCongruence
    (canonicalFrontierSemantics lam) profile hcongruent
    (canonicalFrontierSemantics.compatibleWithModel profile) rfl

end canonicalFrontierSemantics
