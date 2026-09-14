/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveSourceGeometry
import CMVFigureFourBilateralIncidence
import CMVFigureFiveAngular

/-!
# Scalar accounting for CMV Figure 5

The independent Figure-5 source geometry already forces common radius one.  This
module computes the resulting cap angle, chord, area, and boundary excess for
each of its one or two capped interfaces.  It then proves that the component
model lies above the closed type-(iii) endpoint area and perimeter support line.

The scalar area theorem integrates the unchanged actual source through its
stored planar almost-everywhere representative relation.  It does not identify
the actual source carrier with a global component carrier and does not assert a
relaxed-perimeter lower bound.
-/

open Set Real MeasureTheory

noncomputable section

namespace CMVFigureThree.DegenerateHorizontalSegment

/-- Euclidean length of a possibly degenerate horizontal segment. -/
def length (s : DegenerateHorizontalSegment) : ℝ := s.rightX - s.leftX

lemma length_nonneg (s : DegenerateHorizontalSegment) : 0 ≤ s.length :=
  sub_nonneg.mpr s.left_le_right

end CMVFigureThree.DegenerateHorizontalSegment

namespace CMVFigureFive

/-- A possibly degenerate horizontal interface segment has planar measure
zero. -/
theorem volume_degenerateHorizontalSegment
    (s : CMVFigureThree.DegenerateHorizontalSegment) :
    volume s.carrier = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint | p.2 = s.baseY})
  · intro p hp
    exact hp.1
  · exact volume_horizontalLine s.baseY

/-- Every literal cap arc is planar-null. -/
theorem volume_capArcTrace (c : OneSidedCircularCap) :
    volume c.arcTrace = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint |
      CMVFigureFour.circleValue c.center c.radius p = 0})
  · intro p hp
    change CMVFigureFour.circleValue c.center c.radius p = 0
    have hcircle := hp.1
    unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
    nlinarith
  · exact CMVFigureFour.volume_circleValue_eq_zero _ _

/-- Every literal strip-side trace is planar-null. -/
theorem volume_stripCircleTrace
    (branch : CMVFigureFour.HorizontalCircleBranch)
    (center : PlanePoint) (radius : ℝ) :
    volume (CMVFigureFour.stripCircleTrace branch center radius) = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint |
      CMVFigureFour.circleValue center radius p = 0})
  · intro p hp
    exact hp.1
  · exact CMVFigureFour.volume_circleValue_eq_zero _ _

namespace CappedInterface

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- The positive signed contact law selects the principal Figure-5 cap angle. -/
theorem theta_eq_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) :
    b.cap.theta = endpointAngle lam := by
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  have hcos : cos b.cap.theta = 1 / lam := by
    apply (eq_div_iff hlam_ne).2
    simpa only [mul_comm] using b.signed_contact_law
  calc
    b.cap.theta = arccos (cos b.cap.theta) :=
      (Real.arccos_cos b.cap.theta_pos.le b.cap.theta_lt_pi.le).symm
    _ = endpointAngle lam := by rw [hcos]; rfl

/-- At source radius one, every Figure-5 cap has the endpoint chord. -/
theorem chord_eq_two_mul_sin_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.chord = 2 * sin (endpointAngle lam) := by
  have hcapRadius : b.cap.radius = 1 := b.cap_radius.trans hRadius
  have h := b.cap.radius_mul_sin
  rw [hcapRadius, b.theta_eq_endpointAngle hlam] at h
  linarith

/-- At source radius one, the cap arc length is twice its principal half-angle. -/
theorem arcLength_eq_two_mul_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.arcLength = 2 * endpointAngle lam := by
  rw [cap_arcLength_eq_two_radius_theta]
  rw [show b.cap.radius = 1 from b.cap_radius.trans hRadius,
    b.theta_eq_endpointAngle hlam]
  ring

/-- Exact radius-one cap area in principal-angle coordinates. -/
theorem euclideanArea_eq_endpointAngle_sub
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.euclideanArea =
      endpointAngle lam - sin (endpointAngle lam) * cos (endpointAngle lam) := by
  have hsin : 0 < sin (endpointAngle lam) :=
    sin_pos_of_pos_of_lt_pi (endpointAngle_mem hlam).1
      ((endpointAngle_mem hlam).2.trans (half_lt_self Real.pi_pos))
  rw [OneSidedCircularCap.euclideanArea, area,
    b.chord_eq_two_mul_sin_endpointAngle hlam hRadius,
    b.theta_eq_endpointAngle hlam]
  field_simp [ne_of_gt hsin]
  ring

/-- The density-weighted area of one source cap is the endpoint support gap. -/
theorem weightedAreaContribution_eq_endpointGap
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    lam * b.cap.euclideanArea = endpointGap lam := by
  rw [b.euclideanArea_eq_endpointAngle_sub hlam hRadius]
  calc
    lam * (endpointAngle lam - sin (endpointAngle lam) *
        cos (endpointAngle lam)) =
        lam * endpointAngle lam - sin (endpointAngle lam) *
          (lam * cos (endpointAngle lam)) := by ring
    _ = lam * endpointAngle lam - sin (endpointAngle lam) := by
      rw [← b.theta_eq_endpointAngle hlam, b.signed_contact_law]
      ring
    _ = endpointGap lam := rfl

/-- Replacing the cap chord by its exterior weighted arc adds twice the endpoint
support gap to boundary cost. -/
theorem weightedArc_sub_chord_eq_two_mul_endpointGap
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    lam * b.cap.arcLength - b.cap.chord = 2 * endpointGap lam := by
  rw [b.arcLength_eq_two_mul_endpointAngle hlam hRadius,
    b.chord_eq_two_mul_sin_endpointAngle hlam hRadius]
  unfold endpointGap
  ring

/-- The cap chord is contained in the full interval between strip tangencies. -/
theorem chord_le_tangent_span
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side) :
    b.cap.chord ≤ rightTangentX - leftTangentX := by
  have hbetween := b.cap_endpoints_between
  simp only [OneSidedCircularCap.leftEndpoint,
    OneSidedCircularCap.rightEndpoint] at hbetween
  linarith

end CappedInterface

namespace InterfaceBoundary

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- Real-valued cap indicator, used only for the finite one-or-two case split. -/
def capIndicator
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed _ => 0
  | .capped _ => 1

/-- The finite cap indicator is nonnegative. -/
theorem capIndicator_nonneg
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    0 ≤ b.capIndicator := by
  cases b <;> norm_num [capIndicator]

/-- The indicator records exactly the exposed/capped dichotomy. -/
theorem capIndicator_eq_zero_or_one
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    b.capIndicator = 0 ∨ b.capIndicator = 1 := by
  cases b <;> simp [capIndicator]

/-- Density-weighted area contributed outside the strip by this interface. -/
def weightedAreaContribution
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed _ => 0
  | .capped data => lam * data.cap.euclideanArea

/-- Weighted cost of the complete trace on this density interface. -/
def weightedBoundaryCost
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed data => data.segment.length
  | .capped data =>
      data.leftSegment.length + lam * data.cap.arcLength +
        data.rightSegment.length

/-- A capped interface contributes exactly one endpoint gap to weighted area. -/
theorem weightedAreaContribution_eq
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.weightedAreaContribution = b.capIndicator * endpointGap lam := by
  cases b with
  | exposed data => simp [weightedAreaContribution, capIndicator]
  | capped data =>
      simp only [weightedAreaContribution, capIndicator, one_mul]
      exact data.weightedAreaContribution_eq_endpointGap hlam hRadius

/-- The complete interface cost is its full tangency span plus twice the endpoint
gap when a cap replaces part of the flat interface. -/
theorem weightedBoundaryCost_eq
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.weightedBoundaryCost = rightTangentX - leftTangentX +
      2 * b.capIndicator * endpointGap lam := by
  cases b with
  | exposed data =>
      simp only [weightedBoundaryCost, capIndicator, mul_zero, zero_mul, add_zero]
      unfold CMVFigureThree.DegenerateHorizontalSegment.length
      rw [data.segment_starts_at_left_tangency,
        data.segment_ends_at_right_tangency]
  | capped data =>
      simp only [weightedBoundaryCost, capIndicator, mul_one]
      unfold CMVFigureThree.DegenerateHorizontalSegment.length
      rw [data.left_segment_starts_at_tangency,
        data.left_segment_ends_at_cap,
        data.right_segment_starts_at_cap,
        data.right_segment_ends_at_tangency]
      have hgap := data.weightedArc_sub_chord_eq_two_mul_endpointGap
        hlam hRadius
      simp only [OneSidedCircularCap.leftEndpoint,
        OneSidedCircularCap.rightEndpoint] at hgap ⊢
      linarith

/-- If this boundary is capped, its endpoint chord fits inside the tangency span. -/
theorem endpointChord_le_span_of_isCapped
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1)
    (hcapped : b.IsCapped) :
    2 * sin (endpointAngle lam) ≤ rightTangentX - leftTangentX := by
  cases b with
  | exposed data => simp [IsCapped] at hcapped
  | capped data =>
      rw [← data.chord_eq_two_mul_sin_endpointAngle hlam hRadius]
      exact data.chord_le_tangent_span

/-- The complete trace of either interface is planar-null. -/
theorem volume_trace
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    volume b.trace = 0 := by
  cases b with
  | exposed data =>
      simpa [trace] using volume_degenerateHorizontalSegment data.segment
  | capped data =>
      simp only [trace, CappedInterface.trace]
      exact measure_union_null
        (volume_degenerateHorizontalSegment data.leftSegment)
        (measure_union_null (volume_capArcTrace data.cap)
          (volume_degenerateHorizontalSegment data.rightSegment))

end InterfaceBoundary

/-- Removing the arc and chord from a closed cap does not change its planar
volume. -/
private theorem volume_capInterior (c : OneSidedCircularCap) :
    volume c.interiorCarrier = ENNReal.ofReal c.euclideanArea := by
  have hchord : volume c.chordCarrier = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint | p.2 = c.baseY})
    · intro p hp
      exact hp.1
    · exact volume_horizontalLine c.baseY
  have hboundary :
      volume (c.arcTrace ∪ c.chordCarrier) = 0 :=
    measure_union_null (volume_capArcTrace c) hchord
  have hclosedSubset :
      c.carrier ⊆ c.interiorCarrier ∪ (c.arcTrace ∪ c.chordCarrier) := by
    intro p hp
    by_cases hi : p ∈ c.interiorCarrier
    · exact Or.inl hi
    · right
      by_cases hcircle : c.radiusSquaredAt p = c.radius ^ 2
      · exact Or.inl ⟨hcircle, hp.2⟩
      · right
        apply c.mem_chordCarrier_of_mem_carrier_of_eq_base hp
        have hcircleLt :
            c.radiusSquaredAt p < c.radius ^ 2 :=
          lt_of_le_of_ne hp.1 hcircle
        cases hside : c.side with
        | upper =>
            simp only [OneSidedCircularCap.carrier, hside] at hp
            simp only [OneSidedCircularCap.interiorCarrier, hside] at hi
            by_contra hne
            apply hi
            exact ⟨hcircleLt, lt_of_le_of_ne hp.2 (Ne.symm hne)⟩
        | lower =>
            simp only [OneSidedCircularCap.carrier, hside] at hp
            simp only [OneSidedCircularCap.interiorCarrier, hside] at hi
            by_contra hne
            apply hi
            exact ⟨hcircleLt, lt_of_le_of_ne hp.2 hne⟩
  have hinteriorSubset : c.interiorCarrier ⊆ c.carrier := by
    intro p hp
    cases hside : c.side with
    | upper =>
        simp only [OneSidedCircularCap.interiorCarrier,
          OneSidedCircularCap.carrier, hside] at hp ⊢
        exact ⟨hp.1.le, hp.2.le⟩
    | lower =>
        simp only [OneSidedCircularCap.interiorCarrier,
          OneSidedCircularCap.carrier, hside] at hp ⊢
        exact ⟨hp.1.le, hp.2.le⟩
  have hleClosed :
      volume c.carrier ≤ volume c.interiorCarrier := by
    calc
      volume c.carrier ≤
          volume (c.interiorCarrier ∪
            (c.arcTrace ∪ c.chordCarrier)) :=
        measure_mono hclosedSubset
      _ ≤ volume c.interiorCarrier +
          volume (c.arcTrace ∪ c.chordCarrier) :=
        measure_union_le _ _
      _ = volume c.interiorCarrier := by rw [hboundary, add_zero]
  have hvolume :
      volume c.interiorCarrier = volume c.carrier :=
    le_antisymm (measure_mono hinteriorSubset) hleClosed
  rw [hvolume, c.volume_carrier]

namespace SourceGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- Number of capped interfaces, represented in `ℝ`; the source signature makes
this value either one or two. -/
def capCount : ℝ :=
  g.upperBoundary.capIndicator + g.lowerBoundary.capIndicator

/-- Component weighted area: radius-one stadium area plus exterior cap areas. -/
def modeledWeightedArea : ℝ :=
  Real.pi + 2 * g.width +
    g.upperBoundary.weightedAreaContribution +
      g.lowerBoundary.weightedAreaContribution

/-- Component weighted boundary cost: the two unit semicircles plus both
interface traces. -/
def modeledWeightedPerimeter : ℝ :=
  2 * Real.pi + g.upperBoundary.weightedBoundaryCost +
    g.lowerBoundary.weightedBoundaryCost

/-- Boundedness of the open representative gives finite weighted area before
any section integral is evaluated. -/
theorem integrableOn_representative :
    IntegrableOn (StripDensity lam) g.representative :=
  stripDensity_integrableOn_of_volume_ne_top lam
    g.sourceRepresentative.representative_bounded.measure_lt_top.ne

/-- Weighted-area integrability transports from the bounded representative to
the possibly unbounded almost-everywhere-modified actual source carrier. -/
theorem integrableOn_sourceCarrier :
    IntegrableOn (StripDensity lam) g.sourceCarrier :=
  g.integrableOn_representative.congr_set_ae
    g.sourceRepresentative.source_ae_representative

/-- Actual source weighted area is computed on the bounded open representative
through the stored planar almost-everywhere relation. -/
theorem weightedArea_sourceCarrier_eq_representative :
    _root_.WeightedArea lam g.sourceCarrier =
      _root_.WeightedArea lam g.representative :=
  CMVRelaxation.weightedArea_congr_ae lam
    g.sourceRepresentative.source_ae_representative

/-- Portion of the actual bounded representative in the strict density-one
strip. -/
def strictStripRegion : Set PlanePoint :=
  g.representative ∩ {p | |p.2| < 1}

/-- Portion of the actual bounded representative strictly above the strip. -/
def upperExteriorRegion : Set PlanePoint :=
  g.representative ∩ {p | 1 < p.2}

/-- Portion of the actual bounded representative strictly below the strip. -/
def lowerExteriorRegion : Set PlanePoint :=
  g.representative ∩ {p | p.2 < -1}


private theorem measurableSet_strictStripRegion :
    MeasurableSet g.strictStripRegion :=
  g.sourceRepresentative.representative_open.measurableSet.inter
    (isOpen_lt continuous_snd.abs continuous_const).measurableSet

private theorem measurableSet_upperExteriorRegion :
    MeasurableSet g.upperExteriorRegion :=
  g.sourceRepresentative.representative_open.measurableSet.inter
    (isOpen_lt continuous_const continuous_snd).measurableSet

private theorem measurableSet_lowerExteriorRegion :
    MeasurableSet g.lowerExteriorRegion :=
  g.sourceRepresentative.representative_open.measurableSet.inter
    (isOpen_lt continuous_snd continuous_const).measurableSet
/-- The three open density bands cut from the actual representative. -/
def sectionRegion : Set PlanePoint :=
  (g.strictStripRegion ∪ g.upperExteriorRegion) ∪
    g.lowerExteriorRegion

private theorem measurableSet_sectionRegion :
    MeasurableSet g.sectionRegion :=
  (g.measurableSet_strictStripRegion.union
    g.measurableSet_upperExteriorRegion).union
      g.measurableSet_lowerExteriorRegion

/-- The actual representative is almost everywhere the disjoint union of its
strict strip, upper exterior, and lower exterior.  Only the two density
interfaces are omitted. -/
theorem representative_ae_sectionRegion :
    g.representative =ᵐ[volume] g.sectionRegion := by
  let interfaces : Set PlanePoint :=
    {p | p.2 = -1} ∪ {p | p.2 = 1}
  have hinterfaces : volume interfaces = 0 :=
    measure_union_null (volume_horizontalLine (-1))
      (volume_horizontalLine 1)
  have hcover :
      g.representative ⊆ g.sectionRegion ∪ interfaces := by
    intro p hp
    by_cases hlower : p.2 < -1
    · exact Or.inl (Or.inr ⟨hp, hlower⟩)
    by_cases hlowerEq : p.2 = -1
    · exact Or.inr (Or.inl hlowerEq)
    have hlowerLt : -1 < p.2 :=
      lt_of_le_of_ne (not_lt.mp hlower) (Ne.symm hlowerEq)
    by_cases hupper : 1 < p.2
    · exact Or.inl (Or.inl (Or.inr ⟨hp, hupper⟩))
    by_cases hupperEq : p.2 = 1
    · exact Or.inr (Or.inr hupperEq)
    have hupperLt : p.2 < 1 :=
      lt_of_le_of_ne (not_lt.mp hupper) hupperEq
    exact Or.inl
      (Or.inl (Or.inl ⟨hp, abs_lt.mpr ⟨hlowerLt, hupperLt⟩⟩))
  have hsubset : g.sectionRegion ⊆ g.representative := by
    rintro p ((hstrip | hupper) | hlower)
    · exact hstrip.1
    · exact hupper.1
    · exact hlower.1
  have hle :
      volume g.representative ≤ volume g.sectionRegion := by
    calc
      volume g.representative ≤
          volume (g.sectionRegion ∪ interfaces) :=
        measure_mono hcover
      _ ≤ volume g.sectionRegion + volume interfaces :=
        measure_union_le _ _
      _ = volume g.sectionRegion := by
        rw [hinterfaces, add_zero]
  exact
    (ae_eq_of_subset_of_measure_ge hsubset hle
      g.measurableSet_sectionRegion.nullMeasurableSet
      g.sourceRepresentative.representative_bounded.measure_lt_top.ne).symm


private theorem horizontalSection_upperCapInterior
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    {y : ℝ} (hbase : 1 < y)
    (hpole : y < b.cap.center.2 + g.sourceRadius) :
    CMVSourceClassification.horizontalSection b.cap.interiorCarrier y =
      Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1) := by
  have hcenter := b.upper_center_lt_interface g.density_jump
  have hdiffLt : y - b.cap.center.2 < g.sourceRadius := by linarith
  have hdiffPos : 0 < y - b.cap.center.2 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 -
        (y - b.cap.center.2) ^ 2)) ^ 2 =
          g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  have hsqrtNonneg :
      0 ≤ √(g.sourceRadius ^ 2 -
        (y - b.cap.center.2) ^ 2) :=
    Real.sqrt_nonneg _
  ext x
  change
    (b.cap.radiusSquaredAt (x, y) < b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY < y
        | .lower => y < b.cap.baseY)) ↔
      x ∈ Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1)
  rw [b.cap_side, b.cap_base, b.cap_radius]
  simp only [interfaceY]
  unfold OneSidedCircularCap.radiusSquaredAt
    CappedInterface.exteriorLeftBoundaryPoint
    CappedInterface.exteriorRightBoundaryPoint
  dsimp only
  constructor
  · rintro ⟨hcircle, _⟩
    constructor <;> nlinarith
  · rintro ⟨hleft, hright⟩
    constructor
    · nlinarith
    · exact hbase

private theorem horizontalSection_lowerCapInterior
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    {y : ℝ} (hpole : b.cap.center.2 - g.sourceRadius < y)
    (hbase : y < -1) :
    CMVSourceClassification.horizontalSection b.cap.interiorCarrier y =
      Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1) := by
  have hcenter := b.lower_interface_lt_center g.density_jump
  have hdiffNeg : -g.sourceRadius < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < 0 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(g.sourceRadius ^ 2 -
        (y - b.cap.center.2) ^ 2)) ^ 2 =
          g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  have hsqrtNonneg :
      0 ≤ √(g.sourceRadius ^ 2 -
        (y - b.cap.center.2) ^ 2) :=
    Real.sqrt_nonneg _
  ext x
  change
    (b.cap.radiusSquaredAt (x, y) < b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY < y
        | .lower => y < b.cap.baseY)) ↔
      x ∈ Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1)
  rw [b.cap_side, b.cap_base, b.cap_radius]
  simp only [interfaceY]
  unfold OneSidedCircularCap.radiusSquaredAt
    CappedInterface.exteriorLeftBoundaryPoint
    CappedInterface.exteriorRightBoundaryPoint
  dsimp only
  constructor
  · rintro ⟨hcircle, _⟩
    constructor <;> nlinarith
  · rintro ⟨hleft, hright⟩
    constructor
    · nlinarith
    · exact hbase
/-- Direct Fubini integration of the already reconstructed strict-strip
sections.  This computes the actual representative region, not a supplied
stadium carrier. -/
theorem volume_strictStripRegion :
    volume g.strictStripRegion =
      ENNReal.ofReal (Real.pi + 2 * g.width) := by
  have hfiber (y : ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' g.strictStripRegion) =
        (Ioo (-1 : ℝ) 1).indicator
          (fun y => ENNReal.ofReal
            (g.width + 2 * √(1 - y ^ 2))) y := by
    by_cases hy : y ∈ Ioo (-1 : ℝ) 1
    · have hyAbs : |y| < 1 := abs_lt.mpr hy
      have hsection := g.actual_strictStripSection hyAbs
      have heq :
          (fun x : ℝ => (x, y)) ⁻¹' g.strictStripRegion =
            Ioo ((g.leftStripBoundaryPoint y).1)
              ((g.rightStripBoundaryPoint y).1) := by
        ext x
        change
          (x ∈ CMVSourceClassification.horizontalSection
              g.representative y ∧ |y| < 1) ↔
            x ∈ Ioo ((g.leftStripBoundaryPoint y).1)
              ((g.rightStripBoundaryPoint y).1)
        rw [hsection]
        simp only [hyAbs, and_true]
      rw [heq, Real.volume_Ioo, Set.indicator_of_mem hy]
      congr 1
      simp only [SourceGeometry.width,
        SourceGeometry.leftStripBoundaryPoint,
        SourceGeometry.rightStripBoundaryPoint]
      ring
    · rw [Set.indicator_of_notMem hy]
      have heq :
          (fun x : ℝ => (x, y)) ⁻¹' g.strictStripRegion = ∅ := by
        ext x
        change
          ((x, y) ∈ g.representative ∧ |y| < 1) ↔ False
        simp only [iff_false]
        intro h
        apply hy
        exact abs_lt.mp h.2
      rw [heq, measure_empty]
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply_symm g.measurableSet_strictStripRegion]
  simp_rw [hfiber]
  rw [lintegral_indicator measurableSet_Ioo]
  let f : ℝ → ℝ := fun y => g.width + 2 * √(1 - y ^ 2)
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfIntegrable : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    hfContinuous.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hfNonneg : ∀ y, 0 ≤ f y := by
    intro y
    dsimp only [f]
    nlinarith [g.width_pos, Real.sqrt_nonneg (1 - y ^ 2)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfIntegrable
    (Filter.Eventually.of_forall hfNonneg)]
  congr 1
  change (∫ y in Ioo (-1 : ℝ) 1,
      g.width + 2 * √(1 - y ^ 2)) =
    Real.pi + 2 * g.width
  rw [← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hsqrtContinuous :
      Continuous (fun y : ℝ => √(1 - y ^ 2)) := by
    fun_prop
  have hsqrtIntegrable :
      IntervalIntegrable (fun y : ℝ => √(1 - y ^ 2))
        volume (-1) 1 :=
    hsqrtContinuous.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (hsqrtIntegrable.const_mul 2)]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  norm_num
  ring

/-- The actual upper exterior has exactly the area of its optional source cap.
The proof reconstructs the planar region from the derived horizontal sections;
no normalized target carrier is an input. -/
theorem volume_upperExteriorRegion :
    volume g.upperExteriorRegion =
      match g.upperBoundary with
      | .exposed _ => 0
      | .capped b => ENNReal.ofReal b.cap.euclideanArea := by
  cases hBoundary : g.upperBoundary with
  | exposed b =>
      have hempty : g.upperExteriorRegion = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hsection :=
          g.actual_upperExposedSection_empty b hBoundary hp.2
        have hmem :
            p.1 ∈ CMVSourceClassification.horizontalSection
              g.representative p.2 :=
          hp.1
        rw [hsection] at hmem
        exact hmem
      rw [hempty, measure_empty]
  | capped b =>
      have hsections :
          ∀ᵐ y ∂(volume : Measure ℝ),
            CMVSourceClassification.horizontalSection
                g.upperExteriorRegion y =ᵐ[volume]
              CMVSourceClassification.horizontalSection
                b.cap.interiorCarrier y := by
        filter_upwards
          [measure_eq_zero_iff_ae_notMem.mp
            g.measure_exteriorExceptionalHeights] with y hy
        by_cases hbase : 1 < y
        · by_cases hpole :
              y < b.cap.center.2 + g.sourceRadius
          · have hactual :=
              g.actual_upperCappedSection b hBoundary hbase hpole
            have hcap :=
              g.horizontalSection_upperCapInterior b hbase hpole
            have hregion :
                CMVSourceClassification.horizontalSection
                    g.upperExteriorRegion y =
                  CMVSourceClassification.horizontalSection
                    g.representative y := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                SourceGeometry.upperExteriorRegion, mem_inter_iff,
                mem_ofPred_eq, hbase, and_true]
            rw [hregion, hactual, hcap]
            exact Filter.Eventually.of_forall (fun _ => rfl)
          · have hpoleNe :
                y ≠ b.cap.center.2 + g.sourceRadius := by
              intro heq
              apply hy
              simp [SourceGeometry.exteriorExceptionalHeights,
                InterfaceBoundary.tangentHeights, hBoundary, heq]
            have hpoleAbove :
                b.cap.center.2 + g.sourceRadius < y :=
              lt_of_le_of_ne (not_lt.mp hpole) (Ne.symm hpoleNe)
            have hactual :=
              g.actual_upperCappedSection_empty_above b hBoundary
                hbase hpoleAbove
            have hregion :
                CMVSourceClassification.horizontalSection
                    g.upperExteriorRegion y = ∅ := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                SourceGeometry.upperExteriorRegion, mem_inter_iff,
                mem_ofPred_eq, hbase, and_true, mem_empty_iff_false,
                iff_false]
              intro hx
              have : x ∈ CMVSourceClassification.horizontalSection
                  g.representative y := hx
              rw [hactual] at this
              exact this
            have hcap :
                CMVSourceClassification.horizontalSection
                    b.cap.interiorCarrier y = ∅ := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                OneSidedCircularCap.interiorCarrier, b.cap_side,
                mem_ofPred_eq, mem_empty_iff_false, iff_false]
              rintro ⟨hcircle, _⟩
              unfold OneSidedCircularCap.radiusSquaredAt at hcircle
              rw [b.cap_radius] at hcircle
              have hdiff :
                  g.sourceRadius < y - b.cap.center.2 := by linarith
              nlinarith [sq_nonneg (x - b.cap.center.1),
                g.sourceRadius_pos]
            rw [hregion, hcap]
            exact Filter.Eventually.of_forall (fun _ => rfl)
        · have hregion :
              CMVSourceClassification.horizontalSection
                  g.upperExteriorRegion y = ∅ := by
            ext x
            simp only [CMVSourceClassification.horizontalSection,
              SourceGeometry.upperExteriorRegion, mem_inter_iff,
              mem_ofPred_eq, mem_empty_iff_false, iff_false]
            exact fun hx => hbase hx.2
          have hcap :
              CMVSourceClassification.horizontalSection
                  b.cap.interiorCarrier y = ∅ := by
            ext x
            simp only [CMVSourceClassification.horizontalSection,
              OneSidedCircularCap.interiorCarrier, b.cap_side,
              b.cap_base, interfaceY, mem_ofPred_eq,
              mem_empty_iff_false, iff_false]
            exact fun hx => hbase hx.2
          rw [hregion, hcap]
          exact Filter.Eventually.of_forall (fun _ => rfl)
      have hae :
          g.upperExteriorRegion =ᵐ[volume] b.cap.interiorCarrier :=
        CMVSourceClassification.ae_eq_of_ae_horizontalSection_eq
          g.measurableSet_upperExteriorRegion.nullMeasurableSet
          b.cap.isOpen_interiorCarrier.measurableSet.nullMeasurableSet
          hsections
      calc
        volume g.upperExteriorRegion =
            volume b.cap.interiorCarrier :=
          measure_congr hae
        _ = ENNReal.ofReal b.cap.euclideanArea :=
          volume_capInterior b.cap

/-- The actual lower exterior has exactly the area of its optional source cap,
again by sectionwise Fubini reconstruction. -/
theorem volume_lowerExteriorRegion :
    volume g.lowerExteriorRegion =
      match g.lowerBoundary with
      | .exposed _ => 0
      | .capped b => ENNReal.ofReal b.cap.euclideanArea := by
  cases hBoundary : g.lowerBoundary with
  | exposed b =>
      have hempty : g.lowerExteriorRegion = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hsection :=
          g.actual_lowerExposedSection_empty b hBoundary hp.2
        have hmem :
            p.1 ∈ CMVSourceClassification.horizontalSection
              g.representative p.2 :=
          hp.1
        rw [hsection] at hmem
        exact hmem
      rw [hempty, measure_empty]
  | capped b =>
      have hsections :
          ∀ᵐ y ∂(volume : Measure ℝ),
            CMVSourceClassification.horizontalSection
                g.lowerExteriorRegion y =ᵐ[volume]
              CMVSourceClassification.horizontalSection
                b.cap.interiorCarrier y := by
        filter_upwards
          [measure_eq_zero_iff_ae_notMem.mp
            g.measure_exteriorExceptionalHeights] with y hy
        by_cases hbase : y < -1
        · by_cases hpole :
              b.cap.center.2 - g.sourceRadius < y
          · have hactual :=
              g.actual_lowerCappedSection b hBoundary hpole hbase
            have hcap :=
              g.horizontalSection_lowerCapInterior b hpole hbase
            have hregion :
                CMVSourceClassification.horizontalSection
                    g.lowerExteriorRegion y =
                  CMVSourceClassification.horizontalSection
                    g.representative y := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                SourceGeometry.lowerExteriorRegion, mem_inter_iff,
                mem_ofPred_eq, hbase, and_true]
            rw [hregion, hactual, hcap]
            exact Filter.Eventually.of_forall (fun _ => rfl)
          · have hpoleNe :
                y ≠ b.cap.center.2 - g.sourceRadius := by
              intro heq
              apply hy
              simp [SourceGeometry.exteriorExceptionalHeights,
                InterfaceBoundary.tangentHeights, hBoundary, heq]
            have hpoleBelow :
                y < b.cap.center.2 - g.sourceRadius :=
              lt_of_le_of_ne (not_lt.mp hpole) hpoleNe
            have hactual :=
              g.actual_lowerCappedSection_empty_below b hBoundary
                hpoleBelow hbase
            have hregion :
                CMVSourceClassification.horizontalSection
                    g.lowerExteriorRegion y = ∅ := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                SourceGeometry.lowerExteriorRegion, mem_inter_iff,
                mem_ofPred_eq, hbase, and_true, mem_empty_iff_false,
                iff_false]
              intro hx
              have : x ∈ CMVSourceClassification.horizontalSection
                  g.representative y := hx
              rw [hactual] at this
              exact this
            have hcap :
                CMVSourceClassification.horizontalSection
                    b.cap.interiorCarrier y = ∅ := by
              ext x
              simp only [CMVSourceClassification.horizontalSection,
                OneSidedCircularCap.interiorCarrier, b.cap_side,
                mem_ofPred_eq, mem_empty_iff_false, iff_false]
              rintro ⟨hcircle, _⟩
              unfold OneSidedCircularCap.radiusSquaredAt at hcircle
              rw [b.cap_radius] at hcircle
              have hdiff :
                  y - b.cap.center.2 < -g.sourceRadius := by linarith
              nlinarith [sq_nonneg (x - b.cap.center.1),
                g.sourceRadius_pos]
            rw [hregion, hcap]
            exact Filter.Eventually.of_forall (fun _ => rfl)
        · have hregion :
              CMVSourceClassification.horizontalSection
                  g.lowerExteriorRegion y = ∅ := by
            ext x
            simp only [CMVSourceClassification.horizontalSection,
              SourceGeometry.lowerExteriorRegion, mem_inter_iff,
              mem_ofPred_eq, mem_empty_iff_false, iff_false]
            exact fun hx => hbase hx.2
          have hcap :
              CMVSourceClassification.horizontalSection
                  b.cap.interiorCarrier y = ∅ := by
            ext x
            simp only [CMVSourceClassification.horizontalSection,
              OneSidedCircularCap.interiorCarrier, b.cap_side,
              b.cap_base, interfaceY, mem_ofPred_eq,
              mem_empty_iff_false, iff_false]
            exact fun hx => hbase hx.2
          rw [hregion, hcap]
          exact Filter.Eventually.of_forall (fun _ => rfl)
      have hae :
          g.lowerExteriorRegion =ᵐ[volume] b.cap.interiorCarrier :=
        CMVSourceClassification.ae_eq_of_ae_horizontalSection_eq
          g.measurableSet_lowerExteriorRegion.nullMeasurableSet
          b.cap.isOpen_interiorCarrier.measurableSet.nullMeasurableSet
          hsections
      calc
        volume g.lowerExteriorRegion =
            volume b.cap.interiorCarrier :=
          measure_congr hae
        _ = ENNReal.ofReal b.cap.euclideanArea :=
          volume_capInterior b.cap

/-- Direct weighted-area integration of the unchanged source carrier.  The
stored planar AE relation transports to the representative; Fubini-computed
band volumes then give exactly the component formula. -/
theorem weightedArea_sourceCarrier_eq_modeledWeightedArea :
    _root_.WeightedArea lam g.sourceCarrier = g.modeledWeightedArea := by
  have hstripUpper : AEDisjoint volume
      g.strictStripRegion g.upperExteriorRegion := by
    refine measure_mono_null ?_ (measure_empty : volume (∅ : Set PlanePoint) = 0)
    rintro p ⟨hstrip, hupper⟩
    exfalso
    have hstripY : |p.2| < 1 := hstrip.2
    have hy := (abs_lt.mp hstripY).2
    have hupperY : 1 < p.2 := hupper.2
    linarith [hupperY]
  have hfirstLower : AEDisjoint volume
      (g.strictStripRegion ∪ g.upperExteriorRegion)
      g.lowerExteriorRegion := by
    refine measure_mono_null ?_ (measure_empty : volume (∅ : Set PlanePoint) = 0)
    rintro p ⟨hfirst, hlower⟩
    rcases hfirst with hstrip | hupper
    · exfalso
      have hstripY : |p.2| < 1 := hstrip.2
      have hy := (abs_lt.mp hstripY).1
      have hlowerY : p.2 < -1 := hlower.2
      linarith [hlowerY]
    · exfalso
      have hupperY : 1 < p.2 := hupper.2
      have hlowerY : p.2 < -1 := hlower.2
      linarith [hupperY, hlowerY]
  have hstripIntegrable :
      IntegrableOn (StripDensity lam) g.strictStripRegion :=
    g.integrableOn_representative.mono_set inter_subset_left
  have hupperIntegrable :
      IntegrableOn (StripDensity lam) g.upperExteriorRegion :=
    g.integrableOn_representative.mono_set inter_subset_left
  have hlowerIntegrable :
      IntegrableOn (StripDensity lam) g.lowerExteriorRegion :=
    g.integrableOn_representative.mono_set inter_subset_left
  have hsectionArea :
      _root_.WeightedArea lam g.sectionRegion =
        (∫ p in g.strictStripRegion, StripDensity lam p) +
          (∫ p in g.upperExteriorRegion, StripDensity lam p) +
            ∫ p in g.lowerExteriorRegion, StripDensity lam p := by
    rw [_root_.WeightedArea, SourceGeometry.sectionRegion,
      setIntegral_union₀ hfirstLower
        g.measurableSet_lowerExteriorRegion.nullMeasurableSet
        (hstripIntegrable.union hupperIntegrable) hlowerIntegrable,
      setIntegral_union₀ hstripUpper
        g.measurableSet_upperExteriorRegion.nullMeasurableSet
        hstripIntegrable hupperIntegrable]
  have hstripIntegral :
      (∫ p in g.strictStripRegion, StripDensity lam p) =
        Real.pi + 2 * g.width := by
    calc
      (∫ p in g.strictStripRegion, StripDensity lam p) =
          ∫ _p in g.strictStripRegion, (1 : ℝ) := by
        apply setIntegral_congr_fun g.measurableSet_strictStripRegion
        intro p hp
        rw [StripDensity, if_pos hp.2.le]
      _ = volume.real g.strictStripRegion := by
        rw [integral_const, measureReal_restrict_apply_univ]
        simp
      _ = Real.pi + 2 * g.width := by
        rw [Measure.real, g.volume_strictStripRegion,
          ENNReal.toReal_ofReal]
        nlinarith [Real.pi_pos, g.width_pos]
  have hupperIntegral :
      (∫ p in g.upperExteriorRegion, StripDensity lam p) =
        g.upperBoundary.weightedAreaContribution := by
    calc
      (∫ p in g.upperExteriorRegion, StripDensity lam p) =
          ∫ _p in g.upperExteriorRegion, lam := by
        apply setIntegral_congr_fun g.measurableSet_upperExteriorRegion
        intro p hp
        have hpY : 1 < p.2 := hp.2
        rw [StripDensity, if_neg]
        exact not_le.mpr (hpY.trans_le (le_abs_self p.2))
      _ = lam * volume.real g.upperExteriorRegion := by
        rw [integral_const, measureReal_restrict_apply_univ]
        ring
      _ = g.upperBoundary.weightedAreaContribution := by
        cases hBoundary : g.upperBoundary with
        | exposed b =>
            rw [Measure.real, g.volume_upperExteriorRegion, hBoundary]
            simp [InterfaceBoundary.weightedAreaContribution]
        | capped b =>
            rw [Measure.real, g.volume_upperExteriorRegion, hBoundary,
              ENNReal.toReal_ofReal b.cap.euclideanArea_pos.le]
            rfl
  have hlowerIntegral :
      (∫ p in g.lowerExteriorRegion, StripDensity lam p) =
        g.lowerBoundary.weightedAreaContribution := by
    calc
      (∫ p in g.lowerExteriorRegion, StripDensity lam p) =
          ∫ _p in g.lowerExteriorRegion, lam := by
        apply setIntegral_congr_fun g.measurableSet_lowerExteriorRegion
        intro p hp
        rw [StripDensity, if_neg]
        apply not_le.mpr
        have hpY : p.2 < -1 := hp.2
        exact (show 1 < -p.2 by linarith [hpY]).trans_le
          (neg_le_abs p.2)
      _ = lam * volume.real g.lowerExteriorRegion := by
        rw [integral_const, measureReal_restrict_apply_univ]
        ring
      _ = g.lowerBoundary.weightedAreaContribution := by
        cases hBoundary : g.lowerBoundary with
        | exposed b =>
            rw [Measure.real, g.volume_lowerExteriorRegion, hBoundary]
            simp [InterfaceBoundary.weightedAreaContribution]
        | capped b =>
            rw [Measure.real, g.volume_lowerExteriorRegion, hBoundary,
              ENNReal.toReal_ofReal b.cap.euclideanArea_pos.le]
            rfl
  calc
    _root_.WeightedArea lam g.sourceCarrier =
        _root_.WeightedArea lam g.representative :=
      g.weightedArea_sourceCarrier_eq_representative
    _ = _root_.WeightedArea lam g.sectionRegion :=
      CMVRelaxation.weightedArea_congr_ae lam
        g.representative_ae_sectionRegion
    _ = g.modeledWeightedArea := by
      rw [hsectionArea, hstripIntegral, hupperIntegral, hlowerIntegral]
      rfl

/-- The literal complete frontier in every frozen Figure-5 source geometry has
planar measure zero. -/
theorem volume_frontier_representative :
    volume (frontier g.representative) = 0 := by
  rw [g.frontier_eq_components]
  exact measure_union_null
    (volume_stripCircleTrace .left g.leftStripCenter g.sourceRadius)
    (measure_union_null
      (volume_stripCircleTrace .right g.rightStripCenter g.sourceRadius)
      (measure_union_null g.upperBoundary.volume_trace
        g.lowerBoundary.volume_trace))

/-- Closing the bounded open representative changes it only on its null
complete frontier. -/
theorem representative_ae_closure :
    g.representative =ᵐ[volume] closure g.representative :=
  (closure_ae_eq_of_null_frontier g.volume_frontier_representative).symm

/-- The actual source carrier is almost everywhere the closed topological
carrier determined by its frozen representative.  This does not yet identify
that closure with the explicit segmented component model. -/
theorem sourceCarrier_ae_closure_representative :
    g.sourceCarrier =ᵐ[volume] closure g.representative :=
  g.sourceRepresentative.source_ae_representative.trans
    g.representative_ae_closure

/-- Weighted area may be computed on the closed representative without any
pointwise carrier equality. -/
theorem weightedArea_sourceCarrier_eq_closure :
    _root_.WeightedArea lam g.sourceCarrier =
      _root_.WeightedArea lam (closure g.representative) :=
  CMVRelaxation.weightedArea_congr_ae lam
    g.sourceCarrier_ae_closure_representative

/-- The extended relaxed perimeter is likewise invariant under passage to the
closed representative. -/
theorem relaxedPerimeter_sourceCarrier_eq_closure :
    CMVRelaxation.relaxedPerimeter lam g.sourceCarrier =
      CMVRelaxation.relaxedPerimeter lam (closure g.representative) :=
  CMVRelaxation.relaxedPerimeter_congr_ae lam
    g.sourceCarrier_ae_closure_representative

/-- Figure 5 has at least one capped interface. -/
theorem one_le_capCount : 1 ≤ g.capCount := by
  rcases g.has_exterior_cap with hupper | hlower
  · cases h : g.upperBoundary with
    | exposed data => simp [InterfaceBoundary.IsCapped, h] at hupper
    | capped data =>
        rw [capCount, h]
        change 1 ≤ 1 + g.lowerBoundary.capIndicator
        linarith [g.lowerBoundary.capIndicator_nonneg]
  · cases h : g.lowerBoundary with
    | exposed data => simp [InterfaceBoundary.IsCapped, h] at hlower
    | capped data =>
        rw [capCount, h]
        change 1 ≤ g.upperBoundary.capIndicator + 1
        linarith [g.upperBoundary.capIndicator_nonneg]

/-- The source signature's cap count is exactly one or two. -/
theorem capCount_eq_one_or_two : g.capCount = 1 ∨ g.capCount = 2 := by
  rcases g.upperBoundary.capIndicator_eq_zero_or_one with hupper | hupper <;>
    rcases g.lowerBoundary.capIndicator_eq_zero_or_one with hlower | hlower
  · exfalso
    have hcount := g.one_le_capCount
    rw [capCount, hupper, hlower] at hcount
    norm_num at hcount
  · left
    rw [capCount, hupper, hlower]
    norm_num
  · left
    rw [capCount, hupper, hlower]
    norm_num
  · right
    rw [capCount, hupper, hlower]
    norm_num

/-- Any one exterior cap forces the full source width to contain the common
endpoint chord. -/
theorem endpointChord_le_width :
    2 * sin (endpointAngle lam) ≤ g.width := by
  rcases g.has_exterior_cap with hupper | hlower
  · exact g.upperBoundary.endpointChord_le_span_of_isCapped g.density_jump
      g.sourceRadius_eq_one hupper
  · exact g.lowerBoundary.endpointChord_le_span_of_isCapped g.density_jump
      g.sourceRadius_eq_one hlower

/-- Exact component area after summing the one or two radius-one caps. -/
theorem modeledWeightedArea_eq :
    g.modeledWeightedArea =
      Real.pi + 2 * g.width + g.capCount * endpointGap lam := by
  rw [modeledWeightedArea, capCount,
    g.upperBoundary.weightedAreaContribution_eq g.density_jump
      g.sourceRadius_eq_one,
    g.lowerBoundary.weightedAreaContribution_eq g.density_jump
      g.sourceRadius_eq_one]
  ring

/-- Exact weighted area of the unchanged Figure-5 source carrier. -/
theorem weightedArea_sourceCarrier_eq :
    _root_.WeightedArea lam g.sourceCarrier =
      Real.pi + 2 * g.width + g.capCount * endpointGap lam :=
  g.weightedArea_sourceCarrier_eq_modeledWeightedArea.trans
    g.modeledWeightedArea_eq

/-- Exact component boundary cost after summing both interface traces. -/
theorem modeledWeightedPerimeter_eq :
    g.modeledWeightedPerimeter =
      2 * Real.pi + 2 * g.width + 2 * g.capCount * endpointGap lam := by
  rw [modeledWeightedPerimeter,
    g.upperBoundary.weightedBoundaryCost_eq g.density_jump
      g.sourceRadius_eq_one,
    g.lowerBoundary.weightedBoundaryCost_eq g.density_jump
      g.sourceRadius_eq_one]
  unfold width capCount
  ring

/-- Exact support identity before specializing the cap count to one or two. -/
theorem modeledWeightedPerimeter_sub_modeledWeightedArea :
    g.modeledWeightedPerimeter - g.modeledWeightedArea =
      Real.pi + g.capCount * endpointGap lam := by
  rw [g.modeledWeightedPerimeter_eq, g.modeledWeightedArea_eq]
  ring

/-- Closed type-(iii) endpoint area in the same support-gap coordinates. -/
theorem typeThreeArea_one_eq (hlam : 1 < lam) :
    LeanSuffixAnalytic.typeThreeArea lam 1 =
      Real.pi + 4 * sin (endpointAngle lam) + endpointGap lam := by
  have hsine := endpointSine_eq_scaledRadical hlam
  unfold LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  norm_num [Real.arcsin_one]
  rw [← hsine]
  unfold endpointGap endpointAngle
  ring

/-- Every Figure-5 component model has at least the closed type-(iii) endpoint
area.  Equality is possible only at the one-cap, zero-extra-segment geometry;
that refinement is not needed here. -/
theorem typeThreeArea_one_le_modeledWeightedArea :
    LeanSuffixAnalytic.typeThreeArea lam 1 ≤ g.modeledWeightedArea := by
  rw [typeThreeArea_one_eq g.density_jump, g.modeledWeightedArea_eq]
  have hgap : 0 ≤ endpointGap lam := (endpointGap_pos g.density_jump).le
  have hcount := mul_le_mul_of_nonneg_right g.one_le_capCount hgap
  linarith [g.endpointChord_le_width]

/-- The component boundary cost lies on or above the one-cap endpoint support
line at its own component area. -/
theorem modeledWeightedArea_add_support_le_modeledWeightedPerimeter :
    g.modeledWeightedArea + Real.pi + endpointGap lam ≤
      g.modeledWeightedPerimeter := by
  rw [g.modeledWeightedArea_eq, g.modeledWeightedPerimeter_eq]
  have hgap : 0 ≤ endpointGap lam := (endpointGap_pos g.density_jump).le
  have hcount := mul_le_mul_of_nonneg_right g.one_le_capCount hgap
  linarith

/-- The checked type-(iii) recovery produces an actual source-admissible carrier
with the component area and boundary cost strictly below the Figure-5 component
accounting.  Relating those component values to the actual source carrier is a
separate geometric/relaxation theorem. -/
theorem exists_admissible_typeThree_below_modeledWeightedPerimeter :
    ∃ a : _root_.TypeThreeAssembly lam,
      a.h ∈ Ioo (0 : ℝ) 1 ∧
      (CMVRelaxation.relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier = g.modeledWeightedArea ∧
      a.WeightedPerimeter < g.modeledWeightedPerimeter := by
  rcases exists_admissible_typeThree_below_endpoint_support g.density_jump
      g.typeThreeArea_one_le_modeledWeightedArea with
    ⟨a, ha, hadmissible, harea, hperimeter⟩
  exact ⟨a, ha, hadmissible, harea,
    hperimeter.trans_le g.modeledWeightedArea_add_support_le_modeledWeightedPerimeter⟩

/-- The same recovered type-(iii) carrier is cheaper in the extended relaxation
than the Figure-5 component cost, and its weighted area is the actual source
area.  This closes the competitor side of the source comparison; no lower bound
for the Figure-5 source perimeter is asserted here. -/
theorem exists_admissible_typeThree_relaxedPerimeter_lt_modeledWeightedPerimeter :
    ∃ a : _root_.TypeThreeAssembly lam,
      a.h ∈ Ioo (0 : ℝ) 1 ∧
      (CMVRelaxation.relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier =
        _root_.WeightedArea lam g.sourceCarrier ∧
      CMVRelaxation.relaxedPerimeter lam a.carrier <
        ENNReal.ofReal g.modeledWeightedPerimeter := by
  rcases g.exists_admissible_typeThree_below_modeledWeightedPerimeter with
    ⟨a, ha, hadmissible, harea, hperimeter⟩
  have hmodeledPos : 0 < g.modeledWeightedPerimeter :=
    lt_of_le_of_lt
      (CMVRelaxation.TypeThreeRecovery.assemblyWeightedPerimeter_nonneg a)
      hperimeter
  refine ⟨a, ha, hadmissible,
    harea.trans g.weightedArea_sourceCarrier_eq_modeledWeightedArea.symm, ?_⟩
  calc
    CMVRelaxation.relaxedPerimeter lam a.carrier ≤
        ENNReal.ofReal a.WeightedPerimeter :=
      CMVRelaxation.TypeThreeRecovery.relaxedPerimeter_le_frontierCost_typeThree a
    _ < ENNReal.ofReal g.modeledWeightedPerimeter :=
      (ENNReal.ofReal_lt_ofReal_iff hmodeledPos).2 hperimeter

/-- A lower bound by the literal Figure-5 component cost is sufficient for
source exclusion.  The premise is deliberately the remaining geometric/
relaxation obligation, rather than an assumed frontier equality or recovery
identity. -/
theorem sourceCarrier_not_isMinimizer_of_modeledWeightedPerimeter_le_relaxedPerimeter
    (hlower :
      ENNReal.ofReal g.modeledWeightedPerimeter ≤
        CMVRelaxation.relaxedPerimeter lam g.sourceCarrier) :
    ¬ (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
      g.sourceCarrier := by
  intro hmin
  rcases
      g.exists_admissible_typeThree_relaxedPerimeter_lt_modeledWeightedPerimeter with
    ⟨a, -, hadmissible, hequalArea, hstrict⟩
  have hsourceLeReal :=
    hmin.2 a.carrier hadmissible hequalArea
  have hsourceLe :
      CMVRelaxation.relaxedPerimeter lam g.sourceCarrier ≤
        CMVRelaxation.relaxedPerimeter lam a.carrier :=
    (CMVRelaxation.relaxedSourceSemantics_perimeter_le_iff
      hmin.1.1 hadmissible.1).1 hsourceLeReal
  exact (not_lt_of_ge hsourceLe) (hstrict.trans_le hlower)

end SourceGeometry

end CMVFigureFive
