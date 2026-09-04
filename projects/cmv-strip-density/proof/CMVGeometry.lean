/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MorgansArcFunction

/-!
# Coordinate geometry for the CMV strip model

This file fixes the geometric normalization used by the bridge.  The source does
not orient its cap chord or specify the minor-to-major continuation.  We use a
horizontal chord and the accepted `θ ∈ (0, π)` branch from
`MorgansArcFunction`.  Thus a closed upper cap has its chord on the interface,
its non-endpoint arc and interior above the interface, and its closure in the
closed upper half-plane.

The region constructors below are not scalar witnesses.  Each has a coordinate
carrier in `ℝ × ℝ`; area and boundary length are computed from its primitive
rectangle and circular-segment constructors.  This is the regular
piecewise-circular specialization of CMV's finite-perimeter semantics needed by
the cap substitution.
-/

open Set
open Real
open MeasureTheory

noncomputable section

/-- The coordinate plane used by the bridge. -/
abbrev PlanePoint := ℝ × ℝ

/-- The Euclidean L2 realization used to form geometric Hausdorff measure.
`PlanePoint` keeps its coordinate topology and all existing carrier definitions. -/
abbrev EuclideanPlane := WithLp 2 (ℝ × ℝ)

/-- The coordinate-preserving homeomorphism from the existing coordinate plane
to its Euclidean L2 realization. -/
noncomputable def planeEuclideanHomeomorph : PlanePoint ≃ₜ EuclideanPlane :=
  (WithLp.homeomorphProd 2 ℝ ℝ).symm

/-- CMV's strip density.  The closed interfaces belong to the density-one
branch. -/
def StripDensity (lam : ℝ) (p : PlanePoint) : ℝ :=
  if |p.2| ≤ 1 then 1 else lam

@[simp] theorem stripDensity_upper_interface (lam x : ℝ) :
    StripDensity lam (x, 1) = 1 := by
  simp [StripDensity]

@[simp] theorem stripDensity_lower_interface (lam x : ℝ) :
    StripDensity lam (x, -1) = 1 := by
  simp [StripDensity]

/-- Lebesgue weighted area for a general measurable planar carrier. -/
def WeightedArea (lam : ℝ) (carrier : Set PlanePoint) : ℝ :=
  ∫ p in carrier, StripDensity lam p

/-- Canonical Euclidean one-dimensional Hausdorff measure on the complete
topological frontier of a planar carrier, mapped back to the coordinate plane.
A general competitor cannot choose perimeter data independently of its region. -/
def FrontierMeasure (carrier : Set PlanePoint) : Measure PlanePoint :=
  Measure.map planeEuclideanHomeomorph.symm
    ((μH[1] : Measure EuclideanPlane).restrict
      (frontier (planeEuclideanHomeomorph '' carrier)))

/-- Weighted perimeter is the density integral against a boundary measure. -/
def WeightedPerimeter (lam : ℝ)
    (boundaryMeasure : Measure PlanePoint) : ℝ :=
  ∫ p, StripDensity lam p ∂boundaryMeasure

/-- General finite-perimeter input to minimization.  Its perimeter measure is
canonically the one-dimensional Hausdorff measure restricted to the complete
frontier; finiteness is an invariant, not independently supplied data. -/
structure FinitePerimeterRegion (lam : ℝ) where
  carrier : Set PlanePoint
  measurable_carrier : MeasurableSet carrier
  finite_weighted_area : IntegrableOn (StripDensity lam) carrier
  finite_weighted_perimeter :
    Integrable (StripDensity lam) (FrontierMeasure carrier)

namespace FinitePerimeterRegion

def weightedArea {lam : ℝ} (r : FinitePerimeterRegion lam) : ℝ :=
  WeightedArea lam r.carrier

def weightedPerimeter {lam : ℝ} (r : FinitePerimeterRegion lam) : ℝ :=
  WeightedPerimeter lam (FrontierMeasure r.carrier)

end FinitePerimeterRegion

/-- Which side of a horizontal chord contains a circular segment. -/
inductive CapSide where
  | upper
  | lower
  deriving DecidableEq

/-- A branch-correct circular segment on a horizontal chord.  Its carrier is
`disk ∩ half-plane`; this single definition includes minor, semicircular, and
major caps. -/
structure OneSidedCircularCap where
  chord : ℝ
  theta : ℝ
  midpointX : ℝ
  baseY : ℝ
  side : CapSide
  chord_pos : 0 < chord
  theta_pos : 0 < theta
  theta_lt_pi : theta < π

namespace OneSidedCircularCap

/-- Radius determined by chord length and half-central-angle. -/
def radius (c : OneSidedCircularCap) : ℝ := c.chord / (2 * sin c.theta)

/-- The center lies below an upper chord and above a lower chord.  For a major
cap `cos θ < 0`, so the center crosses to the cap side, as it should. -/
def center (c : OneSidedCircularCap) : PlanePoint :=
  match c.side with
  | .upper => (c.midpointX, c.baseY - c.radius * cos c.theta)
  | .lower => (c.midpointX, c.baseY + c.radius * cos c.theta)

/-- Coordinate realization of the selected arc, with parameter
`-theta ≤ t ≤ theta`. -/
def arcPoint (c : OneSidedCircularCap) (t : ℝ) : PlanePoint :=
  match c.side with
  | .upper =>
      (c.midpointX + c.radius * sin t,
        c.baseY + c.radius * (cos t - cos c.theta))
  | .lower =>
      (c.midpointX + c.radius * sin t,
        c.baseY - c.radius * (cos t - cos c.theta))

/-- Left endpoint of the oriented chord. -/
def leftEndpoint (c : OneSidedCircularCap) : PlanePoint :=
  (c.midpointX - c.chord / 2, c.baseY)

/-- Right endpoint of the oriented chord. -/
def rightEndpoint (c : OneSidedCircularCap) : PlanePoint :=
  (c.midpointX + c.chord / 2, c.baseY)

/-- Squared distance from the cap's circle center. -/
def radiusSquaredAt (c : OneSidedCircularCap) (p : PlanePoint) : ℝ :=
  (p.1 - c.center.1) ^ 2 + (p.2 - c.center.2) ^ 2

/-- The genuine closed coordinate carrier of a one-sided cap. -/
def carrier (c : OneSidedCircularCap) : Set PlanePoint :=
  {p | c.radiusSquaredAt p ≤ c.radius ^ 2 ∧
    match c.side with
    | .upper => c.baseY ≤ p.2
    | .lower => p.2 ≤ c.baseY}

/-- The open cap interior.  Endpoints and the chord are deliberately absent. -/
def interiorCarrier (c : OneSidedCircularCap) : Set PlanePoint :=
  {p | c.radiusSquaredAt p < c.radius ^ 2 ∧
    match c.side with
    | .upper => c.baseY < p.2
    | .lower => p.2 < c.baseY}

/-- The horizontal chord, including both endpoints. -/
def chordCarrier (c : OneSidedCircularCap) : Set PlanePoint :=
  {p | p.2 = c.baseY ∧ |p.1 - c.midpointX| ≤ c.chord / 2}

/-- Euclidean area computed by the circular-segment constructor. -/
def euclideanArea (c : OneSidedCircularCap) : ℝ := c.chord ^ 2 * area c.theta

/-- Euclidean length of the selected circular arc. -/
def arcLength (c : OneSidedCircularCap) : ℝ := c.chord * ell c.theta

/-- The branch-correct cap with prescribed positive normalized area.  This is
the reusable geometric constructor behind the candidate-specific replacement. -/
def ofNormalizedArea (q x midpointX baseY : ℝ) (side : CapSide)
    (hq : 0 < q) (hx : 0 < x) : OneSidedCircularCap where
  chord := q
  theta := θOf x
  midpointX := midpointX
  baseY := baseY
  side := side
  chord_pos := hq
  theta_pos := (θOf_mem hx).1
  theta_lt_pi := (θOf_mem hx).2

@[simp] theorem ofNormalizedArea_euclideanArea
    (q x midpointX baseY : ℝ) (side : CapSide)
    (hq : 0 < q) (hx : 0 < x) :
    (ofNormalizedArea q x midpointX baseY side hq hx).euclideanArea =
      q ^ 2 * x := by
  rw [euclideanArea]
  exact congrArg (q ^ 2 * ·) (area_θOf hx)

@[simp] theorem ofNormalizedArea_arcLength
    (q x midpointX baseY : ℝ) (side : CapSide)
    (hq : 0 < q) (hx : 0 < x) :
    (ofNormalizedArea q x midpointX baseY side hq hx).arcLength =
      q * arc x := by
  rfl

/-- The prescribed-area angle is the only accepted angle in `(0, π)`. -/
theorem ofNormalizedArea_theta_unique
    (q x midpointX baseY : ℝ) (side : CapSide)
    (hq : 0 < q) (hx : 0 < x)
    {theta : ℝ} (htheta : theta ∈ Ioo 0 π) (harea : area theta = x) :
    theta = (ofNormalizedArea q x midpointX baseY side hq hx).theta := by
  apply area_strictMonoOn.injOn htheta (θOf_mem hx)
  rw [area_θOf hx]
  exact harea

theorem sin_theta_pos (c : OneSidedCircularCap) : 0 < sin c.theta :=
  sin_pos_of_pos_of_lt_pi c.theta_pos c.theta_lt_pi

theorem radius_pos (c : OneSidedCircularCap) : 0 < c.radius := by
  exact div_pos c.chord_pos (mul_pos (by norm_num) c.sin_theta_pos)

theorem euclideanArea_pos (c : OneSidedCircularCap) : 0 < c.euclideanArea := by
  exact mul_pos (sq_pos_of_pos c.chord_pos) (area_pos c.theta_pos c.theta_lt_pi)

theorem ell_theta_pos (c : OneSidedCircularCap) : 0 < ell c.theta := by
  rw [ell]
  exact div_pos c.theta_pos c.sin_theta_pos

theorem arcLength_pos (c : OneSidedCircularCap) : 0 < c.arcLength :=
  mul_pos c.chord_pos c.ell_theta_pos

theorem radius_mul_sin (c : OneSidedCircularCap) :
    c.radius * sin c.theta = c.chord / 2 := by
  rw [radius]
  field_simp [ne_of_gt c.sin_theta_pos]

theorem arcPoint_left (c : OneSidedCircularCap) :
    c.arcPoint (-c.theta) = c.leftEndpoint := by
  cases h : c.side <;>
    simp [arcPoint, leftEndpoint, h, sin_neg, c.radius_mul_sin] <;> ring

theorem arcPoint_right (c : OneSidedCircularCap) :
    c.arcPoint c.theta = c.rightEndpoint := by
  cases h : c.side <;>
    simp [arcPoint, rightEndpoint, h, c.radius_mul_sin]

/-- Every point of the selected arc lies in the declared closed half-plane,
including on the major branch. -/
theorem arcPoint_in_closed_side (c : OneSidedCircularCap) {t : ℝ}
    (ht : |t| ≤ c.theta) :
    match c.side with
    | .upper => c.baseY ≤ (c.arcPoint t).2
    | .lower => (c.arcPoint t).2 ≤ c.baseY := by
  have hc : cos c.theta ≤ cos t := by
    rw [← Real.cos_abs t]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (le_of_lt c.theta_lt_pi) ht
  have hr := c.radius_pos
  cases h : c.side <;> simp [arcPoint, h] <;> nlinarith

/-- A non-endpoint arc point is strictly on the cap side of the chord. -/
theorem arcPoint_in_open_side (c : OneSidedCircularCap) {t : ℝ}
    (ht : |t| < c.theta) :
    match c.side with
    | .upper => c.baseY < (c.arcPoint t).2
    | .lower => (c.arcPoint t).2 < c.baseY := by
  have hc : cos c.theta < cos t := by
    rw [← Real.cos_abs t]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (le_of_lt c.theta_lt_pi) ht
  have hr := c.radius_pos
  cases h : c.side <;> simp [arcPoint, h] <;> nlinarith

/-- The selected circular arc has no self-intersections, including on the
major branch. -/
theorem arcPoint_injOn (c : OneSidedCircularCap) :
    Set.InjOn c.arcPoint (Icc (-c.theta) c.theta) := by
  intro t ht u hu htu
  have hr := c.radius_pos
  have hsin : sin t = sin u := by
    have hx := congrArg Prod.fst htu
    cases hside : c.side <;>
      simp only [arcPoint, hside] at hx <;> nlinarith
  have hcos : cos t = cos u := by
    have hy := congrArg Prod.snd htu
    cases hside : c.side <;>
      simp only [arcPoint, hside] at hy <;> nlinarith
  have hcircle : circleMap 0 1 t = circleMap 0 1 u := by
    apply Complex.ext
    · simpa [circleMap_zero_re] using hcos
    · simpa [circleMap_zero_im] using hsin
  apply eq_of_circleMap_eq one_ne_zero _ hcircle
  rcases ht with ⟨htl, htr⟩
  rcases hu with ⟨hul, hur⟩
  rw [abs_lt]
  constructor <;> linarith [c.theta_lt_pi]

/-- A cap point on the base line lies on the finite chord, not elsewhere on
the supporting line. -/
theorem mem_chordCarrier_of_mem_carrier_of_eq_base
    (c : OneSidedCircularCap) {p : PlanePoint}
    (hp : p ∈ c.carrier) (hy : p.2 = c.baseY) :
    p ∈ c.chordCarrier := by
  refine ⟨hy, ?_⟩
  have hdisk := hp.1
  cases hside : c.side <;>
    simp only [radiusSquaredAt, center, hside, hy] at hdisk
  all_goals
    have htrig := Real.sin_sq_add_cos_sq c.theta
    have htrigScaled := congrArg
      (fun z : ℝ => c.radius ^ 2 * z) htrig
    have hsq : (p.1 - c.midpointX) ^ 2 ≤
        (c.radius * sin c.theta) ^ 2 := by
      nlinarith
    rw [c.radius_mul_sin] at hsq
    exact abs_le_of_sq_le_sq hsq
      (div_nonneg c.chord_pos.le (by norm_num))

/-- Every point of the finite chord belongs to the closed cap. -/
theorem chordCarrier_subset_carrier (c : OneSidedCircularCap) :
    c.chordCarrier ⊆ c.carrier := by
  intro p hp
  have hxabs : |p.1 - c.midpointX| ≤ c.chord / 2 := hp.2
  have hhalf : 0 < c.chord / 2 := div_pos c.chord_pos (by norm_num)
  have hxsq : (p.1 - c.midpointX) ^ 2 ≤ (c.chord / 2) ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_pos hhalf] using hxabs)
  rw [← c.radius_mul_sin] at hxsq
  have htrig := Real.sin_sq_add_cos_sq c.theta
  have htrigScaled := congrArg
    (fun z : ℝ => c.radius ^ 2 * z) htrig
  cases hside : c.side with
  | upper =>
      constructor
      · simp only [radiusSquaredAt, center, hside, hp.1]
        nlinarith
      · simp [hside, hp.1]
  | lower =>
      constructor
      · simp only [radiusSquaredAt, center, hside, hp.1]
        nlinarith
      · simp [hside, hp.1]

/-- The coordinate cap is measurable. -/
theorem measurableSet_carrier (c : OneSidedCircularCap) :
    MeasurableSet c.carrier := by
  have hdist : Continuous (fun p : PlanePoint => c.radiusSquaredAt p) := by
    simp only [radiusSquaredAt]
    fun_prop
  have hdisk : MeasurableSet {p : PlanePoint |
      c.radiusSquaredAt p ≤ c.radius ^ 2} :=
    (isClosed_le hdist continuous_const).measurableSet
  cases h : c.side with
  | upper =>
      have hhalf : MeasurableSet {p : PlanePoint | c.baseY ≤ p.2} :=
        (isClosed_le continuous_const continuous_snd).measurableSet
      rw [carrier]
      simp only [h]
      change MeasurableSet
        ({p : PlanePoint | c.radiusSquaredAt p ≤ c.radius ^ 2} ∩
          {p : PlanePoint | c.baseY ≤ p.2})
      exact hdisk.inter hhalf
  | lower =>
      have hhalf : MeasurableSet {p : PlanePoint | p.2 ≤ c.baseY} :=
        (isClosed_le continuous_snd continuous_const).measurableSet
      rw [carrier]
      simp only [h]
      change MeasurableSet
        ({p : PlanePoint | c.radiusSquaredAt p ≤ c.radius ^ 2} ∩
          {p : PlanePoint | p.2 ≤ c.baseY})
      exact hdisk.inter hhalf

/-- The disk/closed-half-plane cap carrier is closed. -/
theorem isClosed_carrier (c : OneSidedCircularCap) :
    IsClosed c.carrier := by
  have hdist : Continuous (fun p : PlanePoint => c.radiusSquaredAt p) := by
    simp only [radiusSquaredAt]
    fun_prop
  have hdisk : IsClosed {p : PlanePoint |
      c.radiusSquaredAt p ≤ c.radius ^ 2} :=
    isClosed_le hdist continuous_const
  cases hside : c.side with
  | upper =>
      rw [carrier]
      simp only [hside]
      change IsClosed
        ({p : PlanePoint | c.radiusSquaredAt p ≤ c.radius ^ 2} ∩
          {p : PlanePoint | c.baseY ≤ p.2})
      exact hdisk.inter (isClosed_le continuous_const continuous_snd)
  | lower =>
      rw [carrier]
      simp only [hside]
      change IsClosed
        ({p : PlanePoint | c.radiusSquaredAt p ≤ c.radius ^ 2} ∩
          {p : PlanePoint | p.2 ≤ c.baseY})
      exact hdisk.inter (isClosed_le continuous_snd continuous_const)

end OneSidedCircularCap

/-- A horizontal segment.  Its metric length is its positive chord parameter,
not an independently asserted scalar. -/
structure HorizontalSegment where
  chord : ℝ
  midpointX : ℝ
  baseY : ℝ
  chord_pos : 0 < chord

namespace HorizontalSegment

def leftEndpoint (s : HorizontalSegment) : PlanePoint :=
  (s.midpointX - s.chord / 2, s.baseY)

def rightEndpoint (s : HorizontalSegment) : PlanePoint :=
  (s.midpointX + s.chord / 2, s.baseY)

def carrier (s : HorizontalSegment) : Set PlanePoint :=
  {p | p.2 = s.baseY ∧ |p.1 - s.midpointX| ≤ s.chord / 2}

def euclideanLength (s : HorizontalSegment) : ℝ := s.chord

end HorizontalSegment

/-- The unchanged central part of a type-(iv) candidate.  It is the rectangle
of height two and width `chord`, together with the two radius-`1/h` side
segments. -/
structure StripCore where
  chord : ℝ
  curvature : ℝ
  chord_pos : 0 < chord
  curvature_pos : 0 < curvature
  curvature_le_one : curvature ≤ 1

namespace StripCore

/-- Common radius of both strip arcs. -/
def radius (c : StripCore) : ℝ := 1 / c.curvature

/-- Half-central-angle of either strip arc. -/
def sideAngle (c : StripCore) : ℝ := arcsin c.curvature

def leftCenterX (c : StripCore) : ℝ :=
  -c.chord / 2 + c.radius * cos c.sideAngle

def rightCenterX (c : StripCore) : ℝ :=
  c.chord / 2 - c.radius * cos c.sideAngle

def rectangleCarrier (c : StripCore) : Set PlanePoint :=
  {p | -c.chord / 2 ≤ p.1 ∧ p.1 ≤ c.chord / 2 ∧ |p.2| ≤ 1}

def leftCapCarrier (c : StripCore) : Set PlanePoint :=
  {p | (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2 ∧
    p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1}

def rightCapCarrier (c : StripCore) : Set PlanePoint :=
  {p | (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2 ∧
    c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1}

/-- Genuine coordinate carrier of the retained central region. -/
def carrier (c : StripCore) : Set PlanePoint :=
  c.rectangleCarrier ∪ c.leftCapCarrier ∪ c.rightCapCarrier

/-- Rectangle plus two side circular segments. -/
def euclideanArea (c : StripCore) : ℝ :=
  2 * c.chord + 8 * area c.sideAngle

/-- The two side arcs, each of chord length two. -/
def boundaryArcLength (c : StripCore) : ℝ :=
  4 * ell c.sideAngle

theorem radius_pos (c : StripCore) : 0 < c.radius :=
  one_div_pos.mpr c.curvature_pos

theorem sideAngle_pos (c : StripCore) : 0 < c.sideAngle := by
  simpa [sideAngle] using (Real.arcsin_pos.mpr c.curvature_pos)

theorem sideAngle_le_pi_div_two (c : StripCore) :
    c.sideAngle ≤ π / 2 := by
  exact Real.arcsin_le_pi_div_two c.curvature

theorem sideAngle_lt_pi (c : StripCore) : c.sideAngle < π := by
  have hp := Real.pi_pos
  linarith [c.sideAngle_le_pi_div_two]

theorem sin_sideAngle (c : StripCore) : sin c.sideAngle = c.curvature := by
  rw [sideAngle]
  exact Real.sin_arcsin (by linarith [c.curvature_pos]) c.curvature_le_one

theorem cos_sideAngle (c : StripCore) :
    cos c.sideAngle = √(1 - c.curvature ^ 2) := by
  simp [sideAngle, Real.cos_arcsin]

theorem carrier_y_bounds (c : StripCore) {p : PlanePoint}
    (hp : p ∈ c.carrier) : |p.2| ≤ 1 := by
  rcases hp with (hp | hp) | hp
  · exact hp.2.2
  · exact hp.2.2
  · exact hp.2.2

/-- Every horizontal segment across the core rectangle is contained in the
retained region. -/
theorem horizontalChord_subset_carrier (c : StripCore) {y : ℝ}
    (hy : |y| ≤ 1) :
    {p : PlanePoint | p.2 = y ∧ |p.1| ≤ c.chord / 2} ⊆ c.carrier := by
  intro p hp
  have hx := abs_le.mp hp.2
  apply Or.inl
  apply Or.inl
  exact ⟨by linarith, by linarith, by simpa [hp.1] using hy⟩

theorem measurableSet_carrier (c : StripCore) : MeasurableSet c.carrier := by
  have hx : Continuous (fun p : PlanePoint => p.1) := continuous_fst
  have hy : Continuous (fun p : PlanePoint => p.2) := continuous_snd
  have hrect : MeasurableSet c.rectangleCarrier := by
    have hxmin : IsClosed {p : PlanePoint | -c.chord / 2 ≤ p.1} :=
      isClosed_le continuous_const hx
    have hxmax : IsClosed {p : PlanePoint | p.1 ≤ c.chord / 2} :=
      isClosed_le hx continuous_const
    have hybound : IsClosed {p : PlanePoint | |p.2| ≤ 1} :=
      isClosed_le hy.abs continuous_const
    rw [rectangleCarrier]
    change MeasurableSet
      ({p : PlanePoint | -c.chord / 2 ≤ p.1} ∩
        ({p : PlanePoint | p.1 ≤ c.chord / 2} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (hxmin.inter (hxmax.inter hybound)).measurableSet
  have hleft : MeasurableSet c.leftCapCarrier := by
    have hdisk : IsClosed {p : PlanePoint |
        (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} :=
      isClosed_le (((hx.sub continuous_const).pow 2).add (hy.pow 2))
        continuous_const
    have hxbound : IsClosed {p : PlanePoint | p.1 ≤ -c.chord / 2} :=
      isClosed_le hx continuous_const
    have hybound : IsClosed {p : PlanePoint | |p.2| ≤ 1} :=
      isClosed_le hy.abs continuous_const
    rw [leftCapCarrier]
    change MeasurableSet
      ({p : PlanePoint |
          (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} ∩
        ({p : PlanePoint | p.1 ≤ -c.chord / 2} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (hdisk.inter (hxbound.inter hybound)).measurableSet
  have hright : MeasurableSet c.rightCapCarrier := by
    have hdisk : IsClosed {p : PlanePoint |
        (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} :=
      isClosed_le (((hx.sub continuous_const).pow 2).add (hy.pow 2))
        continuous_const
    have hxbound : IsClosed {p : PlanePoint | c.chord / 2 ≤ p.1} :=
      isClosed_le continuous_const hx
    have hybound : IsClosed {p : PlanePoint | |p.2| ≤ 1} :=
      isClosed_le hy.abs continuous_const
    rw [rightCapCarrier]
    change MeasurableSet
      ({p : PlanePoint |
          (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} ∩
        ({p : PlanePoint | c.chord / 2 ≤ p.1} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (hdisk.inter (hxbound.inter hybound)).measurableSet
  exact (hrect.union hleft).union hright

end StripCore

private theorem circle_eq_not_mem_interior_disk
    (cx cy r : ℝ) (hr : 0 < r) (p : PlanePoint)
    (hp : (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 = r ^ 2) :
    p ∉ interior {q : PlanePoint |
      (q.1 - cx) ^ 2 + (q.2 - cy) ^ 2 ≤ r ^ 2} := by
  intro hi
  have hn : interior {q : PlanePoint |
      (q.1 - cx) ^ 2 + (q.2 - cy) ^ 2 ≤ r ^ 2} ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  have hnonzero : p.1 - cx ≠ 0 ∨ p.2 - cy ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    nlinarith
  rcases hnonzero with hx | hy
  · rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · let q : PlanePoint := (p.1 - ε / 2, p.2)
      have hqball : q ∈ Metric.ball p ε := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [q]
        rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hq := interior_subset (hball hqball)
      dsimp [q] at hq
      nlinarith
    · let q : PlanePoint := (p.1 + ε / 2, p.2)
      have hqball : q ∈ Metric.ball p ε := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [q]
        rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hq := interior_subset (hball hqball)
      dsimp [q] at hq
      nlinarith
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · let q : PlanePoint := (p.1, p.2 - ε / 2)
      have hqball : q ∈ Metric.ball p ε := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [q]
        rw [abs_of_neg (by linarith : p.2 - ε / 2 - p.2 < 0)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_right (by positivity)]
        linarith
      have hq := interior_subset (hball hqball)
      dsimp [q] at hq
      nlinarith
    · let q : PlanePoint := (p.1, p.2 + ε / 2)
      have hqball : q ∈ Metric.ball p ε := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [q]
        rw [abs_of_pos (by linarith : 0 < p.2 + ε / 2 - p.2)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_right (by positivity)]
        linarith
      have hq := interior_subset (hball hqball)
      dsimp [q] at hq
      nlinarith

private theorem second_eq_not_mem_interior_ge (b : ℝ) (p : PlanePoint)
    (hp : p.2 = b) :
    p ∉ interior {q : PlanePoint | b ≤ q.2} := by
  intro hi
  have hn : interior {q : PlanePoint | b ≤ q.2} ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  have hnear : (p.1, p.2 - ε / 2) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
      show p.2 - ε / 2 - p.2 = -(ε / 2) by ring,
      abs_neg, abs_of_pos hhalf, max_eq_right hhalf.le]
    linarith
  have := interior_subset (hball hnear)
  dsimp at this
  linarith

private theorem second_eq_not_mem_interior_le (b : ℝ) (p : PlanePoint)
    (hp : p.2 = b) :
    p ∉ interior {q : PlanePoint | q.2 ≤ b} := by
  intro hi
  have hn : interior {q : PlanePoint | q.2 ≤ b} ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  have hnear : (p.1, p.2 + ε / 2) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
      show p.2 + ε / 2 - p.2 = ε / 2 by ring,
      abs_of_pos hhalf, max_eq_right hhalf.le]
    linarith
  have := interior_subset (hball hnear)
  dsimp at this
  linarith

namespace OneSidedCircularCap

/-- The exact circular part of the boundary of a one-sided cap. -/
def arcTrace (c : OneSidedCircularCap) : Set PlanePoint :=
  {p | c.radiusSquaredAt p = c.radius ^ 2 ∧
    match c.side with
    | .upper => c.baseY ≤ p.2
    | .lower => p.2 ≤ c.baseY}

theorem isOpen_interiorCarrier (c : OneSidedCircularCap) :
    IsOpen c.interiorCarrier := by
  have hdisk : IsOpen {p : PlanePoint |
      c.radiusSquaredAt p < c.radius ^ 2} := by
    apply isOpen_lt
    · change Continuous (fun p : PlanePoint =>
        (p.1 - c.center.1) ^ 2 + (p.2 - c.center.2) ^ 2)
      fun_prop
    · fun_prop
  cases hside : c.side with
  | upper =>
      rw [OneSidedCircularCap.interiorCarrier]
      simp only [hside]
      change IsOpen
        ({p : PlanePoint | c.radiusSquaredAt p < c.radius ^ 2} ∩
          {p : PlanePoint | c.baseY < p.2})
      exact hdisk.inter (isOpen_lt continuous_const continuous_snd)
  | lower =>
      rw [OneSidedCircularCap.interiorCarrier]
      simp only [hside]
      change IsOpen
        ({p : PlanePoint | c.radiusSquaredAt p < c.radius ^ 2} ∩
          {p : PlanePoint | p.2 < c.baseY})
      exact hdisk.inter (isOpen_lt continuous_snd continuous_const)

theorem interiorCarrier_subset_interior (c : OneSidedCircularCap) :
    c.interiorCarrier ⊆ interior c.carrier := by
  apply interior_maximal
  intro p hp
  exact ⟨hp.1.le, by
    cases hside : c.side <;>
      simp only [OneSidedCircularCap.interiorCarrier, hside] at hp <;>
      simp only [OneSidedCircularCap.carrier, hside] <;> linarith [hp.2]⟩
  exact isOpen_interiorCarrier c

theorem frontier_carrier (c : OneSidedCircularCap) :
    frontier c.carrier = arcTrace c ∪ c.chordCarrier := by
  apply Subset.antisymm
  · intro p hp
    have hpc : p ∈ c.carrier :=
      c.isClosed_carrier.frontier_subset hp
    by_cases heq : c.radiusSquaredAt p = c.radius ^ 2
    · exact Or.inl ⟨heq, hpc.2⟩
    have hlt : c.radiusSquaredAt p < c.radius ^ 2 :=
      lt_of_le_of_ne hpc.1 heq
    cases hside : c.side with
    | upper =>
        have hsidep : c.baseY ≤ p.2 := by
          simpa [OneSidedCircularCap.carrier, hside] using hpc.2
        by_cases hy : p.2 = c.baseY
        · exact Or.inr
            (c.mem_chordCarrier_of_mem_carrier_of_eq_base hpc hy)
        · exfalso
          have hi : p ∈ c.interiorCarrier := by
            simpa [OneSidedCircularCap.interiorCarrier, hside] using
              ⟨hlt, lt_of_le_of_ne hsidep (Ne.symm hy)⟩
          exact (mem_frontier_iff_notMem_interior hpc).mp hp
            (interiorCarrier_subset_interior c hi)
    | lower =>
        have hsidep : p.2 ≤ c.baseY := by
          simpa [OneSidedCircularCap.carrier, hside] using hpc.2
        by_cases hy : p.2 = c.baseY
        · exact Or.inr
            (c.mem_chordCarrier_of_mem_carrier_of_eq_base hpc hy)
        · exfalso
          have hi : p ∈ c.interiorCarrier := by
            simpa [OneSidedCircularCap.interiorCarrier, hside] using
              ⟨hlt, lt_of_le_of_ne hsidep hy⟩
          exact (mem_frontier_iff_notMem_interior hpc).mp hp
            (interiorCarrier_subset_interior c hi)
  · rintro p (hp | hp)
    · have hpc : p ∈ c.carrier := ⟨hp.1.le, hp.2⟩
      rw [mem_frontier_iff_notMem_interior hpc]
      intro hi
      apply circle_eq_not_mem_interior_disk
          c.center.1 c.center.2 c.radius c.radius_pos p
          (by simpa [OneSidedCircularCap.radiusSquaredAt] using hp.1)
      apply interior_mono _ hi
      intro q hq
      exact hq.1
    · have hpc := c.chordCarrier_subset_carrier hp
      rw [mem_frontier_iff_notMem_interior hpc]
      intro hi
      cases hside : c.side with
      | upper =>
          apply second_eq_not_mem_interior_ge c.baseY p hp.1
          apply interior_mono _ hi
          intro q hq
          simpa [OneSidedCircularCap.carrier, hside] using hq.2
      | lower =>
          apply second_eq_not_mem_interior_le c.baseY p hp.1
          apply interior_mono _ hi
          intro q hq
          simpa [OneSidedCircularCap.carrier, hside] using hq.2

end OneSidedCircularCap

namespace StripCore

/-- The exact left circular trace of a strip core. -/
def leftArcTrace (c : StripCore) : Set PlanePoint :=
  {p | (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
    p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1}

/-- The exact right circular trace of a strip core. -/
def rightArcTrace (c : StripCore) : Set PlanePoint :=
  {p | (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
    c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1}

def upperChordTrace (c : StripCore) : Set PlanePoint :=
  {p | p.2 = 1 ∧ |p.1| ≤ c.chord / 2}

def lowerChordTrace (c : StripCore) : Set PlanePoint :=
  {p | p.2 = -1 ∧ |p.1| ≤ c.chord / 2}

private theorem radius_mul_curvature (c : StripCore) :
    c.radius * c.curvature = 1 := by
  rw [StripCore.radius]
  field_simp [ne_of_gt c.curvature_pos]

private theorem radius_sq_cos_sq (c : StripCore) :
    (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hrc := radius_mul_curvature c
  nlinarith [sq_nonneg (c.radius * c.curvature - 1)]

private theorem left_interface_circle (c : StripCore) (y : ℝ) :
    ((-c.chord / 2) - c.leftCenterX) ^ 2 + y ^ 2 =
      c.radius ^ 2 - 1 + y ^ 2 := by
  rw [StripCore.leftCenterX]
  have h := radius_sq_cos_sq c
  nlinarith

private theorem right_interface_circle (c : StripCore) (y : ℝ) :
    (c.chord / 2 - c.rightCenterX) ^ 2 + y ^ 2 =
      c.radius ^ 2 - 1 + y ^ 2 := by
  rw [StripCore.rightCenterX]
  rw [show c.chord / 2 - (c.chord / 2 -
      c.radius * cos c.sideAngle) =
      c.radius * cos c.sideAngle by ring, radius_sq_cos_sq c]

theorem isClosed_carrier (c : StripCore) : IsClosed c.carrier := by
  have hx : Continuous (fun p : PlanePoint => p.1) := continuous_fst
  have hy : Continuous (fun p : PlanePoint => p.2) := continuous_snd
  have habsy : Continuous (fun p : PlanePoint => |p.2|) := hy.abs
  have hrect : IsClosed c.rectangleCarrier := by
    rw [StripCore.rectangleCarrier]
    change IsClosed
      ({p : PlanePoint | -c.chord / 2 ≤ p.1} ∩
        ({p : PlanePoint | p.1 ≤ c.chord / 2} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (isClosed_le continuous_const hx).inter
      ((isClosed_le hx continuous_const).inter
        (isClosed_le habsy continuous_const))
  have hleft : IsClosed c.leftCapCarrier := by
    rw [StripCore.leftCapCarrier]
    change IsClosed
      ({p : PlanePoint |
          (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} ∩
        ({p : PlanePoint | p.1 ≤ -c.chord / 2} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (isClosed_le
      (((hx.sub continuous_const).pow 2).add (hy.pow 2))
      continuous_const).inter
        ((isClosed_le hx continuous_const).inter
          (isClosed_le habsy continuous_const))
  have hright : IsClosed c.rightCapCarrier := by
    rw [StripCore.rightCapCarrier]
    change IsClosed
      ({p : PlanePoint |
          (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2} ∩
        ({p : PlanePoint | c.chord / 2 ≤ p.1} ∩
          {p : PlanePoint | |p.2| ≤ 1}))
    exact (isClosed_le
      (((hx.sub continuous_const).pow 2).add (hy.pow 2))
      continuous_const).inter
        ((isClosed_le continuous_const hx).inter
          (isClosed_le habsy continuous_const))
  exact (hrect.union hleft).union hright

private theorem strictRectangle_subset_interior (c : StripCore) :
    {p : PlanePoint | -c.chord / 2 < p.1 ∧
      p.1 < c.chord / 2 ∧ |p.2| < 1} ⊆ interior c.carrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inl (Or.inl ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  · change IsOpen
      ({p : PlanePoint | -c.chord / 2 < p.1} ∩
        ({p : PlanePoint | p.1 < c.chord / 2} ∩
          {p : PlanePoint | |p.2| < 1}))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const))

private theorem strictLeftCap_subset_interior (c : StripCore) :
    {p : PlanePoint |
      (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 ∧
      p.1 < -c.chord / 2 ∧ |p.2| < 1} ⊆ interior c.carrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inl (Or.inr ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  · change IsOpen
      ({p : PlanePoint |
          (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2} ∩
        ({p : PlanePoint | p.1 < -c.chord / 2} ∩
          {p : PlanePoint | |p.2| < 1}))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const))

private theorem strictRightCap_subset_interior (c : StripCore) :
    {p : PlanePoint |
      (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 ∧
      c.chord / 2 < p.1 ∧ |p.2| < 1} ⊆ interior c.carrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inr ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  · change IsOpen
      ({p : PlanePoint |
          (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2} ∩
        ({p : PlanePoint | c.chord / 2 < p.1} ∩
          {p : PlanePoint | |p.2| < 1}))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_snd.abs continuous_const))

private theorem leftInterface_subset_interior (c : StripCore) :
    {p : PlanePoint | p.1 = -c.chord / 2 ∧ |p.2| < 1} ⊆
      interior c.carrier := by
  intro p hp
  have hybounds := (abs_lt.mp hp.2)
  have hysq : p.2 ^ 2 < 1 := by nlinarith
  have hdisk :
      (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 := by
    rw [hp.1, left_interface_circle]
    linarith
  let U : Set PlanePoint :=
    {q | (q.1 - c.leftCenterX) ^ 2 + q.2 ^ 2 < c.radius ^ 2 ∧
      |q.2| < 1 ∧ q.1 < c.chord / 2}
  have hopen : IsOpen U := by
    change IsOpen
      ({q : PlanePoint |
          (q.1 - c.leftCenterX) ^ 2 + q.2 ^ 2 < c.radius ^ 2} ∩
        ({q : PlanePoint | |q.2| < 1} ∩
          {q : PlanePoint | q.1 < c.chord / 2}))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isOpen_lt continuous_snd.abs continuous_const).inter
        (isOpen_lt continuous_fst continuous_const))
  have hsub : U ⊆ c.carrier := by
    intro q hq
    by_cases hx : q.1 ≤ -c.chord / 2
    · exact Or.inl (Or.inr ⟨hq.1.le, hx, hq.2.1.le⟩)
    · exact Or.inl (Or.inl
        ⟨le_of_not_ge hx, hq.2.2.le, hq.2.1.le⟩)
  apply interior_maximal hsub hopen
  exact ⟨hdisk, hp.2, by rw [hp.1]; nlinarith [c.chord_pos]⟩

private theorem rightInterface_subset_interior (c : StripCore) :
    {p : PlanePoint | p.1 = c.chord / 2 ∧ |p.2| < 1} ⊆
      interior c.carrier := by
  intro p hp
  have hybounds := (abs_lt.mp hp.2)
  have hysq : p.2 ^ 2 < 1 := by nlinarith
  have hdisk :
      (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 := by
    rw [hp.1, right_interface_circle]
    linarith
  let U : Set PlanePoint :=
    {q | (q.1 - c.rightCenterX) ^ 2 + q.2 ^ 2 < c.radius ^ 2 ∧
      |q.2| < 1 ∧ -c.chord / 2 < q.1}
  have hopen : IsOpen U := by
    change IsOpen
      ({q : PlanePoint |
          (q.1 - c.rightCenterX) ^ 2 + q.2 ^ 2 < c.radius ^ 2} ∩
        ({q : PlanePoint | |q.2| < 1} ∩
          {q : PlanePoint | -c.chord / 2 < q.1}))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isOpen_lt continuous_snd.abs continuous_const).inter
        (isOpen_lt continuous_const continuous_fst))
  have hsub : U ⊆ c.carrier := by
    intro q hq
    by_cases hx : c.chord / 2 ≤ q.1
    · exact Or.inr ⟨hq.1.le, hx, hq.2.1.le⟩
    · exact Or.inl (Or.inl
        ⟨hq.2.2.le, le_of_not_ge hx, hq.2.1.le⟩)
  apply interior_maximal hsub hopen
  exact ⟨hdisk, hp.2, by rw [hp.1]; nlinarith [c.chord_pos]⟩

private theorem leftCap_circle_eq_of_abs_eq_one (c : StripCore)
    {p : PlanePoint} (hp : p ∈ c.leftCapCarrier) (hy : |p.2| = 1) :
    (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 := by
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hd :
      p.1 - c.leftCenterX ≤ -(c.radius * cos c.sideAngle) := by
    rw [StripCore.leftCenterX]
    linarith [hp.2.1]
  have hdneg : p.1 - c.leftCenterX ≤ 0 := by
    nlinarith [c.radius_pos]
  have hbase : -(c.radius * cos c.sideAngle) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg c.radius_pos.le hcos)
  have hsquare :
      (c.radius * cos c.sideAngle) ^ 2 ≤
        (p.1 - c.leftCenterX) ^ 2 := by
    nlinarith
  have hy2 : p.2 ^ 2 = 1 := by
    nlinarith [sq_abs p.2]
  nlinarith [radius_sq_cos_sq c, hp.1]

private theorem rightCap_circle_eq_of_abs_eq_one (c : StripCore)
    {p : PlanePoint} (hp : p ∈ c.rightCapCarrier) (hy : |p.2| = 1) :
    (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 := by
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hd :
      c.radius * cos c.sideAngle ≤ p.1 - c.rightCenterX := by
    rw [StripCore.rightCenterX]
    linarith [hp.2.1]
  have hdpos : 0 ≤ p.1 - c.rightCenterX := by
    nlinarith [c.radius_pos]
  have hbase : 0 ≤ c.radius * cos c.sideAngle := by
    exact mul_nonneg c.radius_pos.le hcos
  have hsquare :
      (c.radius * cos c.sideAngle) ^ 2 ≤
        (p.1 - c.rightCenterX) ^ 2 := by
    nlinarith
  have hy2 : p.2 ^ 2 = 1 := by
    nlinarith [sq_abs p.2]
  nlinarith [radius_sq_cos_sq c, hp.1]

private theorem leftArc_not_mem_interior (c : StripCore) {p : PlanePoint}
    (hp : p ∈ leftArcTrace c) : p ∉ interior c.carrier := by
  change
    (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1 at hp
  intro hi
  have hn : interior c.carrier ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 - ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with (hrect | hleft) | hright
  · change -c.chord / 2 ≤ p.1 - ε / 2 ∧
      p.1 - ε / 2 ≤ c.chord / 2 ∧ |p.2| ≤ 1 at hrect
    linarith [hp.2.1]
  · have hcenter :
        p.1 - c.leftCenterX ≤ 0 := by
      have hcos : 0 ≤ cos c.sideAngle := by
        rw [c.cos_sideAngle]
        positivity
      rw [StripCore.leftCenterX]
      nlinarith [hp.2.1, c.radius_pos]
    change
      ((p.1 - ε / 2 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤
        c.radius ^ 2) ∧ p.1 - ε / 2 ≤ -c.chord / 2 ∧
        |p.2| ≤ 1 at hleft
    nlinarith [hp.1]
  · change
      ((p.1 - ε / 2 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤
        c.radius ^ 2) ∧ c.chord / 2 ≤ p.1 - ε / 2 ∧
        |p.2| ≤ 1 at hright
    nlinarith [hp.2.1, c.chord_pos]

private theorem rightArc_not_mem_interior (c : StripCore) {p : PlanePoint}
    (hp : p ∈ rightArcTrace c) : p ∉ interior c.carrier := by
  change
    (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1 at hp
  intro hi
  have hn : interior c.carrier ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with (hrect | hleft) | hright
  · change -c.chord / 2 ≤ p.1 + ε / 2 ∧
      p.1 + ε / 2 ≤ c.chord / 2 ∧ |p.2| ≤ 1 at hrect
    linarith [hp.2.1]
  · change
      ((p.1 + ε / 2 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤
        c.radius ^ 2) ∧ p.1 + ε / 2 ≤ -c.chord / 2 ∧
        |p.2| ≤ 1 at hleft
    nlinarith [hp.2.1, c.chord_pos]
  · have hcenter :
        0 ≤ p.1 - c.rightCenterX := by
      have hcos : 0 ≤ cos c.sideAngle := by
        rw [c.cos_sideAngle]
        positivity
      rw [StripCore.rightCenterX]
      nlinarith [hp.2.1, c.radius_pos]
    change
      ((p.1 + ε / 2 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤
        c.radius ^ 2) ∧ c.chord / 2 ≤ p.1 + ε / 2 ∧
        |p.2| ≤ 1 at hright
    nlinarith [hp.1]

theorem frontier_carrier (c : StripCore) :
    frontier c.carrier =
      leftArcTrace c ∪
        (rightArcTrace c ∪ (upperChordTrace c ∪ lowerChordTrace c)) := by
  apply Subset.antisymm
  · intro p hp
    have hpc : p ∈ c.carrier := (isClosed_carrier c).frontier_subset hp
    have hnint : p ∉ interior c.carrier :=
      (mem_frontier_iff_notMem_interior hpc).mp hp
    rcases hpc with (hrect | hleft) | hright
    · change -c.chord / 2 ≤ p.1 ∧ p.1 ≤ c.chord / 2 ∧
        |p.2| ≤ 1 at hrect
      by_cases htop : p.2 = 1
      · exact Or.inr (Or.inr (Or.inl
          ⟨htop, abs_le.mpr
            ⟨by linarith [hrect.1], hrect.2.1⟩⟩))
      by_cases hbottom : p.2 = -1
      · exact Or.inr (Or.inr (Or.inr
          ⟨hbottom, abs_le.mpr
            ⟨by linarith [hrect.1], hrect.2.1⟩⟩))
      have hybounds := abs_le.mp hrect.2.2
      have hylt : |p.2| < 1 := abs_lt.mpr
        ⟨lt_of_le_of_ne hybounds.1 (Ne.symm hbottom),
          lt_of_le_of_ne hybounds.2 htop⟩
      by_cases hxl : p.1 = -c.chord / 2
      · exfalso
        exact hnint (leftInterface_subset_interior c ⟨hxl, hylt⟩)
      by_cases hxr : p.1 = c.chord / 2
      · exfalso
        exact hnint (rightInterface_subset_interior c ⟨hxr, hylt⟩)
      · exfalso
        apply hnint
        exact strictRectangle_subset_interior c
          ⟨lt_of_le_of_ne hrect.1 (Ne.symm hxl),
            lt_of_le_of_ne hrect.2.1 hxr, hylt⟩
    · change
        ((p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2) ∧
          p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1 at hleft
      by_cases heq :
          (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2
      · exact Or.inl ⟨heq, hleft.2⟩
      have hdisk :
          (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 :=
        lt_of_le_of_ne hleft.1 heq
      have hylt : |p.2| < 1 := by
        apply lt_of_le_of_ne hleft.2.2
        intro hone
        exact heq (leftCap_circle_eq_of_abs_eq_one c hleft hone)
      by_cases hx : p.1 = -c.chord / 2
      · exfalso
        exact hnint (leftInterface_subset_interior c ⟨hx, hylt⟩)
      · exfalso
        exact hnint (strictLeftCap_subset_interior c
          ⟨hdisk, lt_of_le_of_ne hleft.2.1 hx, hylt⟩)
    · change
        ((p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2) ∧
          c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1 at hright
      by_cases heq :
          (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2
      · exact Or.inr (Or.inl ⟨heq, hright.2⟩)
      have hdisk :
          (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 < c.radius ^ 2 :=
        lt_of_le_of_ne hright.1 heq
      have hylt : |p.2| < 1 := by
        apply lt_of_le_of_ne hright.2.2
        intro hone
        exact heq (rightCap_circle_eq_of_abs_eq_one c hright hone)
      by_cases hx : p.1 = c.chord / 2
      · exfalso
        exact hnint (rightInterface_subset_interior c ⟨hx, hylt⟩)
      · exfalso
        exact hnint (strictRightCap_subset_interior c
          ⟨hdisk, lt_of_le_of_ne hright.2.1 (Ne.symm hx), hylt⟩)
  · rintro p (hleft | hright | hupper | hlower)
    · have hpc : p ∈ c.carrier :=
        Or.inl (Or.inr ⟨hleft.1.le, hleft.2⟩)
      exact (mem_frontier_iff_notMem_interior hpc).2
        (leftArc_not_mem_interior c hleft)
    · have hpc : p ∈ c.carrier :=
        Or.inr ⟨hright.1.le, hright.2⟩
      exact (mem_frontier_iff_notMem_interior hpc).2
        (rightArc_not_mem_interior c hright)
    · have hpc : p ∈ c.carrier := by
        apply Or.inl
        apply Or.inl
        have hxbounds := abs_le.mp hupper.2
        exact ⟨by linarith [hxbounds.1], hxbounds.2,
          by simp [hupper.1]⟩
      rw [mem_frontier_iff_notMem_interior hpc]
      intro hi
      apply second_eq_not_mem_interior_le 1 p hupper.1
      exact interior_mono (by
        intro q hq
        exact le_trans (le_abs_self q.2) (c.carrier_y_bounds hq)) hi
    · have hpc : p ∈ c.carrier := by
        apply Or.inl
        apply Or.inl
        have hxbounds := abs_le.mp hlower.2
        exact ⟨by linarith [hxbounds.1], hxbounds.2,
          by simp [hlower.1]⟩
      rw [mem_frontier_iff_notMem_interior hpc]
      intro hi
      apply second_eq_not_mem_interior_ge (-1) p hlower.1
      exact interior_mono (by
        intro q hq
        have hneg : -q.2 ≤ 1 :=
          le_trans (neg_le_abs q.2) (c.carrier_y_bounds hq)
        show (-1 : ℝ) ≤ q.2
        linarith) hi

end StripCore
/-- Push one-dimensional Lebesgue measure on a closed interval through a curve. -/
def intervalPushforward (curve : ℝ → PlanePoint) (a b : ℝ) : Measure PlanePoint :=
  Measure.map curve (volume.restrict (Icc a b))

private theorem intervalPushforward_mass
    {curve : ℝ → PlanePoint} {a b : ℝ} (hcurve : Measurable curve) :
    intervalPushforward curve a b Set.univ = ENNReal.ofReal (b - a) := by
  simp [intervalPushforward, Measure.map_apply, hcurve, Real.volume_Icc]

private theorem intervalPushforward_singleton_zero
    {curve : ℝ → PlanePoint} {a b x : ℝ}
    (hcurve : Measurable curve) (hinj : Set.InjOn curve (Icc a b))
    (hx : x ∈ Icc a b) :
    intervalPushforward curve a b {curve x} = 0 := by
  rw [intervalPushforward, Measure.map_apply hcurve (measurableSet_singleton _)]
  rw [Measure.restrict_apply ((measurableSet_singleton _).preimage hcurve)]
  have hset : curve ⁻¹' {curve x} ∩ Icc a b = {x} := by
    ext y
    constructor
    · rintro ⟨hycurve, hy⟩
      have heq : curve y = curve x := by simpa using hycurve
      exact mem_singleton_iff.mpr (hinj hy hx heq)
    · rintro rfl
      exact ⟨by simp, hx⟩
  rw [hset]
  simp

private theorem integral_intervalPushforward
    {curve : ℝ → PlanePoint} {a b : ℝ} (hcurve : Measurable curve)
    {f : PlanePoint → ℝ} (hf : Measurable f) :
    ∫ p, f p ∂intervalPushforward curve a b =
      ∫ s in Icc a b, f (curve s) := by
  rw [intervalPushforward, integral_map hcurve.aemeasurable hf.aestronglyMeasurable]

/-- The strip density is Borel measurable, including at its two interfaces. -/
theorem measurable_stripDensity (lam : ℝ) : Measurable (StripDensity lam) := by
  unfold StripDensity
  exact Measurable.ite (by measurability) measurable_const measurable_const

/-! ## One-sided circular caps -/

/-- The cap arc, parametrized by signed arclength. -/
def capParam (c : OneSidedCircularCap) (s : ℝ) : PlanePoint :=
  c.arcPoint (s / c.radius)

def capStart (c : OneSidedCircularCap) : ℝ := -c.radius * c.theta

def capEnd (c : OneSidedCircularCap) : ℝ := c.radius * c.theta

/-- Explicit regular boundary measure of a one-sided circular arc. -/
def capBoundaryMeasure (c : OneSidedCircularCap) : Measure PlanePoint :=
  intervalPushforward (capParam c) (capStart c) (capEnd c)

private theorem capParam_measurable (c : OneSidedCircularCap) :
    Measurable (capParam c) := by
  apply Continuous.measurable
  unfold capParam OneSidedCircularCap.arcPoint
  split <;> fun_prop

private theorem cap_angle_mem {c : OneSidedCircularCap} {s : ℝ}
    (hs : s ∈ Icc (capStart c) (capEnd c)) :
    s / c.radius ∈ Icc (-c.theta) c.theta := by
  have hr := c.radius_pos
  constructor
  · apply (le_div_iff₀ hr).2
    simpa [capStart, mul_comm] using hs.1
  · apply (div_le_iff₀ hr).2
    simpa [capEnd, mul_comm] using hs.2

private theorem cap_angle_mem_open {c : OneSidedCircularCap} {s : ℝ}
    (hs : s ∈ Ioo (capStart c) (capEnd c)) :
    |s / c.radius| < c.theta := by
  rw [abs_lt]
  have hr := c.radius_pos
  constructor
  · apply (lt_div_iff₀ hr).2
    simpa [capStart, mul_comm] using hs.1
  · apply (div_lt_iff₀ hr).2
    simpa [capEnd, mul_comm] using hs.2

private theorem capParam_injOn (c : OneSidedCircularCap) :
    Set.InjOn (capParam c) (Icc (capStart c) (capEnd c)) := by
  intro s hs t ht hst
  have hang := c.arcPoint_injOn (cap_angle_mem hs) (cap_angle_mem ht) hst
  exact (div_left_inj' (ne_of_gt c.radius_pos)).mp hang

private theorem cap_arcLength_eq (c : OneSidedCircularCap) :
    c.arcLength = capEnd c - capStart c := by
  rw [OneSidedCircularCap.arcLength]
  unfold capEnd capStart OneSidedCircularCap.radius ell
  field_simp [ne_of_gt c.sin_theta_pos]
  <;> ring

@[simp] theorem capParam_start (c : OneSidedCircularCap) :
    capParam c (capStart c) = c.leftEndpoint := by
  have hr : c.radius ≠ 0 := ne_of_gt c.radius_pos
  have hangle : capStart c / c.radius = -c.theta := by
    unfold capStart
    field_simp [hr]
  rw [capParam, hangle, c.arcPoint_left]

@[simp] theorem capParam_end (c : OneSidedCircularCap) :
    capParam c (capEnd c) = c.rightEndpoint := by
  have hr : c.radius ≠ 0 := ne_of_gt c.radius_pos
  have hangle : capEnd c / c.radius = c.theta := by
    unfold capEnd
    field_simp [hr]
  rw [capParam, hangle, c.arcPoint_right]

/-- Total pushforward mass is the geometric arc length. -/
theorem capBoundaryMeasure_mass (c : OneSidedCircularCap) :
    capBoundaryMeasure c Set.univ = ENNReal.ofReal c.arcLength := by
  rw [capBoundaryMeasure, intervalPushforward_mass (capParam_measurable c),
    cap_arcLength_eq c]

/-- Both cap endpoints are null for the regular boundary measure. -/
theorem capBoundaryMeasure_endpoints (c : OneSidedCircularCap) :
    capBoundaryMeasure c {c.leftEndpoint} = 0 ∧
      capBoundaryMeasure c {c.rightEndpoint} = 0 := by
  rw [← capParam_start c, ← capParam_end c]
  constructor
  · apply intervalPushforward_singleton_zero (capParam_measurable c) (capParam_injOn c)
    constructor <;> dsimp [capStart, capEnd] <;>
      nlinarith [c.radius_pos, c.theta_pos]
  · apply intervalPushforward_singleton_zero (capParam_measurable c) (capParam_injOn c)
    constructor <;> dsimp [capStart, capEnd] <;>
      nlinarith [c.radius_pos, c.theta_pos]

/-- The non-endpoint part of an upper cap based on `y = 1` is in the external
(density `lam`) branch. -/
theorem cap_upper_external_density (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .upper) (hbase : c.baseY = 1)
    {s : ℝ} (hs : s ∈ Ioo (capStart c) (capEnd c)) :
    StripDensity lam (capParam c s) = lam := by
  have hopen := c.arcPoint_in_open_side (cap_angle_mem_open hs)
  have hy : 1 < (capParam c s).2 := by
    simpa [capParam, hside, hbase] using hopen
  rw [StripDensity, if_neg]
  exact not_le.mpr (hy.trans_le (le_abs_self _))

/-- The non-endpoint part of a lower cap based on `y = -1` is in the external
(density `lam`) branch. -/
theorem cap_lower_external_density (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .lower) (hbase : c.baseY = -1)
    {s : ℝ} (hs : s ∈ Ioo (capStart c) (capEnd c)) :
    StripDensity lam (capParam c s) = lam := by
  have hopen := c.arcPoint_in_open_side (cap_angle_mem_open hs)
  have hy : (capParam c s).2 < -1 := by
    simpa [capParam, hside, hbase] using hopen
  rw [StripDensity, if_neg]
  apply not_le.mpr
  exact (show 1 < -(capParam c s).2 by linarith).trans_le (neg_le_abs _)

/-- Upper external cap: weighted integral equals `lam` times arc length. -/
theorem cap_upper_weightedIntegral (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .upper) (hbase : c.baseY = 1) :
    ∫ p, StripDensity lam p ∂capBoundaryMeasure c = lam * c.arcLength := by
  rw [capBoundaryMeasure]
  rw [integral_intervalPushforward (capParam_measurable c) (measurable_stripDensity lam)]
  rw [integral_Icc_eq_integral_Ioo]
  calc
    (∫ s in Ioo (capStart c) (capEnd c), StripDensity lam (capParam c s)) =
        ∫ _s in Ioo (capStart c) (capEnd c), lam := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact cap_upper_external_density lam c hside hbase hs
    _ = lam * (capEnd c - capStart c) := by
      have hlen : 0 ≤ capEnd c - capStart c := by
        dsimp [capEnd, capStart]
        nlinarith [c.radius_pos, c.theta_pos]
      simp [max_eq_left hlen, mul_comm]
    _ = lam * c.arcLength := by rw [cap_arcLength_eq c]

/-- Lower external cap: weighted integral equals `lam` times arc length. -/
theorem cap_lower_weightedIntegral (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .lower) (hbase : c.baseY = -1) :
    ∫ p, StripDensity lam p ∂capBoundaryMeasure c = lam * c.arcLength := by
  rw [capBoundaryMeasure]
  rw [integral_intervalPushforward (capParam_measurable c) (measurable_stripDensity lam)]
  rw [integral_Icc_eq_integral_Ioo]
  calc
    (∫ s in Ioo (capStart c) (capEnd c), StripDensity lam (capParam c s)) =
        ∫ _s in Ioo (capStart c) (capEnd c), lam := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact cap_lower_external_density lam c hside hbase hs
    _ = lam * (capEnd c - capStart c) := by
      have hlen : 0 ≤ capEnd c - capStart c := by
        dsimp [capEnd, capStart]
        nlinarith [c.radius_pos, c.theta_pos]
      simp [max_eq_left hlen, mul_comm]
    _ = lam * c.arcLength := by rw [cap_arcLength_eq c]

/-! ## Horizontal segments -/

/-- Unit-speed left-to-right segment parametrization. -/
def segmentParam (seg : HorizontalSegment) (s : ℝ) : PlanePoint :=
  (seg.midpointX + s, seg.baseY)

def segmentStart (seg : HorizontalSegment) : ℝ := -seg.chord / 2

def segmentEnd (seg : HorizontalSegment) : ℝ := seg.chord / 2

/-- Explicit regular boundary measure of a horizontal segment. -/
def segmentBoundaryMeasure (seg : HorizontalSegment) : Measure PlanePoint :=
  intervalPushforward (segmentParam seg) (segmentStart seg) (segmentEnd seg)

private theorem segmentParam_measurable (seg : HorizontalSegment) :
    Measurable (segmentParam seg) := by
  unfold segmentParam
  fun_prop

private theorem segmentParam_injOn (seg : HorizontalSegment) :
    Set.InjOn (segmentParam seg) (Icc (segmentStart seg) (segmentEnd seg)) := by
  intro s _ t _ hst
  have hx := congrArg Prod.fst hst
  simp only [segmentParam] at hx
  linarith

@[simp] theorem segmentParam_start (seg : HorizontalSegment) :
    segmentParam seg (segmentStart seg) = seg.leftEndpoint := by
  unfold segmentParam segmentStart HorizontalSegment.leftEndpoint
  congr 1
  ring

@[simp] theorem segmentParam_end (seg : HorizontalSegment) :
    segmentParam seg (segmentEnd seg) = seg.rightEndpoint := by
  unfold segmentParam segmentEnd HorizontalSegment.rightEndpoint
  congr 1

/-- Total pushforward mass is the segment's Euclidean length. -/
theorem segmentBoundaryMeasure_mass (seg : HorizontalSegment) :
    segmentBoundaryMeasure seg Set.univ = ENNReal.ofReal seg.euclideanLength := by
  rw [segmentBoundaryMeasure, intervalPushforward_mass (segmentParam_measurable seg)]
  congr 1
  unfold segmentStart segmentEnd HorizontalSegment.euclideanLength
  ring

/-- Both segment endpoints are null. -/
theorem segmentBoundaryMeasure_endpoints (seg : HorizontalSegment) :
    segmentBoundaryMeasure seg {seg.leftEndpoint} = 0 ∧
      segmentBoundaryMeasure seg {seg.rightEndpoint} = 0 := by
  rw [← segmentParam_start seg, ← segmentParam_end seg]
  constructor
  · apply intervalPushforward_singleton_zero (segmentParam_measurable seg)
      (segmentParam_injOn seg)
    constructor <;> dsimp [segmentStart, segmentEnd] <;> nlinarith [seg.chord_pos]
  · apply intervalPushforward_singleton_zero (segmentParam_measurable seg)
      (segmentParam_injOn seg)
    constructor <;> dsimp [segmentStart, segmentEnd] <;> nlinarith [seg.chord_pos]

/-- Any horizontal segment on or inside the closed strip has density one. -/
theorem segment_strip_density (lam : ℝ) (seg : HorizontalSegment)
    (hbase : |seg.baseY| ≤ 1) (s : ℝ) :
    StripDensity lam (segmentParam seg s) = 1 := by
  simp [StripDensity, segmentParam, hbase]

/-- Weighted integral of a horizontal segment in the closed strip. -/
theorem segment_weightedIntegral (lam : ℝ) (seg : HorizontalSegment)
    (hbase : |seg.baseY| ≤ 1) :
    ∫ p, StripDensity lam p ∂segmentBoundaryMeasure seg = seg.euclideanLength := by
  rw [segmentBoundaryMeasure]
  rw [integral_intervalPushforward (segmentParam_measurable seg)
    (measurable_stripDensity lam)]
  simp_rw [segment_strip_density lam seg hbase]
  unfold segmentStart segmentEnd HorizontalSegment.euclideanLength
  have horder : -seg.chord / 2 ≤ seg.chord / 2 := by
    nlinarith [seg.chord_pos]
  simp [horder]
  ring

/-! ## Left and right arcs of `StripCore` -/

def coreArcStart (c : StripCore) : ℝ := -c.radius * c.sideAngle

def coreArcEnd (c : StripCore) : ℝ := c.radius * c.sideAngle

/-- Unit-speed parametrization of the left core arc. -/
def leftCoreParam (c : StripCore) (s : ℝ) : PlanePoint :=
  (c.leftCenterX - c.radius * cos (s / c.radius),
    c.radius * sin (s / c.radius))

/-- Unit-speed parametrization of the right core arc. -/
def rightCoreParam (c : StripCore) (s : ℝ) : PlanePoint :=
  (c.rightCenterX + c.radius * cos (s / c.radius),
    c.radius * sin (s / c.radius))

/-- Explicit regular boundary measure of the left core arc. -/
def leftCoreBoundaryMeasure (c : StripCore) : Measure PlanePoint :=
  intervalPushforward (leftCoreParam c) (coreArcStart c) (coreArcEnd c)

/-- Explicit regular boundary measure of the right core arc. -/
def rightCoreBoundaryMeasure (c : StripCore) : Measure PlanePoint :=
  intervalPushforward (rightCoreParam c) (coreArcStart c) (coreArcEnd c)

private theorem leftCoreParam_measurable (c : StripCore) :
    Measurable (leftCoreParam c) := by
  unfold leftCoreParam
  fun_prop

private theorem rightCoreParam_measurable (c : StripCore) :
    Measurable (rightCoreParam c) := by
  unfold rightCoreParam
  fun_prop

private theorem core_radius_mul_curvature (c : StripCore) :
    c.radius * c.curvature = 1 := by
  unfold StripCore.radius
  field_simp [ne_of_gt c.curvature_pos]

private theorem core_angle_mem {c : StripCore} {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    s / c.radius ∈ Icc (-c.sideAngle) c.sideAngle := by
  have hr := c.radius_pos
  constructor
  · apply (le_div_iff₀ hr).2
    simpa [coreArcStart, mul_comm] using hs.1
  · apply (div_le_iff₀ hr).2
    simpa [coreArcEnd, mul_comm] using hs.2

private theorem core_angle_mem_pi_div_two {c : StripCore} {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    s / c.radius ∈ Icc (-(π / 2)) (π / 2) := by
  have hu := core_angle_mem hs
  have hb := c.sideAngle_le_pi_div_two
  exact ⟨(neg_le_neg hb).trans hu.1, hu.2.trans hb⟩

private theorem coreParam_injOn (c : StripCore)
    (curve : ℝ → PlanePoint)
    (hy : ∀ s, (curve s).2 = c.radius * sin (s / c.radius)) :
    Set.InjOn curve (Icc (coreArcStart c) (coreArcEnd c)) := by
  intro s hs t ht hst
  have hcoord := congrArg Prod.snd hst
  rw [hy s, hy t] at hcoord
  have hsin : sin (s / c.radius) = sin (t / c.radius) := by
    nlinarith [c.radius_pos]
  have hang := Real.injOn_sin (core_angle_mem_pi_div_two hs)
    (core_angle_mem_pi_div_two ht) hsin
  exact (div_left_inj' (ne_of_gt c.radius_pos)).mp hang

private theorem leftCoreParam_injOn (c : StripCore) :
    Set.InjOn (leftCoreParam c) (Icc (coreArcStart c) (coreArcEnd c)) := by
  apply coreParam_injOn c
  intro s
  rfl

private theorem rightCoreParam_injOn (c : StripCore) :
    Set.InjOn (rightCoreParam c) (Icc (coreArcStart c) (coreArcEnd c)) := by
  apply coreParam_injOn c
  intro s
  rfl

private theorem core_single_arc_length (c : StripCore) :
    coreArcEnd c - coreArcStart c = 2 * ell c.sideAngle := by
  unfold coreArcEnd coreArcStart StripCore.radius ell
  rw [c.sin_sideAngle]
  field_simp [ne_of_gt c.curvature_pos]
  <;> ring

/-- Each core arc has mass `2 * ell sideAngle`. -/
theorem leftCoreBoundaryMeasure_mass (c : StripCore) :
    leftCoreBoundaryMeasure c Set.univ = ENNReal.ofReal (2 * ell c.sideAngle) := by
  rw [leftCoreBoundaryMeasure,
    intervalPushforward_mass (leftCoreParam_measurable c),
    core_single_arc_length c]

theorem rightCoreBoundaryMeasure_mass (c : StripCore) :
    rightCoreBoundaryMeasure c Set.univ = ENNReal.ofReal (2 * ell c.sideAngle) := by
  rw [rightCoreBoundaryMeasure,
    intervalPushforward_mass (rightCoreParam_measurable c),
    core_single_arc_length c]

private theorem core_start_angle (c : StripCore) :
    coreArcStart c / c.radius = -c.sideAngle := by
  unfold coreArcStart
  field_simp [ne_of_gt c.radius_pos]

private theorem core_end_angle (c : StripCore) :
    coreArcEnd c / c.radius = c.sideAngle := by
  unfold coreArcEnd
  field_simp [ne_of_gt c.radius_pos]

/-- Exact interface endpoints of the left arc. -/
theorem leftCoreParam_start (c : StripCore) :
    leftCoreParam c (coreArcStart c) = (-c.chord / 2, -1) := by
  rw [leftCoreParam, core_start_angle c, cos_neg, sin_neg,
    c.sin_sideAngle]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · unfold StripCore.leftCenterX
    ring
  · calc
      c.radius * -c.curvature = -(c.radius * c.curvature) := by ring
      _ = -1 := by rw [core_radius_mul_curvature c]

theorem leftCoreParam_end (c : StripCore) :
    leftCoreParam c (coreArcEnd c) = (-c.chord / 2, 1) := by
  rw [leftCoreParam, core_end_angle c, c.sin_sideAngle]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · unfold StripCore.leftCenterX
    ring
  · rw [core_radius_mul_curvature c]

theorem rightCoreParam_start (c : StripCore) :
    rightCoreParam c (coreArcStart c) = (c.chord / 2, -1) := by
  rw [rightCoreParam, core_start_angle c, cos_neg, sin_neg,
    c.sin_sideAngle]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · unfold StripCore.rightCenterX
    ring
  · calc
      c.radius * -c.curvature = -(c.radius * c.curvature) := by ring
      _ = -1 := by rw [core_radius_mul_curvature c]

theorem rightCoreParam_end (c : StripCore) :
    rightCoreParam c (coreArcEnd c) = (c.chord / 2, 1) := by
  rw [rightCoreParam, core_end_angle c, c.sin_sideAngle]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · unfold StripCore.rightCenterX
    ring
  · rw [core_radius_mul_curvature c]

/-- All four strip-core interface endpoints have zero mass. -/
theorem coreBoundaryMeasure_endpoints (c : StripCore) :
    leftCoreBoundaryMeasure c {(-c.chord / 2, -1)} = 0 ∧
    leftCoreBoundaryMeasure c {(-c.chord / 2, 1)} = 0 ∧
    rightCoreBoundaryMeasure c {(c.chord / 2, -1)} = 0 ∧
    rightCoreBoundaryMeasure c {(c.chord / 2, 1)} = 0 := by
  rw [← leftCoreParam_start c, ← leftCoreParam_end c,
    ← rightCoreParam_start c, ← rightCoreParam_end c]
  have hstart : coreArcStart c ∈ Icc (coreArcStart c) (coreArcEnd c) := by
    constructor <;> dsimp [coreArcStart, coreArcEnd] <;>
      nlinarith [c.radius_pos, c.sideAngle_pos]
  have hend : coreArcEnd c ∈ Icc (coreArcStart c) (coreArcEnd c) := by
    constructor <;> dsimp [coreArcStart, coreArcEnd] <;>
      nlinarith [c.radius_pos, c.sideAngle_pos]
  exact ⟨intervalPushforward_singleton_zero (leftCoreParam_measurable c)
      (leftCoreParam_injOn c) hstart,
    intervalPushforward_singleton_zero (leftCoreParam_measurable c)
      (leftCoreParam_injOn c) hend,
    intervalPushforward_singleton_zero (rightCoreParam_measurable c)
      (rightCoreParam_injOn c) hstart,
    intervalPushforward_singleton_zero (rightCoreParam_measurable c)
      (rightCoreParam_injOn c) hend⟩

private theorem coreParam_y_bound (c : StripCore) {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    |c.radius * sin (s / c.radius)| ≤ 1 := by
  have hu := core_angle_mem hs
  have habs : |s / c.radius| ≤ c.sideAngle := abs_le.mpr hu
  have hpi : |s / c.radius| ≤ π := by
    linarith [c.sideAngle_le_pi_div_two, Real.pi_pos]
  have hsin : |sin (s / c.radius)| ≤ sin c.sideAngle := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      ((show -(π / 2) ≤ 0 by linarith [Real.pi_pos]).trans (abs_nonneg _))
      c.sideAngle_le_pi_div_two habs
  rw [abs_mul, abs_of_pos c.radius_pos]
  calc
    c.radius * |sin (s / c.radius)| ≤ c.radius * sin c.sideAngle :=
      mul_le_mul_of_nonneg_left hsin c.radius_pos.le
    _ = 1 := by rw [c.sin_sideAngle, core_radius_mul_curvature c]

/-- Both core arcs remain on the density-one branch, endpoints included. -/
theorem leftCore_strip_density (lam : ℝ) (c : StripCore) {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    StripDensity lam (leftCoreParam c s) = 1 := by
  rw [StripDensity, if_pos]
  simpa [leftCoreParam] using coreParam_y_bound c hs

theorem rightCore_strip_density (lam : ℝ) (c : StripCore) {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    StripDensity lam (rightCoreParam c s) = 1 := by
  rw [StripDensity, if_pos]
  simpa [rightCoreParam] using coreParam_y_bound c hs

/-- Weighted integral of the left core arc equals its Euclidean length. -/
theorem leftCore_weightedIntegral (lam : ℝ) (c : StripCore) :
    ∫ p, StripDensity lam p ∂leftCoreBoundaryMeasure c = 2 * ell c.sideAngle := by
  rw [leftCoreBoundaryMeasure]
  rw [integral_intervalPushforward (leftCoreParam_measurable c)
    (measurable_stripDensity lam)]
  calc
    (∫ s in Icc (coreArcStart c) (coreArcEnd c),
        StripDensity lam (leftCoreParam c s)) =
        ∫ _s in Icc (coreArcStart c) (coreArcEnd c), 1 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact leftCore_strip_density lam c hs
    _ = coreArcEnd c - coreArcStart c := by
      have horder : coreArcStart c ≤ coreArcEnd c := by
        dsimp [coreArcStart, coreArcEnd]
        nlinarith [c.radius_pos, c.sideAngle_pos]
      simp [horder]
    _ = 2 * ell c.sideAngle := core_single_arc_length c

/-- Weighted integral of the right core arc equals its Euclidean length. -/
theorem rightCore_weightedIntegral (lam : ℝ) (c : StripCore) :
    ∫ p, StripDensity lam p ∂rightCoreBoundaryMeasure c = 2 * ell c.sideAngle := by
  rw [rightCoreBoundaryMeasure]
  rw [integral_intervalPushforward (rightCoreParam_measurable c)
    (measurable_stripDensity lam)]
  calc
    (∫ s in Icc (coreArcStart c) (coreArcEnd c),
        StripDensity lam (rightCoreParam c s)) =
        ∫ _s in Icc (coreArcStart c) (coreArcEnd c), 1 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact rightCore_strip_density lam c hs
    _ = coreArcEnd c - coreArcStart c := by
      have horder : coreArcStart c ≤ coreArcEnd c := by
        dsimp [coreArcStart, coreArcEnd]
        nlinarith [c.radius_pos, c.sideAngle_pos]
      simp [horder]
    _ = 2 * ell c.sideAngle := core_single_arc_length c

/-- The two arc masses add to the declared strip-core boundary-arc length. -/
theorem coreBoundaryMeasure_total_mass (c : StripCore) :
    leftCoreBoundaryMeasure c Set.univ + rightCoreBoundaryMeasure c Set.univ =
      ENNReal.ofReal c.boundaryArcLength := by
  rw [leftCoreBoundaryMeasure_mass c, rightCoreBoundaryMeasure_mass c,
    StripCore.boundaryArcLength]
  have hell : 0 ≤ ell c.sideAngle := by
    rw [ell, c.sin_sideAngle]
    exact (div_pos c.sideAngle_pos c.curvature_pos).le
  rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hell)
    (mul_nonneg (by norm_num) hell)]
  congr 1
  ring


lemma integral_sqrt_one_sub_sq_from_cos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    (∫ x in cos θ..1, √(1 - x ^ 2)) =
      (θ - sin θ * cos θ) / 2 := by
  have hcomp := intervalIntegral.integral_comp_mul_deriv
    (a := θ) (b := 0) (f := cos) (f' := fun x ↦ -sin x)
    (g := fun x : ℝ ↦ √(1 - x ^ 2))
    (fun x _ ↦ Real.hasDerivAt_cos x)
    (continuous_sin.neg.continuousOn) (by fun_prop)
  simp only [Function.comp_apply, cos_zero] at hcomp
  rw [← hcomp]
  calc
    (∫ x in θ..0, √(1 - cos x ^ 2) * -sin x) =
        ∫ x in θ..0, -(sin x ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp
          have hx' : x ∈ Icc 0 θ := by
            simpa [uIcc, hθ0] using hx
          rw [← Real.sin_eq_sqrt_one_sub_cos_sq]
          · ring
          · exact hx'.1
          · exact hx'.2.trans hθπ
    _ = ∫ x in 0..θ, sin x ^ 2 := by
      rw [intervalIntegral.integral_symm]
      simp
    _ = (θ - sin θ * cos θ) / 2 := by
      rw [integral_sin_sq]
      simp
      ring

lemma integral_semicircle_scaled {r θ : ℝ} (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    (∫ y in r * cos θ..r, 2 * √(r ^ 2 - y ^ 2)) =
      r ^ 2 * (θ - sin θ * cos θ) := by
  have hcomp := intervalIntegral.integral_comp_mul_deriv
    (a := cos θ) (b := 1) (f := fun x : ℝ ↦ r * x) (f' := fun _ ↦ r)
    (g := fun y : ℝ ↦ 2 * √(r ^ 2 - y ^ 2))
    (fun x _ ↦ by simpa using (hasDerivAt_id x).const_mul r)
    continuousOn_const (by fun_prop)
  simp only [Function.comp_apply, mul_one] at hcomp
  rw [← hcomp]
  calc
    (∫ x in cos θ..1, 2 * √(r ^ 2 - (r * x) ^ 2) * r) =
        ∫ x in cos θ..1, (2 * r ^ 2) * √(1 - x ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp
          have hx' : x ∈ Icc (-1 : ℝ) 1 := by
            have hcos : -1 ≤ cos θ := neg_one_le_cos θ
            have hcos' : cos θ ≤ 1 := cos_le_one θ
            have : x ∈ Icc (cos θ) 1 := by
              simpa [uIcc, hcos'] using hx
            exact ⟨hcos.trans this.1, this.2⟩
          have hnonneg : 0 ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
          rw [show r ^ 2 - (r * x) ^ 2 = r ^ 2 * (1 - x ^ 2) by ring,
            Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
          ring
    _ = (2 * r ^ 2) * (∫ x in cos θ..1, √(1 - x ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = r ^ 2 * (θ - sin θ * cos θ) := by
      rw [integral_sqrt_one_sub_sq_from_cos hθ0 hθπ]
      ring

lemma integral_semicircle_translated {a r θ : ℝ} (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    (∫ y in a + r * cos θ..a + r, 2 * √(r ^ 2 - (y - a) ^ 2)) =
      r ^ 2 * (θ - sin θ * cos θ) := by
  rw [← intervalIntegral.integral_comp_add_left
    (f := fun y : ℝ ↦ 2 * √(r ^ 2 - (y - a) ^ 2)) a]
  simp only [add_sub_cancel_left]
  exact integral_semicircle_scaled hr hθ0 hθπ

lemma lintegral_semicircle_translated {a r θ : ℝ} (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    (∫⁻ y in Icc (a + r * cos θ) (a + r),
        ENNReal.ofReal (2 * √(r ^ 2 - (y - a) ^ 2))) =
      ENNReal.ofReal (r ^ 2 * (θ - sin θ * cos θ)) := by
  have hcos : cos θ ≤ 1 := cos_le_one θ
  have hab : a + r * cos θ ≤ a + r := by nlinarith
  have hcont : Continuous (fun y : ℝ ↦ 2 * √(r ^ 2 - (y - a) ^ 2)) := by
    fun_prop
  have hint :
      IntegrableOn (fun y : ℝ ↦ 2 * √(r ^ 2 - (y - a) ^ 2))
        (Icc (a + r * cos θ) (a + r)) :=
    hcont.integrableOn_Icc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ ↦ by positivity)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_semicircle_translated hr hθ0 hθπ

lemma volume_upper_circular_segment (mx cy r θ : ℝ) (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    volume {p : ℝ × ℝ |
        (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
          cy + r * cos θ ≤ p.2} =
      ENNReal.ofReal (r ^ 2 * (θ - sin θ * cos θ)) := by
  let S : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Icc (cy + r * cos θ) (cy + r) ∧
      p.2 ∈ Icc
        (mx - √(r ^ 2 - (p.1 - cy) ^ 2))
        (mx + √(r ^ 2 - (p.1 - cy) ^ 2))}
  have hS : MeasurableSet S := by
    exact measurableSet_region_between_cc
      (f := fun y : ℝ ↦ mx - √(r ^ 2 - (y - cy) ^ 2))
      (g := fun y : ℝ ↦ mx + √(r ^ 2 - (y - cy) ^ 2))
      (s := Icc (cy + r * cos θ) (cy + r))
      (by fun_prop) (by fun_prop) measurableSet_Icc
  have hpre :
      Prod.swap ⁻¹' S =
        {p : ℝ × ℝ |
          (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
            cy + r * cos θ ≤ p.2} := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hy, hx⟩
      change p.2 ∈ Icc (cy + r * cos θ) (cy + r) at hy
      change p.1 ∈ Icc
        (mx - √(r ^ 2 - (p.2 - cy) ^ 2))
        (mx + √(r ^ 2 - (p.2 - cy) ^ 2)) at hx
      have hcosmul : -r ≤ r * cos θ := by
        simpa using mul_le_mul_of_nonneg_left (neg_one_le_cos θ) hr.le
      have hymin : cy - r ≤ p.2 := by
        linarith [hy.1]
      have hprod :
          0 ≤ (r - (p.2 - cy)) * (r + (p.2 - cy)) :=
        mul_nonneg (by linarith [hy.2]) (by linarith)
      have hD : 0 ≤ r ^ 2 - (p.2 - cy) ^ 2 := by
        nlinarith
      have hsqrt :
          (√(r ^ 2 - (p.2 - cy) ^ 2)) ^ 2 =
            r ^ 2 - (p.2 - cy) ^ 2 :=
        Real.sq_sqrt hD
      have hxl :
          -(√(r ^ 2 - (p.2 - cy) ^ 2)) ≤ p.1 - mx := by
        linarith [hx.1]
      have hxu :
          p.1 - mx ≤ √(r ^ 2 - (p.2 - cy) ^ 2) := by
        linarith [hx.2]
      have hxprod :
          0 ≤ (√(r ^ 2 - (p.2 - cy) ^ 2) - (p.1 - mx)) *
            (√(r ^ 2 - (p.2 - cy) ^ 2) + (p.1 - mx)) :=
        mul_nonneg (by linarith [hxu]) (by linarith [hxl])
      constructor
      · nlinarith
      · exact hy.1
    · rintro ⟨hcircle, hbase⟩
      have hyUpper : p.2 ≤ cy + r := by
        nlinarith [sq_nonneg (p.1 - mx), sq_nonneg (p.2 - cy + r)]
      have hD : 0 ≤ r ^ 2 - (p.2 - cy) ^ 2 := by
        nlinarith [sq_nonneg (p.1 - mx)]
      have hsqrt :
          (√(r ^ 2 - (p.2 - cy) ^ 2)) ^ 2 =
            r ^ 2 - (p.2 - cy) ^ 2 :=
        Real.sq_sqrt hD
      have hsqrt0 : 0 ≤ √(r ^ 2 - (p.2 - cy) ^ 2) :=
        Real.sqrt_nonneg _
      have hdist :
          (p.1 - mx) ^ 2 ≤ (√(r ^ 2 - (p.2 - cy) ^ 2)) ^ 2 := by
        nlinarith
      change p.2 ∈ Icc (cy + r * cos θ) (cy + r) ∧
        p.1 ∈ Icc
          (mx - √(r ^ 2 - (p.2 - cy) ^ 2))
          (mx + √(r ^ 2 - (p.2 - cy) ^ 2))
      constructor
      · exact ⟨hbase, hyUpper⟩
      · constructor <;> nlinarith
  have hsec (y : ℝ) :
      volume (Prod.mk y ⁻¹' S) =
        (Icc (cy + r * cos θ) (cy + r)).indicator
          (fun y ↦ ENNReal.ofReal
            (2 * √(r ^ 2 - (y - cy) ^ 2))) y := by
    by_cases hy : y ∈ Icc (cy + r * cos θ) (cy + r)
    · simp only [Set.indicator_of_mem hy]
      have heq :
          Prod.mk y ⁻¹' S =
            Icc (mx - √(r ^ 2 - (y - cy) ^ 2))
              (mx + √(r ^ 2 - (y - cy) ^ 2)) := by
        ext x
        change (y ∈ Icc (cy + r * cos θ) (cy + r) ∧
          x ∈ Icc (mx - √(r ^ 2 - (y - cy) ^ 2))
            (mx + √(r ^ 2 - (y - cy) ^ 2))) ↔
          x ∈ Icc (mx - √(r ^ 2 - (y - cy) ^ 2))
            (mx + √(r ^ 2 - (y - cy) ^ 2))
        simp only [hy, true_and]
      rw [heq, Real.volume_Icc]
      congr 1
      ring
    · simp only [Set.indicator_of_notMem hy]
      have heq : Prod.mk y ⁻¹' S = ∅ := by
        ext x
        change (y ∈ Icc (cy + r * cos θ) (cy + r) ∧
          x ∈ Icc (mx - √(r ^ 2 - (y - cy) ^ 2))
            (mx + √(r ^ 2 - (y - cy) ^ 2))) ↔ False
        constructor
        · intro h
          exact (hy h.1).elim
        · intro h
          exact h.elim
      rw [heq, measure_empty]
  calc
    volume {p : ℝ × ℝ |
        (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
          cy + r * cos θ ≤ p.2} =
        volume (Prod.swap ⁻¹' S) := by rw [hpre]
    _ = volume S := by
      exact Measure.measurePreserving_swap.measure_preimage hS.nullMeasurableSet
    _ = ∫⁻ y in Icc (cy + r * cos θ) (cy + r),
        ENNReal.ofReal (2 * √(r ^ 2 - (y - cy) ^ 2)) := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hS]
      simp_rw [hsec]
      rw [lintegral_indicator measurableSet_Icc]
    _ = ENNReal.ofReal (r ^ 2 * (θ - sin θ * cos θ)) :=
      lintegral_semicircle_translated hr hθ0 hθπ

lemma volume_lower_circular_segment (mx cy r θ : ℝ) (hr : 0 < r)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    volume {p : ℝ × ℝ |
        (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
          p.2 ≤ cy - r * cos θ} =
      ENNReal.ofReal (r ^ 2 * (θ - sin θ * cos θ)) := by
  let U : Set (ℝ × ℝ) :=
    {p | (p.1 - mx) ^ 2 + (p.2 - (-cy)) ^ 2 ≤ r ^ 2 ∧
      -cy + r * cos θ ≤ p.2}
  have hU : MeasurableSet U := by
    have hcircle : Measurable (fun p : ℝ × ℝ ↦
        (p.1 - mx) ^ 2 + (p.2 - (-cy)) ^ 2) := by fun_prop
    have hside : Measurable (fun p : ℝ × ℝ ↦ p.2) := measurable_snd
    exact (measurableSet_le hcircle measurable_const).inter
      (measurableSet_le measurable_const hside)
  let F : ℝ × ℝ → ℝ × ℝ := Prod.map id (fun y : ℝ ↦ -y)
  have hF :
      MeasurePreserving F (volume : Measure (ℝ × ℝ)) volume := by
    change MeasurePreserving (Prod.map id (fun y : ℝ ↦ -y))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpre :
      F ⁻¹' U =
        {p : ℝ × ℝ |
          (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
            p.2 ≤ cy - r * cos θ} := by
    ext p
    change ((p.1 - mx) ^ 2 + (-p.2 - -cy) ^ 2 ≤ r ^ 2 ∧
      -cy + r * cos θ ≤ -p.2) ↔
      ((p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
        p.2 ≤ cy - r * cos θ)
    constructor <;> rintro ⟨hcircle, hside⟩
    · constructor
      · nlinarith
      · linarith
    · constructor
      · nlinarith
      · linarith
  calc
    volume {p : ℝ × ℝ |
        (p.1 - mx) ^ 2 + (p.2 - cy) ^ 2 ≤ r ^ 2 ∧
          p.2 ≤ cy - r * cos θ} =
        volume (F ⁻¹' U) := by rw [hpre]
    _ = volume U := hF.measure_preimage hU.nullMeasurableSet
    _ = ENNReal.ofReal (r ^ 2 * (θ - sin θ * cos θ)) :=
      volume_upper_circular_segment mx (-cy) r θ hr hθ0 hθπ


namespace OneSidedCircularCap

theorem volume_carrier (c : OneSidedCircularCap) :
    volume c.carrier = ENNReal.ofReal c.euclideanArea := by
  have hreal :
      c.radius ^ 2 * (c.theta - sin c.theta * cos c.theta) =
        c.euclideanArea := by
    rw [euclideanArea, area, radius]
    field_simp [ne_of_gt c.sin_theta_pos]
    ring
  cases hside : c.side with
  | upper =>
      calc
        volume c.carrier =
            ENNReal.ofReal
              (c.radius ^ 2 *
                (c.theta - sin c.theta * cos c.theta)) := by
          simpa [carrier, radiusSquaredAt, center, hside] using
            volume_upper_circular_segment c.midpointX
              (c.baseY - c.radius * cos c.theta) c.radius c.theta
              c.radius_pos c.theta_pos.le c.theta_lt_pi.le
        _ = ENNReal.ofReal c.euclideanArea := congrArg ENNReal.ofReal hreal
  | lower =>
      calc
        volume c.carrier =
            ENNReal.ofReal
              (c.radius ^ 2 *
                (c.theta - sin c.theta * cos c.theta)) := by
          simpa [carrier, radiusSquaredAt, center, hside] using
            volume_lower_circular_segment c.midpointX
              (c.baseY + c.radius * cos c.theta) c.radius c.theta
              c.radius_pos c.theta_pos.le c.theta_lt_pi.le
        _ = ENNReal.ofReal c.euclideanArea := congrArg ENNReal.ofReal hreal

end OneSidedCircularCap
lemma volume_horizontalLine (b : ℝ) :
    volume {p : PlanePoint | p.2 = b} = 0 := by
  have hset : {p : PlanePoint | p.2 = b} = Set.univ ×ˢ ({b} : Set ℝ) := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
  simp

lemma volume_verticalLine (a : ℝ) :
    volume {p : PlanePoint | p.1 = a} = 0 := by
  have hset : {p : PlanePoint | p.1 = a} = ({a} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
  simp

namespace StripCore

private lemma radius_mul_curvature' (c : StripCore) :
    c.radius * c.curvature = 1 := by
  rw [radius]
  field_simp [ne_of_gt c.curvature_pos]

private lemma radius_sq_cos_sq' (c : StripCore) :
    (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hrc := radius_mul_curvature' c
  nlinarith [sq_nonneg (c.radius * c.curvature - 1)]

lemma volume_rectangleCarrier (c : StripCore) :
    volume c.rectangleCarrier = ENNReal.ofReal (2 * c.chord) := by
  have hset : c.rectangleCarrier =
      Icc (-c.chord / 2) (c.chord / 2) ×ˢ Icc (-1 : ℝ) 1 := by
    ext p
    simp only [rectangleCarrier, mem_setOf_eq, mem_prod, mem_Icc]
    constructor
    · rintro ⟨hx1, hx2, hy⟩
      exact ⟨⟨hx1, hx2⟩, abs_le.mp hy⟩
    · rintro ⟨⟨hx1, hx2⟩, hy1, hy2⟩
      exact ⟨hx1, hx2, abs_le.mpr ⟨hy1, hy2⟩⟩
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc,
    show c.chord / 2 - -c.chord / 2 = c.chord by ring]
  norm_num [ENNReal.ofReal_mul, c.chord_pos.le, mul_comm]

lemma volume_leftCapCarrier (c : StripCore) :
    volume c.leftCapCarrier = ENNReal.ofReal (4 * area c.sideAngle) := by
  let U : Set PlanePoint :=
    {p | (p.1 - 0) ^ 2 + (p.2 - c.leftCenterX) ^ 2 ≤ c.radius ^ 2 ∧
      p.2 ≤ c.leftCenterX - c.radius * cos c.sideAngle}
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hpre : Prod.swap ⁻¹' U = c.leftCapCarrier := by
    ext p
    change ((p.2 - 0) ^ 2 + (p.1 - c.leftCenterX) ^ 2 ≤ c.radius ^ 2 ∧
        p.1 ≤ c.leftCenterX - c.radius * cos c.sideAngle) ↔
      ((p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2 ∧
        p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1)
    have hbase : c.leftCenterX - c.radius * cos c.sideAngle = -c.chord / 2 := by
      rw [leftCenterX]
      ring
    rw [hbase]
    constructor
    · rintro ⟨hdisk, hx⟩
      have hdx : p.1 - c.leftCenterX ≤ -(c.radius * cos c.sideAngle) := by
        rw [leftCenterX]
        linarith
      have hdx0 : p.1 - c.leftCenterX ≤ 0 := by
        nlinarith [c.radius_pos]
      have hsquare : (c.radius * cos c.sideAngle) ^ 2 ≤
          (p.1 - c.leftCenterX) ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (mul_nonneg c.radius_pos.le hcos), abs_of_nonpos hdx0]
        linarith
      have hy2 : p.2 ^ 2 ≤ 1 := by
        nlinarith [radius_sq_cos_sq' c]
      have hyabs : |p.2| ≤ |(1 : ℝ)| := sq_le_sq.mp (by simpa using hy2)
      exact ⟨by nlinarith, hx, by simpa using hyabs⟩
    · rintro ⟨hdisk, hx, _hy⟩
      exact ⟨by nlinarith, hx⟩
  have hU : MeasurableSet U := by
    change MeasurableSet
      ({p : PlanePoint |
          (p.1 - 0) ^ 2 + (p.2 - c.leftCenterX) ^ 2 ≤ c.radius ^ 2} ∩
        {p : PlanePoint |
          p.2 ≤ c.leftCenterX - c.radius * cos c.sideAngle})
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet.inter
      (isClosed_le continuous_snd continuous_const).measurableSet
  have hmeasure : volume c.leftCapCarrier = volume U := by
    rw [← hpre]
    exact Measure.measurePreserving_swap.measure_preimage hU.nullMeasurableSet
  have hreal : c.radius ^ 2 *
      (c.sideAngle - sin c.sideAngle * cos c.sideAngle) =
      4 * area c.sideAngle := by
    rw [area]
    have hs : sin c.sideAngle = c.curvature := c.sin_sideAngle
    rw [hs]
    rw [radius]
    field_simp [ne_of_gt c.curvature_pos]
  calc
    volume c.leftCapCarrier = volume U := hmeasure
    _ = ENNReal.ofReal (c.radius ^ 2 *
        (c.sideAngle - sin c.sideAngle * cos c.sideAngle)) := by
      simpa [U] using volume_lower_circular_segment 0 c.leftCenterX
        c.radius c.sideAngle c.radius_pos c.sideAngle_pos.le c.sideAngle_lt_pi.le
    _ = ENNReal.ofReal (4 * area c.sideAngle) := congrArg ENNReal.ofReal hreal

lemma volume_rightCapCarrier (c : StripCore) :
    volume c.rightCapCarrier = ENNReal.ofReal (4 * area c.sideAngle) := by
  let U : Set PlanePoint :=
    {p | (p.1 - 0) ^ 2 + (p.2 - c.rightCenterX) ^ 2 ≤ c.radius ^ 2 ∧
      c.rightCenterX + c.radius * cos c.sideAngle ≤ p.2}
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hpre : Prod.swap ⁻¹' U = c.rightCapCarrier := by
    ext p
    change ((p.2 - 0) ^ 2 + (p.1 - c.rightCenterX) ^ 2 ≤ c.radius ^ 2 ∧
        c.rightCenterX + c.radius * cos c.sideAngle ≤ p.1) ↔
      ((p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 ≤ c.radius ^ 2 ∧
        c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1)
    have hbase : c.rightCenterX + c.radius * cos c.sideAngle = c.chord / 2 := by
      rw [rightCenterX]
      ring
    rw [hbase]
    constructor
    · rintro ⟨hdisk, hx⟩
      have hdx : c.radius * cos c.sideAngle ≤ p.1 - c.rightCenterX := by
        rw [rightCenterX]
        linarith
      have hdx0 : 0 ≤ p.1 - c.rightCenterX := by
        nlinarith [c.radius_pos]
      have hsquare : (c.radius * cos c.sideAngle) ^ 2 ≤
          (p.1 - c.rightCenterX) ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (mul_nonneg c.radius_pos.le hcos), abs_of_nonneg hdx0]
        exact hdx
      have hy2 : p.2 ^ 2 ≤ 1 := by
        nlinarith [radius_sq_cos_sq' c]
      have hyabs : |p.2| ≤ |(1 : ℝ)| := sq_le_sq.mp (by simpa using hy2)
      exact ⟨by nlinarith, hx, by simpa using hyabs⟩
    · rintro ⟨hdisk, hx, _hy⟩
      exact ⟨by nlinarith, hx⟩
  have hU : MeasurableSet U := by
    change MeasurableSet
      ({p : PlanePoint |
          (p.1 - 0) ^ 2 + (p.2 - c.rightCenterX) ^ 2 ≤ c.radius ^ 2} ∩
        {p : PlanePoint |
          c.rightCenterX + c.radius * cos c.sideAngle ≤ p.2})
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet.inter
      (isClosed_le continuous_const continuous_snd).measurableSet
  have hmeasure : volume c.rightCapCarrier = volume U := by
    rw [← hpre]
    exact Measure.measurePreserving_swap.measure_preimage hU.nullMeasurableSet
  have hreal : c.radius ^ 2 *
      (c.sideAngle - sin c.sideAngle * cos c.sideAngle) =
      4 * area c.sideAngle := by
    rw [area]
    have hs : sin c.sideAngle = c.curvature := c.sin_sideAngle
    rw [hs]
    rw [radius]
    field_simp [ne_of_gt c.curvature_pos]
  calc
    volume c.rightCapCarrier = volume U := hmeasure
    _ = ENNReal.ofReal (c.radius ^ 2 *
        (c.sideAngle - sin c.sideAngle * cos c.sideAngle)) := by
      simpa [U] using volume_upper_circular_segment 0 c.rightCenterX
        c.radius c.sideAngle c.radius_pos c.sideAngle_pos.le c.sideAngle_lt_pi.le
    _ = ENNReal.ofReal (4 * area c.sideAngle) := congrArg ENNReal.ofReal hreal

lemma volume_carrier (c : StripCore) :
    volume c.carrier = ENNReal.ofReal c.euclideanArea := by
  have hrectLeft : AEDisjoint volume c.rectangleCarrier c.leftCapCarrier := by
    refine measure_mono_null ?_ (volume_verticalLine (-c.chord / 2))
    rintro p ⟨hrect, hleft⟩
    exact le_antisymm hleft.2.1 hrect.1
  have hfirstRight : AEDisjoint volume
      (c.rectangleCarrier ∪ c.leftCapCarrier) c.rightCapCarrier := by
    refine measure_mono_null ?_ (volume_verticalLine (c.chord / 2))
    rintro p ⟨hfirst, hright⟩
    rcases hfirst with hrect | hleft
    · exact le_antisymm hrect.2.1 hright.2.1
    · exfalso
      nlinarith [hleft.2.1, hright.2.1, c.chord_pos]
  have hleftMeas : MeasurableSet c.leftCapCarrier := by
    rw [leftCapCarrier]
    exact ((isClosed_le
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le continuous_snd.abs continuous_const))).measurableSet
  have hrightMeas : MeasurableSet c.rightCapCarrier := by
    rw [rightCapCarrier]
    exact ((isClosed_le
      (((continuous_fst.sub continuous_const).pow 2).add
        (continuous_snd.pow 2)) continuous_const).inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_snd.abs continuous_const))).measurableSet
  rw [carrier, measure_union₀ hrightMeas.nullMeasurableSet hfirstRight,
    measure_union₀ hleftMeas.nullMeasurableSet hrectLeft,
    volume_rectangleCarrier, volume_leftCapCarrier, volume_rightCapCarrier]
  have hq : 0 ≤ 2 * c.chord := mul_nonneg (by norm_num) c.chord_pos.le
  have ha : 0 ≤ 4 * area c.sideAngle := by
    exact mul_nonneg (by norm_num) (area_pos c.sideAngle_pos c.sideAngle_lt_pi).le
  rw [← ENNReal.ofReal_add hq ha, ← ENNReal.ofReal_add (add_nonneg hq ha) ha]
  congr 1
  rw [euclideanArea]
  ring

end StripCore

lemma stripDensity_integrable_intervalPushforward (lam : ℝ)
    {curve : ℝ → PlanePoint} {a b : ℝ} (hcurve : Measurable curve) :
    Integrable (StripDensity lam) (intervalPushforward curve a b) := by
  rw [intervalPushforward, integrable_map_measure
    (measurable_stripDensity lam).aestronglyMeasurable hcurve.aemeasurable]
  apply Measure.integrableOn_of_bounded (M := 1 + |lam|)
      measure_Icc_lt_top.ne
  · exact ((measurable_stripDensity lam).comp hcurve).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    change |StripDensity lam (curve x)| ≤ 1 + |lam|
    unfold StripDensity
    split_ifs
    · simp only [abs_one]
      nlinarith [abs_nonneg lam]
    · nlinarith [abs_nonneg lam]

lemma capBoundaryMeasure_integrable (lam : ℝ) (c : OneSidedCircularCap) :
    Integrable (StripDensity lam) (capBoundaryMeasure c) := by
  rw [capBoundaryMeasure]
  exact stripDensity_integrable_intervalPushforward lam (by
    apply Continuous.measurable
    unfold capParam OneSidedCircularCap.arcPoint
    split <;> fun_prop)

lemma segmentBoundaryMeasure_integrable (lam : ℝ) (seg : HorizontalSegment) :
    Integrable (StripDensity lam) (segmentBoundaryMeasure seg) := by
  rw [segmentBoundaryMeasure]
  exact stripDensity_integrable_intervalPushforward lam (by
    unfold segmentParam
    fun_prop)

lemma leftCoreBoundaryMeasure_integrable (lam : ℝ) (c : StripCore) :
    Integrable (StripDensity lam) (leftCoreBoundaryMeasure c) := by
  rw [leftCoreBoundaryMeasure]
  exact stripDensity_integrable_intervalPushforward lam (by
    unfold leftCoreParam
    fun_prop)

lemma rightCoreBoundaryMeasure_integrable (lam : ℝ) (c : StripCore) :
    Integrable (StripDensity lam) (rightCoreBoundaryMeasure c) := by
  rw [rightCoreBoundaryMeasure]
  exact stripDensity_integrable_intervalPushforward lam (by
    unfold rightCoreParam
    fun_prop)

lemma stripDensity_integrableOn_of_volume_ne_top (lam : ℝ)
    {s : Set PlanePoint} (hs : volume s ≠ ⊤) :
    IntegrableOn (StripDensity lam) s := by
  apply Measure.integrableOn_of_bounded (M := 1 + |lam|) hs
  · exact (measurable_stripDensity lam).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro p
    change |StripDensity lam p| ≤ 1 + |lam|
    unfold StripDensity
    split_ifs
    · simp only [abs_one]
      nlinarith [abs_nonneg lam]
    · nlinarith [abs_nonneg lam]

lemma cap_integrableOn (lam : ℝ) (c : OneSidedCircularCap) :
    IntegrableOn (StripDensity lam) c.carrier := by
  apply stripDensity_integrableOn_of_volume_ne_top
  rw [c.volume_carrier]
  exact ENNReal.ofReal_ne_top

lemma core_integrableOn (lam : ℝ) (c : StripCore) :
    IntegrableOn (StripDensity lam) c.carrier := by
  apply stripDensity_integrableOn_of_volume_ne_top
  rw [c.volume_carrier]
  exact ENNReal.ofReal_ne_top

lemma StripCore.weightedArea_formula (lam : ℝ) (c : StripCore) :
    WeightedArea lam c.carrier = c.euclideanArea := by
  rw [WeightedArea]
  calc
    (∫ p in c.carrier, StripDensity lam p) =
        ∫ _p in c.carrier, (1 : ℝ) := by
      apply setIntegral_congr_fun c.measurableSet_carrier
      intro p hp
      rw [StripDensity, if_pos (c.carrier_y_bounds hp)]
    _ = c.euclideanArea := by
      have ha : 0 ≤ c.euclideanArea := by
        rw [StripCore.euclideanArea]
        exact add_nonneg (mul_nonneg (by norm_num) c.chord_pos.le)
          (mul_nonneg (by norm_num)
            (area_pos c.sideAngle_pos c.sideAngle_lt_pi).le)
      rw [integral_const, measureReal_restrict_apply_univ,
        Measure.real, c.volume_carrier, ENNReal.toReal_ofReal ha]
      simp

lemma cap_upper_weightedArea (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .upper) (hbase : c.baseY = 1) :
    WeightedArea lam c.carrier = lam * c.euclideanArea := by
  have hne : ∀ᵐ p : PlanePoint ∂volume, p.2 ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using volume_horizontalLine 1
  rw [WeightedArea]
  calc
    (∫ p in c.carrier, StripDensity lam p) =
        ∫ _p in c.carrier, lam := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.measurableSet_carrier,
        ae_restrict_of_ae hne] with p hp hpne
      have hpge : (1 : ℝ) ≤ p.2 := by
        simpa [OneSidedCircularCap.carrier, hside, hbase] using hp.2
      have hpgt : (1 : ℝ) < p.2 := lt_of_le_of_ne hpge (Ne.symm hpne)
      rw [StripDensity, if_neg]
      exact not_le.mpr (hpgt.trans_le (le_abs_self p.2))
    _ = lam * c.euclideanArea := by
      rw [integral_const, measureReal_restrict_apply_univ]
      have hvolume : volume.real c.carrier = c.euclideanArea := by
        rw [Measure.real, c.volume_carrier,
          ENNReal.toReal_ofReal c.euclideanArea_pos.le]
      rw [hvolume]
      ring

lemma cap_lower_weightedArea (lam : ℝ) (c : OneSidedCircularCap)
    (hside : c.side = .lower) (hbase : c.baseY = -1) :
    WeightedArea lam c.carrier = lam * c.euclideanArea := by
  have hne : ∀ᵐ p : PlanePoint ∂volume, p.2 ≠ -1 := by
    rw [ae_iff]
    simpa only [not_not] using volume_horizontalLine (-1)
  rw [WeightedArea]
  calc
    (∫ p in c.carrier, StripDensity lam p) =
        ∫ _p in c.carrier, lam := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem c.measurableSet_carrier,
        ae_restrict_of_ae hne] with p hp hpne
      have hple : p.2 ≤ (-1 : ℝ) := by
        simpa [OneSidedCircularCap.carrier, hside, hbase] using hp.2
      have hplt : p.2 < (-1 : ℝ) := lt_of_le_of_ne hple hpne
      rw [StripDensity, if_neg]
      apply not_le.mpr
      exact (show 1 < -p.2 by linarith).trans_le (neg_le_abs p.2)
    _ = lam * c.euclideanArea := by
      rw [integral_const, measureReal_restrict_apply_univ]
      have hvolume : volume.real c.carrier = c.euclideanArea := by
        rw [Measure.real, c.volume_carrier,
          ENNReal.toReal_ofReal c.euclideanArea_pos.le]
      rw [hvolume]
      ring


/-- The coordinate four-arc assembly: two side arcs from the strip core and two
congruent reflected exterior caps. -/
theorem intervalPushforward_singleton_zero_of_injOn
    {curve : ℝ → PlanePoint} {a b : ℝ} (hcurve : Measurable curve)
    (hinj : Set.InjOn curve (Icc a b)) (p : PlanePoint) :
    intervalPushforward curve a b {p} = 0 := by
  rw [intervalPushforward, Measure.map_apply hcurve (measurableSet_singleton p)]
  rw [Measure.restrict_apply ((measurableSet_singleton p).preimage hcurve)]
  have hsub : (curve ⁻¹' {p} ∩ Icc a b).Subsingleton := by
    intro x hx y hy
    apply hinj hx.2 hy.2
    have hxp : curve x = p := by simpa using hx.1
    have hyp : curve y = p := by simpa using hy.1
    exact hxp.trans hyp.symm
  exact hsub.measure_zero volume

private lemma cap_angle_mem_public {c : OneSidedCircularCap} {s : ℝ}
    (hs : s ∈ Icc (capStart c) (capEnd c)) :
    s / c.radius ∈ Icc (-c.theta) c.theta := by
  have hr := c.radius_pos
  constructor
  · apply (le_div_iff₀ hr).2
    simpa [capStart, mul_comm] using hs.1
  · apply (div_le_iff₀ hr).2
    simpa [capEnd, mul_comm] using hs.2

private lemma capParam_injOn_public (c : OneSidedCircularCap) :
    Set.InjOn (capParam c) (Icc (capStart c) (capEnd c)) := by
  intro s hs t ht hst
  have hang := c.arcPoint_injOn
    (cap_angle_mem_public hs) (cap_angle_mem_public ht) hst
  exact (div_left_inj' (ne_of_gt c.radius_pos)).mp hang

theorem capBoundaryMeasure_singleton_zero (c : OneSidedCircularCap)
    (p : PlanePoint) : capBoundaryMeasure c {p} = 0 := by
  rw [capBoundaryMeasure]
  apply intervalPushforward_singleton_zero_of_injOn
  · apply Continuous.measurable
    unfold capParam OneSidedCircularCap.arcPoint
    split <;> fun_prop
  · exact capParam_injOn_public c

theorem segmentBoundaryMeasure_singleton_zero (seg : HorizontalSegment)
    (p : PlanePoint) : segmentBoundaryMeasure seg {p} = 0 := by
  rw [segmentBoundaryMeasure]
  apply intervalPushforward_singleton_zero_of_injOn
  · unfold segmentParam
    fun_prop
  · intro s _ t _ hst
    have hx := congrArg Prod.fst hst
    simp only [segmentParam] at hx
    linarith

private lemma core_angle_mem_public {c : StripCore} {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    s / c.radius ∈ Icc (-c.sideAngle) c.sideAngle := by
  have hr := c.radius_pos
  constructor
  · apply (le_div_iff₀ hr).2
    simpa [coreArcStart, mul_comm] using hs.1
  · apply (div_le_iff₀ hr).2
    simpa [coreArcEnd, mul_comm] using hs.2

private lemma core_angle_mem_pi_div_two_public {c : StripCore} {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    s / c.radius ∈ Icc (-(π / 2)) (π / 2) := by
  have hu := core_angle_mem_public hs
  have hb := c.sideAngle_le_pi_div_two
  exact ⟨(neg_le_neg hb).trans hu.1, hu.2.trans hb⟩

private lemma coreParam_injOn_public (c : StripCore)
    (curve : ℝ → PlanePoint)
    (hy : ∀ s, (curve s).2 = c.radius * sin (s / c.radius)) :
    Set.InjOn curve (Icc (coreArcStart c) (coreArcEnd c)) := by
  intro s hs t ht hst
  have hcoord := congrArg Prod.snd hst
  rw [hy s, hy t] at hcoord
  have hsin : sin (s / c.radius) = sin (t / c.radius) := by
    nlinarith [c.radius_pos]
  have hang := Real.injOn_sin (core_angle_mem_pi_div_two_public hs)
    (core_angle_mem_pi_div_two_public ht) hsin
  exact (div_left_inj' (ne_of_gt c.radius_pos)).mp hang

theorem leftCoreBoundaryMeasure_singleton_zero (c : StripCore)
    (p : PlanePoint) : leftCoreBoundaryMeasure c {p} = 0 := by
  rw [leftCoreBoundaryMeasure]
  apply intervalPushforward_singleton_zero_of_injOn
  · unfold leftCoreParam
    fun_prop
  · apply coreParam_injOn_public c
    intro s
    rfl

theorem rightCoreBoundaryMeasure_singleton_zero (c : StripCore)
    (p : PlanePoint) : rightCoreBoundaryMeasure c {p} = 0 := by
  rw [rightCoreBoundaryMeasure]
  apply intervalPushforward_singleton_zero_of_injOn
  · unfold rightCoreParam
    fun_prop
  · apply coreParam_injOn_public c
    intro s
    rfl

structure FourArcAssembly where
  core : StripCore
  outerAngle : ℝ
  outerAngle_pos : 0 < outerAngle
  outerAngle_lt_pi_div_two : outerAngle < π / 2

namespace FourArcAssembly

def upperCap (a : FourArcAssembly) : OneSidedCircularCap where
  chord := a.core.chord
  theta := a.outerAngle
  midpointX := 0
  baseY := 1
  side := .upper
  chord_pos := a.core.chord_pos
  theta_pos := a.outerAngle_pos
  theta_lt_pi := lt_trans a.outerAngle_lt_pi_div_two (by linarith [Real.pi_pos])

def lowerCap (a : FourArcAssembly) : OneSidedCircularCap where
  chord := a.core.chord
  theta := a.outerAngle
  midpointX := 0
  baseY := -1
  side := .lower
  chord_pos := a.core.chord_pos
  theta_pos := a.outerAngle_pos
  theta_lt_pi := lt_trans a.outerAngle_lt_pi_div_two (by linarith [Real.pi_pos])

def carrier (a : FourArcAssembly) : Set PlanePoint :=
  a.core.carrier ∪ a.upperCap.carrier ∪ a.lowerCap.carrier

/-- Explicit arc-length pushforward measure of the complete regular boundary.
The attachment chords are omitted because they are internal; endpoint atoms
are null for every summand. -/
def boundaryMeasure (a : FourArcAssembly) : Measure PlanePoint :=
  leftCoreBoundaryMeasure a.core + rightCoreBoundaryMeasure a.core +
    capBoundaryMeasure a.upperCap + capBoundaryMeasure a.lowerCap

/-- The explicit four-arc boundary measure gives every endpoint zero mass. -/
theorem boundaryMeasure_singleton_zero (a : FourArcAssembly) (p : PlanePoint) :
    a.boundaryMeasure {p} = 0 := by
  rw [boundaryMeasure]
  simp only [Measure.add_apply]
  rw [leftCoreBoundaryMeasure_singleton_zero,
    rightCoreBoundaryMeasure_singleton_zero,
    capBoundaryMeasure_singleton_zero,
    capBoundaryMeasure_singleton_zero]
  norm_num

/-- Weighted area is the ambient Lebesgue integral over the coordinate carrier. -/
def weightedArea (lam : ℝ) (a : FourArcAssembly) : ℝ :=
  WeightedArea lam a.carrier

/-- Weighted perimeter is the density integral against the explicit regular
boundary measure. -/
def weightedPerimeter (lam : ℝ) (a : FourArcAssembly) : ℝ :=
  WeightedPerimeter lam a.boundaryMeasure

theorem measurableSet_carrier (a : FourArcAssembly) : MeasurableSet a.carrier :=
  (a.core.measurableSet_carrier.union a.upperCap.measurableSet_carrier).union
    a.lowerCap.measurableSet_carrier

/-- The ambient area integral equals the geometric component formula. -/
theorem weightedArea_formula (lam : ℝ) (a : FourArcAssembly) :
    a.weightedArea lam =
      a.core.euclideanArea + lam *
        (a.upperCap.euclideanArea + a.lowerCap.euclideanArea) := by
  have hcoreUpper : AEDisjoint volume a.core.carrier a.upperCap.carrier := by
    refine measure_mono_null ?_ (volume_horizontalLine 1)
    rintro p ⟨hcore, hupper⟩
    have hyCore := a.core.carrier_y_bounds hcore
    have hyUpper : (1 : ℝ) ≤ p.2 := by
      simpa [upperCap] using hupper.2
    exact le_antisymm (le_trans (le_abs_self p.2) hyCore) hyUpper
  have hfirstLower : AEDisjoint volume
      (a.core.carrier ∪ a.upperCap.carrier) a.lowerCap.carrier := by
    refine measure_mono_null ?_ (volume_horizontalLine (-1))
    rintro p ⟨hfirst, hlower⟩
    rcases hfirst with hcore | hupper
    · have hyCore := a.core.carrier_y_bounds hcore
      have hyLower : p.2 ≤ (-1 : ℝ) := by
        simpa [lowerCap] using hlower.2
      have hneg : -p.2 ≤ 1 := le_trans (neg_le_abs p.2) hyCore
      exact le_antisymm hyLower (by linarith)
    · have hyUpper : (1 : ℝ) ≤ p.2 := by
        simpa [upperCap] using hupper.2
      have hyLower : p.2 ≤ (-1 : ℝ) := by
        simpa [lowerCap] using hlower.2
      linarith
  have hcore := core_integrableOn lam a.core
  have hupper := cap_integrableOn lam a.upperCap
  have hlower := cap_integrableOn lam a.lowerCap
  rw [weightedArea, WeightedArea, carrier,
    setIntegral_union₀ hfirstLower
      a.lowerCap.measurableSet_carrier.nullMeasurableSet
      (hcore.union hupper) hlower,
    setIntegral_union₀ hcoreUpper
      a.upperCap.measurableSet_carrier.nullMeasurableSet hcore hupper]
  rw [show (∫ p in a.core.carrier, StripDensity lam p) =
      a.core.euclideanArea by
        simpa [WeightedArea] using a.core.weightedArea_formula lam,
    show (∫ p in a.upperCap.carrier, StripDensity lam p) =
      lam * a.upperCap.euclideanArea by
        simpa [WeightedArea] using
          cap_upper_weightedArea lam a.upperCap rfl rfl,
    show (∫ p in a.lowerCap.carrier, StripDensity lam p) =
      lam * a.lowerCap.euclideanArea by
        simpa [WeightedArea] using
          cap_lower_weightedArea lam a.lowerCap rfl rfl]
  ring

/-- The boundary integral equals the four-arc component formula. -/
theorem weightedPerimeter_formula (lam : ℝ) (a : FourArcAssembly) :
    a.weightedPerimeter lam =
      a.core.boundaryArcLength + lam *
        (a.upperCap.arcLength + a.lowerCap.arcLength) := by
  rw [weightedPerimeter, WeightedPerimeter, boundaryMeasure]
  rw [integral_add_measure
      (((leftCoreBoundaryMeasure_integrable lam a.core).add_measure
        (rightCoreBoundaryMeasure_integrable lam a.core)).add_measure
          (capBoundaryMeasure_integrable lam a.upperCap))
      (capBoundaryMeasure_integrable lam a.lowerCap)]
  rw [integral_add_measure
      ((leftCoreBoundaryMeasure_integrable lam a.core).add_measure
        (rightCoreBoundaryMeasure_integrable lam a.core))
      (capBoundaryMeasure_integrable lam a.upperCap)]
  rw [integral_add_measure
      (leftCoreBoundaryMeasure_integrable lam a.core)
      (rightCoreBoundaryMeasure_integrable lam a.core)]
  rw [leftCore_weightedIntegral, rightCore_weightedIntegral,
    cap_upper_weightedIntegral lam a.upperCap rfl rfl,
    cap_lower_weightedIntegral lam a.lowerCap rfl rfl,
    StripCore.boundaryArcLength]
  ring
def boundaryTrace (a : FourArcAssembly) : Set PlanePoint :=
  StripCore.leftArcTrace a.core ∪
    (StripCore.rightArcTrace a.core ∪
      (OneSidedCircularCap.arcTrace a.upperCap ∪
        OneSidedCircularCap.arcTrace a.lowerCap))

private lemma core_chord_endpoint_mem_arcs (c : StripCore) {p : PlanePoint}
    (hy : p.2 = 1 ∨ p.2 = -1) (hx : |p.1| ≤ c.chord / 2)
    (hn : ¬ |p.1| < c.chord / 2) :
    p ∈ StripCore.leftArcTrace c ∪ StripCore.rightArcTrace c := by
  have hhalf : 0 < c.chord / 2 := div_pos c.chord_pos (by norm_num)
  have habs : |p.1| = c.chord / 2 := le_antisymm hx (le_of_not_gt hn)
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hcosSq : (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
    nlinarith [sq_nonneg (c.radius * c.curvature - 1)]
  have hySq : p.2 ^ 2 = 1 := by rcases hy with hy | hy <;> rw [hy] <;> norm_num
  by_cases hpnonneg : 0 ≤ p.1
  · have hpx : p.1 = c.chord / 2 := by
      rw [abs_of_nonneg hpnonneg] at habs
      exact habs
    apply Or.inr
    change (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1
    constructor
    · rw [hpx, StripCore.rightCenterX]
      nlinarith
    · exact ⟨hpx.ge, by rcases hy with hy | hy <;> simp [hy]⟩
  · have hpnonpos : p.1 ≤ 0 := le_of_not_ge hpnonneg
    have hpx : p.1 = -c.chord / 2 := by
      rw [abs_of_nonpos hpnonpos] at habs
      linarith
    apply Or.inl
    change (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1
    constructor
    · rw [hpx, StripCore.leftCenterX]
      nlinarith
    · exact ⟨hpx.le, by rcases hy with hy | hy <;> simp [hy]⟩

private theorem upper_strictChord_mem_interior (a : FourArcAssembly)
    {p : PlanePoint} (hp : p.2 = 1 ∧ |p.1| < a.core.chord / 2) :
    p ∈ interior a.carrier := by
  let U : Set PlanePoint :=
    {q | -a.core.chord / 2 < q.1 ∧ q.1 < a.core.chord / 2 ∧
      -1 < q.2 ∧ a.upperCap.radiusSquaredAt q < a.upperCap.radius ^ 2}
  have hopen : IsOpen U := by
    change IsOpen
      ({q : PlanePoint | -a.core.chord / 2 < q.1} ∩
        ({q : PlanePoint | q.1 < a.core.chord / 2} ∩
          ({q : PlanePoint | -1 < q.2} ∩
            {q : PlanePoint |
              a.upperCap.radiusSquaredAt q < a.upperCap.radius ^ 2})))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt (by
            change Continuous (fun q : PlanePoint =>
              (q.1 - a.upperCap.center.1) ^ 2 +
                (q.2 - a.upperCap.center.2) ^ 2)
            fun_prop) continuous_const)))
  have hsub : U ⊆ a.carrier := by
    intro q hq
    by_cases hy : q.2 ≤ 1
    · apply Or.inl
      apply Or.inl
      have hyabs : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.2.1], hy⟩
      apply Or.inl
      apply Or.inl
      exact ⟨hq.1.le, hq.2.1.le, hyabs⟩
    · apply Or.inl
      apply Or.inr
      exact ⟨hq.2.2.2.le, by simpa [upperCap] using (le_of_not_ge hy)⟩
  apply interior_maximal hsub hopen
  have hhalf : 0 < a.core.chord / 2 :=
    div_pos a.core.chord_pos (by norm_num)
  have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_pos hhalf] using hp.2
  have htrig := Real.sin_sq_add_cos_sq a.upperCap.theta
  have hscale := congrArg (fun z : ℝ => a.upperCap.radius ^ 2 * z) htrig
  have hrs : a.upperCap.radius * sin a.upperCap.theta =
      a.core.chord / 2 := by
    simpa [upperCap] using a.upperCap.radius_mul_sin
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
  have hdisk : a.upperCap.radiusSquaredAt p < a.upperCap.radius ^ 2 := by
    simp only [OneSidedCircularCap.radiusSquaredAt,
      OneSidedCircularCap.center, upperCap, hp.1] at ⊢
    simp only [upperCap] at hscale
    simp only [upperCap] at hrsSq
    nlinarith
  have hxbounds := abs_lt.mp hp.2
  exact ⟨by linarith [hxbounds.1], hxbounds.2, by rw [hp.1]; norm_num, hdisk⟩

private theorem lower_strictChord_mem_interior (a : FourArcAssembly)
    {p : PlanePoint} (hp : p.2 = -1 ∧ |p.1| < a.core.chord / 2) :
    p ∈ interior a.carrier := by
  let U : Set PlanePoint :=
    {q | -a.core.chord / 2 < q.1 ∧ q.1 < a.core.chord / 2 ∧
      q.2 < 1 ∧ a.lowerCap.radiusSquaredAt q < a.lowerCap.radius ^ 2}
  have hopen : IsOpen U := by
    change IsOpen
      ({q : PlanePoint | -a.core.chord / 2 < q.1} ∩
        ({q : PlanePoint | q.1 < a.core.chord / 2} ∩
          ({q : PlanePoint | q.2 < 1} ∩
            {q : PlanePoint |
              a.lowerCap.radiusSquaredAt q < a.lowerCap.radius ^ 2})))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_snd continuous_const).inter
          (isOpen_lt (by
            change Continuous (fun q : PlanePoint =>
              (q.1 - a.lowerCap.center.1) ^ 2 +
                (q.2 - a.lowerCap.center.2) ^ 2)
            fun_prop) continuous_const)))
  have hsub : U ⊆ a.carrier := by
    intro q hq
    by_cases hy : -1 ≤ q.2
    · apply Or.inl
      apply Or.inl
      have hyabs : |q.2| ≤ 1 := abs_le.mpr ⟨hy, hq.2.2.1.le⟩
      apply Or.inl
      apply Or.inl
      exact ⟨hq.1.le, hq.2.1.le, hyabs⟩
    · apply Or.inr
      exact ⟨hq.2.2.2.le, by simpa [lowerCap] using (le_of_not_ge hy)⟩
  apply interior_maximal hsub hopen
  have hhalf : 0 < a.core.chord / 2 :=
    div_pos a.core.chord_pos (by norm_num)
  have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_pos hhalf] using hp.2
  have htrig := Real.sin_sq_add_cos_sq a.lowerCap.theta
  have hscale := congrArg (fun z : ℝ => a.lowerCap.radius ^ 2 * z) htrig
  have hrs : a.lowerCap.radius * sin a.lowerCap.theta =
      a.core.chord / 2 := by
    simpa [lowerCap] using a.lowerCap.radius_mul_sin
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
  have hdisk : a.lowerCap.radiusSquaredAt p < a.lowerCap.radius ^ 2 := by
    simp only [OneSidedCircularCap.radiusSquaredAt,
      OneSidedCircularCap.center, lowerCap, hp.1] at ⊢
    simp only [lowerCap] at hscale
    simp only [lowerCap] at hrsSq
    nlinarith
  have hxbounds := abs_lt.mp hp.2
  exact ⟨by linarith [hxbounds.1], hxbounds.2, by rw [hp.1]; norm_num, hdisk⟩

private lemma chord_to_boundaryTrace (a : FourArcAssembly) {p : PlanePoint}
    (hy : p.2 = 1 ∨ p.2 = -1) (hx : |p.1| ≤ a.core.chord / 2)
    (hpfrontier : p ∈ frontier a.carrier) :
    p ∈ a.boundaryTrace := by
  by_cases hstrict : |p.1| < a.core.chord / 2
  · exfalso
    rcases hy with hy | hy
    · exact (mem_frontier_iff_notMem_interior
        ((a.core.isClosed_carrier.union a.upperCap.isClosed_carrier).union
          a.lowerCap.isClosed_carrier |>.frontier_subset hpfrontier)).mp hpfrontier
          (upper_strictChord_mem_interior a ⟨hy, hstrict⟩)
    · exact (mem_frontier_iff_notMem_interior
        ((a.core.isClosed_carrier.union a.upperCap.isClosed_carrier).union
          a.lowerCap.isClosed_carrier |>.frontier_subset hpfrontier)).mp hpfrontier
          (lower_strictChord_mem_interior a ⟨hy, hstrict⟩)
  · rcases core_chord_endpoint_mem_arcs a.core hy hx hstrict with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)

theorem frontier_carrier_subset_boundaryTrace (a : FourArcAssembly) :
    frontier a.carrier ⊆ a.boundaryTrace := by
  intro p hp
  have htop := frontier_union_subset
    (a.core.carrier ∪ a.upperCap.carrier) a.lowerCap.carrier hp
  rcases htop with hfirst | hlower
  · have hmiddle := frontier_union_subset a.core.carrier a.upperCap.carrier hfirst.1
    rcases hmiddle with hcore | hupper
    · rw [a.core.frontier_carrier] at hcore
      rcases hcore.1 with hleft | hright | hupperChord | hlowerChord
      · exact Or.inl hleft
      · exact Or.inr (Or.inl hright)
      · exact chord_to_boundaryTrace a (Or.inl hupperChord.1) hupperChord.2 hp
      · exact chord_to_boundaryTrace a (Or.inr hlowerChord.1) hlowerChord.2 hp
    · rw [a.upperCap.frontier_carrier] at hupper
      rcases hupper.2 with harc | hchord
      · exact Or.inr (Or.inr (Or.inl harc))
      · exact chord_to_boundaryTrace a (Or.inl hchord.1)
          (by simpa [upperCap] using hchord.2) hp
  · rw [a.lowerCap.frontier_carrier] at hlower
    rcases hlower.2 with harc | hchord
    · exact Or.inr (Or.inr (Or.inr harc))
    · exact chord_to_boundaryTrace a (Or.inr hchord.1)
        (by simpa [lowerCap] using hchord.2) hp

theorem isClosed_carrier (a : FourArcAssembly) : IsClosed a.carrier :=
  (a.core.isClosed_carrier.union a.upperCap.isClosed_carrier).union
    a.lowerCap.isClosed_carrier

private lemma mem_frontier_union_of_mem_frontier_of_not_mem
    {s t : Set PlanePoint} {p : PlanePoint}
    (hs : IsClosed s) (ht : IsClosed t) (hp : p ∈ frontier s)
    (hpt : p ∉ t) : p ∈ frontier (s ∪ t) := by
  have hps : p ∈ s := hs.frontier_subset hp
  have hpUnion : p ∈ s ∪ t := Or.inl hps
  rw [mem_frontier_iff_notMem_interior hpUnion]
  intro hi
  have hUnion : interior (s ∪ t) ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  have hCompl : tᶜ ∈ nhds p := ht.isOpen_compl.mem_nhds hpt
  have hInter : interior (s ∪ t) ∩ tᶜ ∈ nhds p :=
    Filter.inter_mem hUnion hCompl
  have hsNhd : s ∈ nhds p := Filter.mem_of_superset hInter (by
    intro q hq
    rcases interior_subset hq.1 with hqs | hqt
    · exact hqs
    · exact False.elim (hq.2 hqt))
  have hpInterior : p ∈ interior s := mem_interior_iff_mem_nhds.mpr hsNhd
  exact (mem_frontier_iff_notMem_interior hps).mp hp hpInterior

private lemma core_radius_cos_sq (c : StripCore) :
    (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  nlinarith [sq_nonneg (c.radius * c.curvature - 1)]

private theorem left_endpoint_mem_frontier (a : FourArcAssembly)
    {p : PlanePoint} (hx : p.1 = -a.core.chord / 2)
    (hy : p.2 = 1 ∨ p.2 = -1) : p ∈ frontier a.carrier := by
  have hpCore : p ∈ a.core.carrier := by
    apply Or.inl
    apply Or.inl
    exact ⟨by rw [hx], by rw [hx]; linarith [a.core.chord_pos],
      by rcases hy with hy | hy <;> simp [hy]⟩
  have hpCarrier : p ∈ a.carrier := Or.inl (Or.inl hpCore)
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 - ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqCarrier := interior_subset (hball hqball)
  rcases hqCarrier with hfirst | hlower
  · rcases hfirst with hcore | hupper
    · rcases hcore with (hrect | hleft) | hright
      · change -a.core.chord / 2 ≤ p.1 - ε / 2 ∧
          p.1 - ε / 2 ≤ a.core.chord / 2 ∧ |p.2| ≤ 1 at hrect
        linarith [hx]
      · have hySq : p.2 ^ 2 = 1 := by
          rcases hy with hy | hy <;> rw [hy] <;> norm_num
        have hpCircle :
            (p.1 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 =
              a.core.radius ^ 2 := by
          rw [hx, StripCore.leftCenterX]
          nlinarith [core_radius_cos_sq a.core]
        have hpDiff : p.1 - a.core.leftCenterX ≤ 0 := by
          rw [hx, StripCore.leftCenterX]
          have hcos : 0 ≤ cos a.core.sideAngle := by
            rw [a.core.cos_sideAngle]
            positivity
          nlinarith [a.core.radius_pos]
        change
          ((p.1 - ε / 2 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 ≤
            a.core.radius ^ 2) ∧
              p.1 - ε / 2 ≤ -a.core.chord / 2 ∧ |p.2| ≤ 1 at hleft
        nlinarith
      · change
          ((p.1 - ε / 2 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 ≤
            a.core.radius ^ 2) ∧
              a.core.chord / 2 ≤ p.1 - ε / 2 ∧ |p.2| ≤ 1 at hright
        linarith [hx, a.core.chord_pos]
    · rcases hy with hy | hy
      · have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
          hupper (by simpa [upperCap, hy])
        have hxbound : |p.1 - ε / 2| ≤ a.core.chord / 2 := by
          simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
        have := (abs_le.mp hxbound).1
        linarith [hx]
      · have hside : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
        linarith
  · rcases hy with hy | hy
    · have hside : p.2 ≤ (-1 : ℝ) := by simpa [lowerCap] using hlower.2
      linarith
    · have hchord := a.lowerCap.mem_chordCarrier_of_mem_carrier_of_eq_base
          hlower (by simpa [lowerCap, hy])
      have hxbound : |p.1 - ε / 2| ≤ a.core.chord / 2 := by
        simpa [OneSidedCircularCap.chordCarrier, lowerCap] using hchord.2
      have := (abs_le.mp hxbound).1
      linarith [hx]

private theorem right_endpoint_mem_frontier (a : FourArcAssembly)
    {p : PlanePoint} (hx : p.1 = a.core.chord / 2)
    (hy : p.2 = 1 ∨ p.2 = -1) : p ∈ frontier a.carrier := by
  have hpCore : p ∈ a.core.carrier := by
    apply Or.inl
    apply Or.inl
    exact ⟨by rw [hx]; linarith [a.core.chord_pos], by rw [hx],
      by rcases hy with hy | hy <;> simp [hy]⟩
  have hpCarrier : p ∈ a.carrier := Or.inl (Or.inl hpCore)
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqCarrier := interior_subset (hball hqball)
  rcases hqCarrier with hfirst | hlower
  · rcases hfirst with hcore | hupper
    · rcases hcore with (hrect | hleft) | hright
      · change -a.core.chord / 2 ≤ p.1 + ε / 2 ∧
          p.1 + ε / 2 ≤ a.core.chord / 2 ∧ |p.2| ≤ 1 at hrect
        linarith [hx]
      · change
          ((p.1 + ε / 2 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 ≤
            a.core.radius ^ 2) ∧
              p.1 + ε / 2 ≤ -a.core.chord / 2 ∧ |p.2| ≤ 1 at hleft
        linarith [hx, a.core.chord_pos]
      · have hySq : p.2 ^ 2 = 1 := by
          rcases hy with hy | hy <;> rw [hy] <;> norm_num
        have hpCircle :
            (p.1 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 =
              a.core.radius ^ 2 := by
          rw [hx, StripCore.rightCenterX]
          nlinarith [core_radius_cos_sq a.core]
        have hpDiff : 0 ≤ p.1 - a.core.rightCenterX := by
          rw [hx, StripCore.rightCenterX]
          have hcos : 0 ≤ cos a.core.sideAngle := by
            rw [a.core.cos_sideAngle]
            positivity
          nlinarith [a.core.radius_pos]
        change
          ((p.1 + ε / 2 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 ≤
            a.core.radius ^ 2) ∧
              a.core.chord / 2 ≤ p.1 + ε / 2 ∧ |p.2| ≤ 1 at hright
        nlinarith
    · rcases hy with hy | hy
      · have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
          hupper (by simpa [upperCap, hy])
        have hxbound : |p.1 + ε / 2| ≤ a.core.chord / 2 := by
          simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
        have := (abs_le.mp hxbound).2
        linarith [hx]
      · have hside : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
        linarith
  · rcases hy with hy | hy
    · have hside : p.2 ≤ (-1 : ℝ) := by simpa [lowerCap] using hlower.2
      linarith
    · have hchord := a.lowerCap.mem_chordCarrier_of_mem_carrier_of_eq_base
          hlower (by simpa [lowerCap, hy])
      have hxbound : |p.1 + ε / 2| ≤ a.core.chord / 2 := by
        simpa [OneSidedCircularCap.chordCarrier, lowerCap] using hchord.2
      have := (abs_le.mp hxbound).2
      linarith [hx]

private theorem leftArc_mem_frontier (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.leftArcTrace a.core) :
    p ∈ frontier a.carrier := by
  by_cases hstrict : |p.2| < 1
  · have hpCoreFrontier : p ∈ frontier a.core.carrier := by
      rw [a.core.frontier_carrier]
      exact Or.inl hp
    have hnotUpper : p ∉ a.upperCap.carrier := by
      intro hupper
      have hy : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
      exact (not_le.mpr (abs_lt.mp hstrict).2) hy
    have hfirst : p ∈ frontier (a.core.carrier ∪ a.upperCap.carrier) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.core.isClosed_carrier a.upperCap.isClosed_carrier
          hpCoreFrontier hnotUpper
    have hnotLower : p ∉ a.lowerCap.carrier := by
      intro hlower
      have hy : p.2 ≤ (-1 : ℝ) := by simpa [lowerCap] using hlower.2
      exact (not_le.mpr (abs_lt.mp hstrict).1) hy
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      (a.core.isClosed_carrier.union a.upperCap.isClosed_carrier)
      a.lowerCap.isClosed_carrier hfirst hnotLower
  · have hyabs : |p.2| = 1 :=
      le_antisymm hp.2.2 (le_of_not_gt hstrict)
    have hy : p.2 = 1 ∨ p.2 = -1 := by
      by_cases hynonneg : 0 ≤ p.2
      · left
        rw [abs_of_nonneg hynonneg] at hyabs
        exact hyabs
      · right
        have hynonpos : p.2 ≤ 0 := le_of_not_ge hynonneg
        rw [abs_of_nonpos hynonpos] at hyabs
        linarith
    have hySq : p.2 ^ 2 = 1 := by
      rcases hy with hy | hy <;> rw [hy] <;> norm_num
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hdiff :
        p.1 - a.core.leftCenterX ≤
          -(a.core.radius * cos a.core.sideAngle) := by
      rw [StripCore.leftCenterX]
      linarith [hp.2.1]
    have hxeq :
        p.1 - a.core.leftCenterX =
          -(a.core.radius * cos a.core.sideAngle) := by
      have hdiff0 : p.1 - a.core.leftCenterX ≤ 0 := by
        nlinarith [a.core.radius_pos]
      have hsq :
          (p.1 - a.core.leftCenterX) ^ 2 =
            (a.core.radius * cos a.core.sideAngle) ^ 2 := by
        nlinarith [hp.1, core_radius_cos_sq a.core]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (p.1 - a.core.leftCenterX)
        (a.core.radius * cos a.core.sideAngle)).mp hsq
      rw [abs_of_nonpos hdiff0,
        abs_of_nonneg (mul_nonneg a.core.radius_pos.le hcos)] at habs
      linarith
    have hx : p.1 = -a.core.chord / 2 := by
      rw [StripCore.leftCenterX] at hxeq
      linarith
    exact left_endpoint_mem_frontier a hx hy

private theorem rightArc_mem_frontier (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.rightArcTrace a.core) :
    p ∈ frontier a.carrier := by
  by_cases hstrict : |p.2| < 1
  · have hpCoreFrontier : p ∈ frontier a.core.carrier := by
      rw [a.core.frontier_carrier]
      exact Or.inr (Or.inl hp)
    have hnotUpper : p ∉ a.upperCap.carrier := by
      intro hupper
      have hy : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
      exact (not_le.mpr (abs_lt.mp hstrict).2) hy
    have hfirst : p ∈ frontier (a.core.carrier ∪ a.upperCap.carrier) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.core.isClosed_carrier a.upperCap.isClosed_carrier
          hpCoreFrontier hnotUpper
    have hnotLower : p ∉ a.lowerCap.carrier := by
      intro hlower
      have hy : p.2 ≤ (-1 : ℝ) := by simpa [lowerCap] using hlower.2
      exact (not_le.mpr (abs_lt.mp hstrict).1) hy
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      (a.core.isClosed_carrier.union a.upperCap.isClosed_carrier)
      a.lowerCap.isClosed_carrier hfirst hnotLower
  · have hyabs : |p.2| = 1 :=
      le_antisymm hp.2.2 (le_of_not_gt hstrict)
    have hy : p.2 = 1 ∨ p.2 = -1 := by
      by_cases hynonneg : 0 ≤ p.2
      · left
        rw [abs_of_nonneg hynonneg] at hyabs
        exact hyabs
      · right
        have hynonpos : p.2 ≤ 0 := le_of_not_ge hynonneg
        rw [abs_of_nonpos hynonpos] at hyabs
        linarith
    have hySq : p.2 ^ 2 = 1 := by
      rcases hy with hy | hy <;> rw [hy] <;> norm_num
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hdiff :
        a.core.radius * cos a.core.sideAngle ≤
          p.1 - a.core.rightCenterX := by
      rw [StripCore.rightCenterX]
      linarith [hp.2.1]
    have hxeq :
        p.1 - a.core.rightCenterX =
          a.core.radius * cos a.core.sideAngle := by
      have hdiff0 : 0 ≤ p.1 - a.core.rightCenterX := by
        nlinarith [a.core.radius_pos]
      have hsq :
          (p.1 - a.core.rightCenterX) ^ 2 =
            (a.core.radius * cos a.core.sideAngle) ^ 2 := by
        nlinarith [hp.1, core_radius_cos_sq a.core]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (p.1 - a.core.rightCenterX)
        (a.core.radius * cos a.core.sideAngle)).mp hsq
      rw [abs_of_nonneg hdiff0,
        abs_of_nonneg (mul_nonneg a.core.radius_pos.le hcos)] at habs
      exact habs
    have hx : p.1 = a.core.chord / 2 := by
      rw [StripCore.rightCenterX] at hxeq
      linarith
    exact right_endpoint_mem_frontier a hx hy

private theorem upperArc_mem_frontier (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.upperCap) :
    p ∈ frontier a.carrier := by
  by_cases hyEq : p.2 = 1
  · have hpCarrier : p ∈ a.upperCap.carrier := ⟨hp.1.le, hp.2⟩
    have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
      hpCarrier (by simpa [upperCap] using hyEq)
    have hx : |p.1| ≤ a.core.chord / 2 := by
      simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
    have hn : ¬ |p.1| < a.core.chord / 2 := by
      intro hstrict
      have hhalf : 0 < a.core.chord / 2 :=
        div_pos a.core.chord_pos (by norm_num)
      have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
        rw [sq_lt_sq]
        simpa [abs_of_pos hhalf] using hstrict
      have htrig := Real.sin_sq_add_cos_sq a.upperCap.theta
      have hscale := congrArg
        (fun z : ℝ => a.upperCap.radius ^ 2 * z) htrig
      have hrs : a.upperCap.radius * sin a.upperCap.theta =
          a.core.chord / 2 := by
        simpa [upperCap] using a.upperCap.radius_mul_sin
      have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
      have hpEq := hp.1
      simp only [OneSidedCircularCap.radiusSquaredAt] at hpEq
      rw [hyEq] at hpEq
      simp only [OneSidedCircularCap.center, upperCap] at hpEq
      simp only [upperCap] at hscale hrsSq
      nlinarith
    rcases core_chord_endpoint_mem_arcs a.core (Or.inl hyEq) hx hn with
      hleft | hright
    · exact leftArc_mem_frontier a hleft
    · exact rightArc_mem_frontier a hright
  · have hy : (1 : ℝ) < p.2 := by
      have := hp.2
      simp only [OneSidedCircularCap.arcTrace, upperCap] at this
      exact lt_of_le_of_ne this (Ne.symm hyEq)
    have hpCapFrontier : p ∈ frontier a.upperCap.carrier := by
      rw [a.upperCap.frontier_carrier]
      exact Or.inl hp
    have hnotCore : p ∉ a.core.carrier := by
      intro hcore
      have hyCore := a.core.carrier_y_bounds hcore
      linarith [le_trans (le_abs_self p.2) hyCore]
    have hcapCore : p ∈ frontier
        (a.upperCap.carrier ∪ a.core.carrier) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.upperCap.isClosed_carrier a.core.isClosed_carrier
          hpCapFrontier hnotCore
    have hfirst : p ∈ frontier
        (a.core.carrier ∪ a.upperCap.carrier) := by
      simpa [union_comm] using hcapCore
    have hnotLower : p ∉ a.lowerCap.carrier := by
      intro hlower
      have hyLower : p.2 ≤ (-1 : ℝ) := by simpa [lowerCap] using hlower.2
      linarith
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      (a.core.isClosed_carrier.union a.upperCap.isClosed_carrier)
      a.lowerCap.isClosed_carrier hfirst hnotLower

private theorem lowerArc_mem_frontier (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.lowerCap) :
    p ∈ frontier a.carrier := by
  by_cases hyEq : p.2 = -1
  · have hpCarrier : p ∈ a.lowerCap.carrier := ⟨hp.1.le, hp.2⟩
    have hchord := a.lowerCap.mem_chordCarrier_of_mem_carrier_of_eq_base
      hpCarrier (by simpa [lowerCap] using hyEq)
    have hx : |p.1| ≤ a.core.chord / 2 := by
      simpa [OneSidedCircularCap.chordCarrier, lowerCap] using hchord.2
    have hn : ¬ |p.1| < a.core.chord / 2 := by
      intro hstrict
      have hhalf : 0 < a.core.chord / 2 :=
        div_pos a.core.chord_pos (by norm_num)
      have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
        rw [sq_lt_sq]
        simpa [abs_of_pos hhalf] using hstrict
      have htrig := Real.sin_sq_add_cos_sq a.lowerCap.theta
      have hscale := congrArg
        (fun z : ℝ => a.lowerCap.radius ^ 2 * z) htrig
      have hrs : a.lowerCap.radius * sin a.lowerCap.theta =
          a.core.chord / 2 := by
        simpa [lowerCap] using a.lowerCap.radius_mul_sin
      have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
      have hpEq := hp.1
      simp only [OneSidedCircularCap.radiusSquaredAt] at hpEq
      rw [hyEq] at hpEq
      simp only [OneSidedCircularCap.center, lowerCap] at hpEq
      simp only [lowerCap] at hscale hrsSq
      nlinarith
    rcases core_chord_endpoint_mem_arcs a.core (Or.inr hyEq) hx hn with
      hleft | hright
    · exact leftArc_mem_frontier a hleft
    · exact rightArc_mem_frontier a hright
  · have hy : p.2 < (-1 : ℝ) := by
      have := hp.2
      simp only [OneSidedCircularCap.arcTrace, lowerCap] at this
      exact lt_of_le_of_ne this hyEq
    have hpCapFrontier : p ∈ frontier a.lowerCap.carrier := by
      rw [a.lowerCap.frontier_carrier]
      exact Or.inl hp
    have hnotFirst :
        p ∉ a.core.carrier ∪ a.upperCap.carrier := by
      rintro (hcore | hupper)
      · have hyCore := a.core.carrier_y_bounds hcore
        have hneg : -p.2 ≤ 1 := le_trans (neg_le_abs p.2) hyCore
        linarith
      · have hyUpper : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
        linarith
    have hlowerFirst : p ∈ frontier
        (a.lowerCap.carrier ∪
          (a.core.carrier ∪ a.upperCap.carrier)) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.lowerCap.isClosed_carrier
        (a.core.isClosed_carrier.union a.upperCap.isClosed_carrier)
          hpCapFrontier hnotFirst
    rw [union_comm a.lowerCap.carrier
      (a.core.carrier ∪ a.upperCap.carrier)] at hlowerFirst
    exact hlowerFirst

theorem boundaryTrace_subset_frontier_carrier (a : FourArcAssembly) :
    a.boundaryTrace ⊆ frontier a.carrier := by
  rintro p (hleft | hright | hupper | hlower)
  · exact leftArc_mem_frontier a hleft
  · exact rightArc_mem_frontier a hright
  · exact upperArc_mem_frontier a hupper
  · exact lowerArc_mem_frontier a hlower

theorem frontier_carrier (a : FourArcAssembly) :
    frontier a.carrier = a.boundaryTrace :=
  Set.Subset.antisymm a.frontier_carrier_subset_boundaryTrace
    a.boundaryTrace_subset_frontier_carrier


/-- All four boundary arcs have the same radius when the exterior chord has the
source incidence length `2 * sin alpha / h`. -/
theorem outer_radius_eq_core_radius (a : FourArcAssembly)
    (hincidence : a.core.chord * a.core.curvature =
      2 * sin a.outerAngle) :
    a.upperCap.radius = a.core.radius := by
  simp only [OneSidedCircularCap.radius, upperCap, StripCore.radius]
  have hchord : a.core.chord =
      2 * sin a.outerAngle / a.core.curvature :=
    (eq_div_iff (ne_of_gt a.core.curvature_pos)).2 hincidence
  calc
    a.core.chord / (2 * sin a.outerAngle) =
        (2 * sin a.outerAngle / a.core.curvature) /
          (2 * sin a.outerAngle) := by rw [hchord]
    _ = 1 / a.core.curvature := by
      have hs := sin_pos_of_pos_of_lt_pi a.outerAngle_pos
        (lt_trans a.outerAngle_lt_pi_div_two (by linarith [Real.pi_pos]))
      field_simp [ne_of_gt hs, ne_of_gt a.core.curvature_pos]

end FourArcAssembly

/-- The exact cap-substitution assembly.  It retains the central strip region,
attaches one upper cap, and exposes the lower interface chord. -/
structure ReplacementAssembly where
  core : StripCore
  replacementAngle : ℝ
  replacementAngle_pos : 0 < replacementAngle
  replacementAngle_lt_pi : replacementAngle < π

namespace ReplacementAssembly

def upperCap (a : ReplacementAssembly) : OneSidedCircularCap where
  chord := a.core.chord
  theta := a.replacementAngle
  midpointX := 0
  baseY := 1
  side := .upper
  chord_pos := a.core.chord_pos
  theta_pos := a.replacementAngle_pos
  theta_lt_pi := a.replacementAngle_lt_pi

def exposedLowerChord (a : ReplacementAssembly) : HorizontalSegment where
  chord := a.core.chord
  midpointX := 0
  baseY := -1
  chord_pos := a.core.chord_pos

def carrier (a : ReplacementAssembly) : Set PlanePoint :=
  a.core.carrier ∪ a.upperCap.carrier

/-- Explicit pushforward measure of the two retained side arcs, inserted upper
arc, and genuinely exposed lower chord. -/
def boundaryMeasure (a : ReplacementAssembly) : Measure PlanePoint :=
  leftCoreBoundaryMeasure a.core + rightCoreBoundaryMeasure a.core +
    capBoundaryMeasure a.upperCap + segmentBoundaryMeasure a.exposedLowerChord

/-- The explicit replacement boundary measure gives every endpoint zero mass. -/
theorem boundaryMeasure_singleton_zero (a : ReplacementAssembly)
    (p : PlanePoint) : a.boundaryMeasure {p} = 0 := by
  rw [boundaryMeasure]
  simp only [Measure.add_apply]
  rw [leftCoreBoundaryMeasure_singleton_zero,
    rightCoreBoundaryMeasure_singleton_zero,
    capBoundaryMeasure_singleton_zero,
    segmentBoundaryMeasure_singleton_zero]
  norm_num

/-- Ambient weighted-area integral over the replacement carrier. -/
def weightedArea (lam : ℝ) (a : ReplacementAssembly) : ℝ :=
  WeightedArea lam a.carrier

/-- Density integral against the complete explicit replacement boundary. -/
def weightedPerimeter (lam : ℝ) (a : ReplacementAssembly) : ℝ :=
  WeightedPerimeter lam a.boundaryMeasure

theorem measurableSet_carrier (a : ReplacementAssembly) :
    MeasurableSet a.carrier :=
  a.core.measurableSet_carrier.union a.upperCap.measurableSet_carrier

/-- The ambient area integral equals the retained-core-plus-cap formula. -/
theorem weightedArea_formula (lam : ℝ) (a : ReplacementAssembly) :
    a.weightedArea lam =
      a.core.euclideanArea + lam * a.upperCap.euclideanArea := by
  have hcoreUpper : AEDisjoint volume a.core.carrier a.upperCap.carrier := by
    refine measure_mono_null ?_ (volume_horizontalLine 1)
    rintro p ⟨hcore, hupper⟩
    have hyCore := a.core.carrier_y_bounds hcore
    have hyUpper : (1 : ℝ) ≤ p.2 := by
      simpa [upperCap] using hupper.2
    exact le_antisymm (le_trans (le_abs_self p.2) hyCore) hyUpper
  have hcore := core_integrableOn lam a.core
  have hupper := cap_integrableOn lam a.upperCap
  rw [weightedArea, WeightedArea, carrier,
    setIntegral_union₀ hcoreUpper
      a.upperCap.measurableSet_carrier.nullMeasurableSet hcore hupper]
  rw [show (∫ p in a.core.carrier, StripDensity lam p) =
      a.core.euclideanArea by
        simpa [WeightedArea] using a.core.weightedArea_formula lam,
    show (∫ p in a.upperCap.carrier, StripDensity lam p) =
      lam * a.upperCap.euclideanArea by
        simpa [WeightedArea] using
          cap_upper_weightedArea lam a.upperCap rfl rfl]

/-- The boundary integral equals the two side arcs, inserted cap arc, and
exposed lower chord formula. -/
theorem weightedPerimeter_formula (lam : ℝ) (a : ReplacementAssembly) :
    a.weightedPerimeter lam =
      a.core.boundaryArcLength + lam * a.upperCap.arcLength +
        a.exposedLowerChord.euclideanLength := by
  rw [weightedPerimeter, WeightedPerimeter, boundaryMeasure]
  rw [integral_add_measure
      (((leftCoreBoundaryMeasure_integrable lam a.core).add_measure
        (rightCoreBoundaryMeasure_integrable lam a.core)).add_measure
          (capBoundaryMeasure_integrable lam a.upperCap))
      (segmentBoundaryMeasure_integrable lam a.exposedLowerChord)]
  rw [integral_add_measure
      ((leftCoreBoundaryMeasure_integrable lam a.core).add_measure
        (rightCoreBoundaryMeasure_integrable lam a.core))
      (capBoundaryMeasure_integrable lam a.upperCap)]
  rw [integral_add_measure
      (leftCoreBoundaryMeasure_integrable lam a.core)
      (rightCoreBoundaryMeasure_integrable lam a.core)]
  rw [leftCore_weightedIntegral, rightCore_weightedIntegral,
    cap_upper_weightedIntegral lam a.upperCap rfl rfl,
    segment_weightedIntegral lam a.exposedLowerChord (by
      simp [exposedLowerChord]),
    StripCore.boundaryArcLength]
  ring

/-- The cap closure and retained strip core can meet only on `y = 1`. -/
theorem core_inter_upperCap_subset_interface (a : ReplacementAssembly) :
    a.core.carrier ∩ a.upperCap.carrier ⊆ {p : PlanePoint | p.2 = 1} := by
  intro p hp
  have hcore := a.core.carrier_y_bounds hp.1
  have hupper : (1 : ℝ) ≤ p.2 := hp.2.2
  have hle : p.2 ≤ 1 := le_trans (le_abs_self p.2) hcore
  exact le_antisymm hle hupper


/-- More precisely, the only possible overlap is the finite upper chord. -/
theorem core_inter_upperCap_subset_chord (a : ReplacementAssembly) :
    a.core.carrier ∩ a.upperCap.carrier ⊆ a.upperCap.chordCarrier := by
  intro p hp
  apply a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base hp.2
  exact a.core_inter_upperCap_subset_interface hp

/-- Exact attachment: the retained core and inserted cap meet along the whole
finite upper chord, and nowhere else. -/
theorem core_inter_upperCap_eq_chord (a : ReplacementAssembly) :
    a.core.carrier ∩ a.upperCap.carrier = a.upperCap.chordCarrier := by
  apply Subset.antisymm a.core_inter_upperCap_subset_chord
  intro p hp
  have hp' :
      p ∈ {q : PlanePoint | q.2 = (1 : ℝ) ∧
        |q.1| ≤ a.core.chord / 2} := by
    simpa [upperCap, OneSidedCircularCap.chordCarrier] using hp
  exact
    ⟨a.core.horizontalChord_subset_carrier (by norm_num) hp',
      a.upperCap.chordCarrier_subset_carrier hp⟩

/-- The cap interior and retained core are disjoint. -/
theorem core_inter_upperCap_interior_eq_empty (a : ReplacementAssembly) :
    a.core.carrier ∩ a.upperCap.interiorCarrier = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  have hcore := a.core.carrier_y_bounds hp.1
  have hupper : 1 < p.2 := hp.2.2
  have hle : p.2 ≤ 1 := le_trans (le_abs_self p.2) hcore
  linarith

/-- The full lower interface segment remains in the replacement carrier. -/
theorem exposedLowerChord_subset_carrier (a : ReplacementAssembly) :
    a.exposedLowerChord.carrier ⊆ a.carrier := by
  intro p hp
  have hp' :
      p ∈ {q : PlanePoint | q.2 = (-1 : ℝ) ∧
        |q.1| ≤ a.core.chord / 2} := by
    simpa [exposedLowerChord, HorizontalSegment.carrier] using hp
  exact Or.inl
    (a.core.horizontalChord_subset_carrier (by norm_num) hp')

/-- Every positive downward displacement from the lower chord leaves the
replacement.  This is the local exposure fact used to identify that segment as
boundary rather than disconnected scalar data. -/
theorem below_exposedLowerChord_not_mem (a : ReplacementAssembly)
    {p : PlanePoint} (hp : p ∈ a.exposedLowerChord.carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (p.1, p.2 - epsilon) ∉ a.carrier := by
  intro hbelow
  rcases hbelow with hcore | hcap
  · have hy := a.core.carrier_y_bounds hcore
    have hpY : p.2 = -1 := hp.1
    have hneg : p.2 - epsilon < 0 := by linarith
    rw [abs_of_neg hneg, hpY] at hy
    linarith
  · have hbase : (1 : ℝ) ≤ p.2 - epsilon := by
      simpa [upperCap] using hcap.2
    have hpY : p.2 = -1 := hp.1
    linarith

/-- The exposed lower chord is an actual boundary subset of the coordinate
replacement carrier. -/
theorem exposedLowerChord_subset_frontier (a : ReplacementAssembly) :
    a.exposedLowerChord.carrier ⊆ frontier a.carrier := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior
    (a.exposedLowerChord_subset_carrier hp)]
  intro hinterior
  have hnhds : interior a.carrier ∈ nhds p :=
    isOpen_interior.mem_nhds hinterior
  rcases Metric.mem_nhds_iff.mp hnhds with
    ⟨epsilon, hepsilon, hball⟩
  have hhalf : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
  have hnear :
      (p.1, p.2 - epsilon / 2) ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
      show p.2 - epsilon / 2 - p.2 = -(epsilon / 2) by ring,
      abs_neg, abs_of_pos hhalf, max_eq_right hhalf.le]
    linarith
  have hmember :
      (p.1, p.2 - epsilon / 2) ∈ a.carrier :=
    interior_subset (hball hnear)
  exact a.below_exposedLowerChord_not_mem hp hhalf hmember
/-- Every interior point of the inserted upper cap lies in `y > 1`. -/
theorem upperCap_interior_above (a : ReplacementAssembly) :
    a.upperCap.interiorCarrier ⊆ {p : PlanePoint | 1 < p.2} := by
  intro p hp
  exact hp.2

def boundaryTrace (a : ReplacementAssembly) : Set PlanePoint :=
  StripCore.leftArcTrace a.core ∪
    (StripCore.rightArcTrace a.core ∪
      (OneSidedCircularCap.arcTrace a.upperCap ∪
        a.exposedLowerChord.carrier))

private lemma core_chord_endpoint_mem_arcs (c : StripCore) {p : PlanePoint}
    (hy : p.2 = 1 ∨ p.2 = -1) (hx : |p.1| ≤ c.chord / 2)
    (hn : ¬ |p.1| < c.chord / 2) :
    p ∈ StripCore.leftArcTrace c ∪ StripCore.rightArcTrace c := by
  have habs : |p.1| = c.chord / 2 := le_antisymm hx (le_of_not_gt hn)
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hcosSq : (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
    nlinarith [sq_nonneg (c.radius * c.curvature - 1)]
  have hySq : p.2 ^ 2 = 1 := by rcases hy with hy | hy <;> rw [hy] <;> norm_num
  by_cases hpnonneg : 0 ≤ p.1
  · have hpx : p.1 = c.chord / 2 := by
      rw [abs_of_nonneg hpnonneg] at habs
      exact habs
    apply Or.inr
    change (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1
    constructor
    · rw [hpx, StripCore.rightCenterX]
      nlinarith
    · exact ⟨hpx.ge, by rcases hy with hy | hy <;> simp [hy]⟩
  · have hpnonpos : p.1 ≤ 0 := le_of_not_ge hpnonneg
    have hpx : p.1 = -c.chord / 2 := by
      rw [abs_of_nonpos hpnonpos] at habs
      linarith
    apply Or.inl
    change (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1
    constructor
    · rw [hpx, StripCore.leftCenterX]
      nlinarith
    · exact ⟨hpx.le, by rcases hy with hy | hy <;> simp [hy]⟩

private theorem upper_strictChord_mem_interior (a : ReplacementAssembly)
    {p : PlanePoint} (hp : p.2 = 1 ∧ |p.1| < a.core.chord / 2) :
    p ∈ interior a.carrier := by
  let U : Set PlanePoint :=
    {q | -a.core.chord / 2 < q.1 ∧ q.1 < a.core.chord / 2 ∧
      -1 < q.2 ∧ a.upperCap.radiusSquaredAt q < a.upperCap.radius ^ 2}
  have hopen : IsOpen U := by
    change IsOpen
      ({q : PlanePoint | -a.core.chord / 2 < q.1} ∩
        ({q : PlanePoint | q.1 < a.core.chord / 2} ∩
          ({q : PlanePoint | -1 < q.2} ∩
            {q : PlanePoint |
              a.upperCap.radiusSquaredAt q < a.upperCap.radius ^ 2})))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt (by
            change Continuous (fun q : PlanePoint =>
              (q.1 - a.upperCap.center.1) ^ 2 +
                (q.2 - a.upperCap.center.2) ^ 2)
            fun_prop) continuous_const)))
  have hsub : U ⊆ a.carrier := by
    intro q hq
    by_cases hy : q.2 ≤ 1
    · apply Or.inl
      apply Or.inl
      apply Or.inl
      have hyabs : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.2.1], hy⟩
      exact ⟨hq.1.le, hq.2.1.le, hyabs⟩
    · apply Or.inr
      exact ⟨hq.2.2.2.le, by simpa [upperCap] using (le_of_not_ge hy)⟩
  apply interior_maximal hsub hopen
  have hhalf : 0 < a.core.chord / 2 := div_pos a.core.chord_pos (by norm_num)
  have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_pos hhalf] using hp.2
  have htrig := Real.sin_sq_add_cos_sq a.upperCap.theta
  have hscale := congrArg (fun z : ℝ => a.upperCap.radius ^ 2 * z) htrig
  have hrs : a.upperCap.radius * sin a.upperCap.theta = a.core.chord / 2 := by
    simpa [upperCap] using a.upperCap.radius_mul_sin
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
  have hdisk : a.upperCap.radiusSquaredAt p < a.upperCap.radius ^ 2 := by
    simp only [OneSidedCircularCap.radiusSquaredAt,
      OneSidedCircularCap.center, upperCap, hp.1] at ⊢
    simp only [upperCap] at hscale hrsSq
    nlinarith
  have hxbounds := abs_lt.mp hp.2
  exact ⟨by linarith [hxbounds.1], hxbounds.2, by rw [hp.1]; norm_num, hdisk⟩

theorem isClosed_carrier (a : ReplacementAssembly) : IsClosed a.carrier :=
  a.core.isClosed_carrier.union a.upperCap.isClosed_carrier
private lemma chord_to_boundaryTrace (a : ReplacementAssembly) {p : PlanePoint}
    (hy : p.2 = 1) (hx : |p.1| ≤ a.core.chord / 2)
    (hpfrontier : p ∈ frontier a.carrier) : p ∈ a.boundaryTrace := by
  by_cases hstrict : |p.1| < a.core.chord / 2
  · exfalso
    have hpCarrier := a.isClosed_carrier.frontier_subset hpfrontier
    exact (mem_frontier_iff_notMem_interior hpCarrier).mp hpfrontier
      (upper_strictChord_mem_interior a ⟨hy, hstrict⟩)
  · rcases core_chord_endpoint_mem_arcs a.core (Or.inl hy) hx hstrict with
      hleft | hright
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)


theorem frontier_carrier_subset_boundaryTrace (a : ReplacementAssembly) :
    frontier a.carrier ⊆ a.boundaryTrace := by
  intro p hp
  have htop := frontier_union_subset a.core.carrier a.upperCap.carrier hp
  rcases htop with hcore | hupper
  · rw [a.core.frontier_carrier] at hcore
    rcases hcore.1 with hleft | hright | hupperChord | hlowerChord
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)
    · exact chord_to_boundaryTrace a hupperChord.1 hupperChord.2 hp
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [StripCore.lowerChordTrace, exposedLowerChord,
          HorizontalSegment.carrier] using hlowerChord)))
  · rw [a.upperCap.frontier_carrier] at hupper
    rcases hupper.2 with harc | hchord
    · exact Or.inr (Or.inr (Or.inl harc))
    · exact chord_to_boundaryTrace a hchord.1
        (by simpa [upperCap] using hchord.2) hp

private lemma mem_frontier_union_of_mem_frontier_of_not_mem
    {s t : Set PlanePoint} {p : PlanePoint}
    (hs : IsClosed s) (ht : IsClosed t) (hp : p ∈ frontier s)
    (hpt : p ∉ t) : p ∈ frontier (s ∪ t) := by
  have hps : p ∈ s := hs.frontier_subset hp
  have hpUnion : p ∈ s ∪ t := Or.inl hps
  rw [mem_frontier_iff_notMem_interior hpUnion]
  intro hi
  have hUnion : interior (s ∪ t) ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  have hCompl : tᶜ ∈ nhds p := ht.isOpen_compl.mem_nhds hpt
  have hInter : interior (s ∪ t) ∩ tᶜ ∈ nhds p :=
    Filter.inter_mem hUnion hCompl
  have hsNhd : s ∈ nhds p := Filter.mem_of_superset hInter (by
    intro q hq
    rcases interior_subset hq.1 with hqs | hqt
    · exact hqs
    · exact False.elim (hq.2 hqt))
  have hpInterior : p ∈ interior s := mem_interior_iff_mem_nhds.mpr hsNhd
  exact (mem_frontier_iff_notMem_interior hps).mp hp hpInterior

private lemma core_radius_cos_sq (c : StripCore) :
    (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  nlinarith [sq_nonneg (c.radius * c.curvature - 1)]

private theorem left_upper_endpoint_mem_frontier (a : ReplacementAssembly)
    {p : PlanePoint} (hx : p.1 = -a.core.chord / 2)
    (hy : p.2 = 1) : p ∈ frontier a.carrier := by
  have hpCore : p ∈ a.core.carrier := by
    apply Or.inl
    apply Or.inl
    exact ⟨by rw [hx], by rw [hx]; linarith [a.core.chord_pos], by simp [hy]⟩
  have hpCarrier : p ∈ a.carrier := Or.inl hpCore
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 - ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqCarrier := interior_subset (hball hqball)
  rcases hqCarrier with hcore | hupper
  · rcases hcore with (hrect | hleft) | hright
    · change -a.core.chord / 2 ≤ p.1 - ε / 2 ∧
        p.1 - ε / 2 ≤ a.core.chord / 2 ∧ |p.2| ≤ 1 at hrect
      linarith [hx]
    · have hpCircle :
          (p.1 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 =
            a.core.radius ^ 2 := by
        rw [hx, hy, StripCore.leftCenterX]
        nlinarith [core_radius_cos_sq a.core]
      have hpDiff : p.1 - a.core.leftCenterX ≤ 0 := by
        rw [hx, StripCore.leftCenterX]
        have hcos : 0 ≤ cos a.core.sideAngle := by
          rw [a.core.cos_sideAngle]
          positivity
        nlinarith [a.core.radius_pos]
      change
        ((p.1 - ε / 2 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 ≤
          a.core.radius ^ 2) ∧
            p.1 - ε / 2 ≤ -a.core.chord / 2 ∧ |p.2| ≤ 1 at hleft
      nlinarith
    · change
        ((p.1 - ε / 2 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 ≤
          a.core.radius ^ 2) ∧
            a.core.chord / 2 ≤ p.1 - ε / 2 ∧ |p.2| ≤ 1 at hright
      linarith [hx, a.core.chord_pos]
  · have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
        hupper (by simpa [upperCap, hy])
    have hxbound : |p.1 - ε / 2| ≤ a.core.chord / 2 := by
      simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
    have := (abs_le.mp hxbound).1
    linarith [hx]

private theorem right_upper_endpoint_mem_frontier (a : ReplacementAssembly)
    {p : PlanePoint} (hx : p.1 = a.core.chord / 2)
    (hy : p.2 = 1) : p ∈ frontier a.carrier := by
  have hpCore : p ∈ a.core.carrier := by
    apply Or.inl
    apply Or.inl
    exact ⟨by rw [hx]; linarith [a.core.chord_pos], by rw [hx], by simp [hy]⟩
  have hpCarrier : p ∈ a.carrier := Or.inl hpCore
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqCarrier := interior_subset (hball hqball)
  rcases hqCarrier with hcore | hupper
  · rcases hcore with (hrect | hleft) | hright
    · change -a.core.chord / 2 ≤ p.1 + ε / 2 ∧
        p.1 + ε / 2 ≤ a.core.chord / 2 ∧ |p.2| ≤ 1 at hrect
      linarith [hx]
    · change
        ((p.1 + ε / 2 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 ≤
          a.core.radius ^ 2) ∧
            p.1 + ε / 2 ≤ -a.core.chord / 2 ∧ |p.2| ≤ 1 at hleft
      linarith [hx, a.core.chord_pos]
    · have hpCircle :
          (p.1 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 =
            a.core.radius ^ 2 := by
        rw [hx, hy, StripCore.rightCenterX]
        nlinarith [core_radius_cos_sq a.core]
      have hpDiff : 0 ≤ p.1 - a.core.rightCenterX := by
        rw [hx, StripCore.rightCenterX]
        have hcos : 0 ≤ cos a.core.sideAngle := by
          rw [a.core.cos_sideAngle]
          positivity
        nlinarith [a.core.radius_pos]
      change
        ((p.1 + ε / 2 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 ≤
          a.core.radius ^ 2) ∧
            a.core.chord / 2 ≤ p.1 + ε / 2 ∧ |p.2| ≤ 1 at hright
      nlinarith
  · have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
        hupper (by simpa [upperCap, hy])
    have hxbound : |p.1 + ε / 2| ≤ a.core.chord / 2 := by
      simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
    have := (abs_le.mp hxbound).2
    linarith [hx]


private theorem leftArc_mem_frontier (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.leftArcTrace a.core) :
    p ∈ frontier a.carrier := by
  by_cases hstrict : |p.2| < 1
  · have hpCoreFrontier : p ∈ frontier a.core.carrier := by
      rw [a.core.frontier_carrier]
      exact Or.inl hp
    have hnotUpper : p ∉ a.upperCap.carrier := by
      intro hupper
      have hy : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
      exact (not_le.mpr (abs_lt.mp hstrict).2) hy
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      a.core.isClosed_carrier a.upperCap.isClosed_carrier
        hpCoreFrontier hnotUpper
  · have hyabs : |p.2| = 1 :=
      le_antisymm hp.2.2 (le_of_not_gt hstrict)
    have hy : p.2 = 1 ∨ p.2 = -1 := by
      by_cases hynonneg : 0 ≤ p.2
      · left
        rw [abs_of_nonneg hynonneg] at hyabs
        exact hyabs
      · right
        have hynonpos : p.2 ≤ 0 := le_of_not_ge hynonneg
        rw [abs_of_nonpos hynonpos] at hyabs
        linarith
    have hySq : p.2 ^ 2 = 1 := by
      rcases hy with hy | hy <;> rw [hy] <;> norm_num
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hdiff :
        p.1 - a.core.leftCenterX ≤
          -(a.core.radius * cos a.core.sideAngle) := by
      rw [StripCore.leftCenterX]
      linarith [hp.2.1]
    have hxeq :
        p.1 - a.core.leftCenterX =
          -(a.core.radius * cos a.core.sideAngle) := by
      have hdiff0 : p.1 - a.core.leftCenterX ≤ 0 := by
        nlinarith [a.core.radius_pos]
      have hsq :
          (p.1 - a.core.leftCenterX) ^ 2 =
            (a.core.radius * cos a.core.sideAngle) ^ 2 := by
        nlinarith [hp.1, core_radius_cos_sq a.core]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (p.1 - a.core.leftCenterX)
        (a.core.radius * cos a.core.sideAngle)).mp hsq
      rw [abs_of_nonpos hdiff0,
        abs_of_nonneg (mul_nonneg a.core.radius_pos.le hcos)] at habs
      linarith
    have hx : p.1 = -a.core.chord / 2 := by
      rw [StripCore.leftCenterX] at hxeq
      linarith
    rcases hy with hy | hy
    · exact left_upper_endpoint_mem_frontier a hx hy
    · apply a.exposedLowerChord_subset_frontier
      simp only [HorizontalSegment.carrier, exposedLowerChord, sub_zero]
      constructor
      · exact hy
      · rw [hx, abs_div, abs_neg, abs_of_pos a.core.chord_pos]
        norm_num

private theorem rightArc_mem_frontier (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.rightArcTrace a.core) :
    p ∈ frontier a.carrier := by
  by_cases hstrict : |p.2| < 1
  · have hpCoreFrontier : p ∈ frontier a.core.carrier := by
      rw [a.core.frontier_carrier]
      exact Or.inr (Or.inl hp)
    have hnotUpper : p ∉ a.upperCap.carrier := by
      intro hupper
      have hy : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hupper.2
      exact (not_le.mpr (abs_lt.mp hstrict).2) hy
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      a.core.isClosed_carrier a.upperCap.isClosed_carrier
        hpCoreFrontier hnotUpper
  · have hyabs : |p.2| = 1 :=
      le_antisymm hp.2.2 (le_of_not_gt hstrict)
    have hy : p.2 = 1 ∨ p.2 = -1 := by
      by_cases hynonneg : 0 ≤ p.2
      · left
        rw [abs_of_nonneg hynonneg] at hyabs
        exact hyabs
      · right
        have hynonpos : p.2 ≤ 0 := le_of_not_ge hynonneg
        rw [abs_of_nonpos hynonpos] at hyabs
        linarith
    have hySq : p.2 ^ 2 = 1 := by
      rcases hy with hy | hy <;> rw [hy] <;> norm_num
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hdiff :
        a.core.radius * cos a.core.sideAngle ≤
          p.1 - a.core.rightCenterX := by
      rw [StripCore.rightCenterX]
      linarith [hp.2.1]
    have hxeq :
        p.1 - a.core.rightCenterX =
          a.core.radius * cos a.core.sideAngle := by
      have hdiff0 : 0 ≤ p.1 - a.core.rightCenterX := by
        nlinarith [a.core.radius_pos]
      have hsq :
          (p.1 - a.core.rightCenterX) ^ 2 =
            (a.core.radius * cos a.core.sideAngle) ^ 2 := by
        nlinarith [hp.1, core_radius_cos_sq a.core]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (p.1 - a.core.rightCenterX)
        (a.core.radius * cos a.core.sideAngle)).mp hsq
      rw [abs_of_nonneg hdiff0,
        abs_of_nonneg (mul_nonneg a.core.radius_pos.le hcos)] at habs
      exact habs
    have hx : p.1 = a.core.chord / 2 := by
      rw [StripCore.rightCenterX] at hxeq
      linarith
    rcases hy with hy | hy
    · exact right_upper_endpoint_mem_frontier a hx hy
    · apply a.exposedLowerChord_subset_frontier
      simp only [HorizontalSegment.carrier, exposedLowerChord, sub_zero]
      constructor
      · exact hy
      · rw [hx, abs_of_pos
          (div_pos a.core.chord_pos (by norm_num))]

private theorem upperArc_mem_frontier (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.upperCap) :
    p ∈ frontier a.carrier := by
  by_cases hyEq : p.2 = 1
  · have hpCarrier : p ∈ a.upperCap.carrier := ⟨hp.1.le, hp.2⟩
    have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
      hpCarrier (by simpa [upperCap] using hyEq)
    have hx : |p.1| ≤ a.core.chord / 2 := by
      simpa [OneSidedCircularCap.chordCarrier, upperCap] using hchord.2
    have hn : ¬ |p.1| < a.core.chord / 2 := by
      intro hstrict
      have hhalf : 0 < a.core.chord / 2 :=
        div_pos a.core.chord_pos (by norm_num)
      have hxsq : p.1 ^ 2 < (a.core.chord / 2) ^ 2 := by
        rw [sq_lt_sq]
        simpa [abs_of_pos hhalf] using hstrict
      have htrig := Real.sin_sq_add_cos_sq a.upperCap.theta
      have hscale := congrArg
        (fun z : ℝ => a.upperCap.radius ^ 2 * z) htrig
      have hrs : a.upperCap.radius * sin a.upperCap.theta =
          a.core.chord / 2 := by
        simpa [upperCap] using a.upperCap.radius_mul_sin
      have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
      have hpEq := hp.1
      simp only [OneSidedCircularCap.radiusSquaredAt] at hpEq
      rw [hyEq] at hpEq
      simp only [OneSidedCircularCap.center, upperCap] at hpEq
      simp only [upperCap] at hscale hrsSq
      nlinarith
    rcases core_chord_endpoint_mem_arcs a.core (Or.inl hyEq) hx hn with
      hleft | hright
    · exact leftArc_mem_frontier a hleft
    · exact rightArc_mem_frontier a hright
  · have hpCapFrontier : p ∈ frontier a.upperCap.carrier := by
      rw [a.upperCap.frontier_carrier]
      exact Or.inl hp
    have hnotCore : p ∉ a.core.carrier := by
      intro hcore
      have hyCore := a.core.carrier_y_bounds hcore
      have hy : (1 : ℝ) < p.2 := by
        have hge : (1 : ℝ) ≤ p.2 := by simpa [upperCap] using hp.2
        exact lt_of_le_of_ne hge (Ne.symm hyEq)
      linarith [le_trans (le_abs_self p.2) hyCore]
    have hcapCore : p ∈ frontier
        (a.upperCap.carrier ∪ a.core.carrier) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.upperCap.isClosed_carrier a.core.isClosed_carrier
          hpCapFrontier hnotCore
    rw [union_comm a.upperCap.carrier a.core.carrier] at hcapCore
    exact hcapCore

theorem boundaryTrace_subset_frontier_carrier (a : ReplacementAssembly) :
    a.boundaryTrace ⊆ frontier a.carrier := by
  rintro p (hleft | hright | hupper | hlower)
  · exact leftArc_mem_frontier a hleft
  · exact rightArc_mem_frontier a hright
  · exact upperArc_mem_frontier a hupper
  · exact a.exposedLowerChord_subset_frontier hlower

theorem frontier_carrier (a : ReplacementAssembly) :
    frontier a.carrier = a.boundaryTrace :=
  Set.Subset.antisymm a.frontier_carrier_subset_boundaryTrace
    a.boundaryTrace_subset_frontier_carrier

end ReplacementAssembly

/-- Admissible competitors include arbitrary finite-perimeter regions, as well
as the two piecewise-circular constructors whose exact formulas are proved in
the bridge.  The replacement constructor is not restricted by stationarity,
Snell, or equal-curvature conditions. -/
inductive AdmissibleCompetitor (lam : ℝ) where
  | empty
  | general (region : FinitePerimeterRegion lam)
  | fourArc (a : FourArcAssembly)
  | replacement (a : ReplacementAssembly)

namespace AdmissibleCompetitor

/-- Coordinate carrier of an admissible regular competitor. -/
def carrier {lam : ℝ} : AdmissibleCompetitor lam → Set PlanePoint
  | .empty => ∅
  | .general region => region.carrier
  | .fourArc a => a.carrier
  | .replacement a => a.carrier

/-- Weighted area on the regular constructor model. -/
def WeightedArea {lam : ℝ} : AdmissibleCompetitor lam → ℝ
  | .empty => 0
  | .general region => region.weightedArea
  | .fourArc a => a.weightedArea lam
  | .replacement a => a.weightedArea lam

/-- Weighted perimeter is canonically determined by the complete topological
frontier of the competitor's coordinate carrier. -/
def WeightedPerimeter {lam : ℝ} (r : AdmissibleCompetitor lam) : ℝ :=
  _root_.WeightedPerimeter lam (FrontierMeasure r.carrier)

/-- The constructor-level weighted area is always the canonical density
integral over the constructor's coordinate carrier. -/
theorem weightedArea_eq_carrier {lam : ℝ} (r : AdmissibleCompetitor lam) :
    r.WeightedArea = _root_.WeightedArea lam r.carrier := by
  cases r with
  | empty =>
      simp [AdmissibleCompetitor.WeightedArea,
        AdmissibleCompetitor.carrier, _root_.WeightedArea]
  | general region => rfl
  | fourArc a => rfl
  | replacement a => rfl

theorem measurableSet_carrier {lam : ℝ} (r : AdmissibleCompetitor lam) :
    MeasurableSet r.carrier := by
  cases r with
  | empty => exact MeasurableSet.empty
  | general region => exact region.measurable_carrier
  | fourArc a => exact a.measurableSet_carrier
  | replacement a => exact a.measurableSet_carrier

end AdmissibleCompetitor
