/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourSourceGeometry

/-!
# Symmetry-free bilateral Figure-4 incidence

This module separates the actual source and circle-incidence hypotheses from the
vertical-reflection conclusions currently required by `CMVFigureFour.SourceGeometry`.
All four circles have the same supplied radius, but their centers are independently
placed.  The four signed Snell equations are retained as upstream local laws.

The elementary circle lemmas below are denominator-free.  In particular, the
opposite-offset lemma permits both horizontal radial offsets to vanish.
-/

open Set
open MeasureTheory
open Real


noncomputable section

namespace CMVFigureFour

/-- Horizontal placement preserves the literal squared circle equation. -/
@[simp] theorem circleValue_horizontalTranslation
    (t : ℝ) (center : PlanePoint) (radius : ℝ) (p : PlanePoint) :
    circleValue (horizontalTranslation t center) radius
        (horizontalTranslation t p) =
      circleValue center radius p := by
  simp only [circleValue, horizontalTranslation_apply]
  ring
/-- A Euclidean circle level has zero planar volume.  This low-level Fubini
lemma is shared by the concrete source specimens. -/
theorem volume_circleValue_eq_zero
    (center : PlanePoint) (radius : ℝ) :
    volume {p : PlanePoint | circleValue center radius p = 0} = 0 := by
  have hmeas :
      MeasurableSet {p : PlanePoint |
        circleValue center radius p = 0} := by
    exact (isClosed_eq (by
      unfold circleValue
      fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  have hfiber : ∀ y : ℝ,
      volume ((fun x : ℝ => (x, y)) ⁻¹'
        {p : PlanePoint | circleValue center radius p = 0}) = 0 := by
    intro y
    let q : ℝ := radius ^ 2 - (y - center.2) ^ 2
    have hset :
        (fun x : ℝ => (x, y)) ⁻¹'
            {p : PlanePoint | circleValue center radius p = 0} =
          {x : ℝ | (x - center.1) ^ 2 = q} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, circleValue]
      unfold q
      constructor <;> intro h <;> nlinarith
    rw [hset]
    by_cases hq : 0 ≤ q
    · apply Set.Finite.measure_zero
      refine ({center.1 + √q, center.1 - √q} : Set ℝ).toFinite.subset ?_
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff]
      have hsqrt : (√q) ^ 2 = q := Real.sq_sqrt hq
      rw [← hsqrt] at hx
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hx with hx | hx
      · left
        linarith
      · right
        linarith
    · have hempty : {x : ℝ | (x - center.1) ^ 2 = q} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hx
        exact hq (by nlinarith [sq_nonneg (x - center.1)])
      simp [hempty]
  simp_rw [hfiber]
  simp
/-- Every nonnegative-radius closed circle sublevel is bounded in the
coordinate-plane metric. -/
theorem isBounded_circleValue_le_zero
    (center : PlanePoint) {radius : ℝ} (hradius : 0 ≤ radius) :
    Bornology.IsBounded
      {p : PlanePoint | circleValue center radius p ≤ 0} := by
  apply ((Metric.isBounded_Icc (center.1 - radius)
      (center.1 + radius)).prod
    (Metric.isBounded_Icc (center.2 - radius)
      (center.2 + radius))).subset
  intro p hp
  change
    (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 -
      radius ^ 2 ≤ 0 at hp
  constructor
  · constructor <;> nlinarith [sq_nonneg (p.2 - center.2)]
  · constructor <;> nlinarith [sq_nonneg (p.1 - center.1)]

/-- Every four-arc carrier is bounded. -/
theorem isBounded_fourArcAssembly_carrier (a : FourArcAssembly) :
    Bornology.IsBounded a.carrier := by
  have hrect :
      Bornology.IsBounded a.core.rectangleCarrier := by
    apply ((Metric.isBounded_Icc (-a.core.chord / 2)
        (a.core.chord / 2)).prod
      (Metric.isBounded_Icc (-1 : ℝ) 1)).subset
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, abs_le.mp hp.2.2⟩
  have hleft :
      Bornology.IsBounded a.core.leftCapCarrier := by
    apply (isBounded_circleValue_le_zero
      (a.core.leftCenterX, 0) a.core.radius_pos.le).subset
    intro p hp
    change circleValue (a.core.leftCenterX, 0) a.core.radius p ≤ 0
    unfold circleValue
    dsimp only
    nlinarith [hp.1]
  have hright :
      Bornology.IsBounded a.core.rightCapCarrier := by
    apply (isBounded_circleValue_le_zero
      (a.core.rightCenterX, 0) a.core.radius_pos.le).subset
    intro p hp
    change circleValue (a.core.rightCenterX, 0) a.core.radius p ≤ 0
    unfold circleValue
    dsimp only
    nlinarith [hp.1]
  have hcore : Bornology.IsBounded a.core.carrier := by
    exact (hrect.union hleft).union hright
  have hupper :
      Bornology.IsBounded a.upperCap.carrier := by
    apply (isBounded_circleValue_le_zero
      a.upperCap.center a.upperCap.radius_pos.le).subset
    intro p hp
    change circleValue a.upperCap.center a.upperCap.radius p ≤ 0
    have hle := hp.1
    unfold OneSidedCircularCap.radiusSquaredAt at hle
    unfold circleValue
    nlinarith
  have hlower :
      Bornology.IsBounded a.lowerCap.carrier := by
    apply (isBounded_circleValue_le_zero
      a.lowerCap.center a.lowerCap.radius_pos.le).subset
    intro p hp
    change circleValue a.lowerCap.center a.lowerCap.radius p ≤ 0
    have hle := hp.1
    unfold OneSidedCircularCap.radiusSquaredAt at hle
    unfold circleValue
    nlinarith
  exact (hcore.union hupper).union hlower

/-- The complete four-arc frontier is planar-null. -/
theorem volume_frontier_fourArcAssembly (a : FourArcAssembly) :
    volume (frontier a.carrier) = 0 := by
  have hleft :
      volume (StripCore.leftArcTrace a.core) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue (a.core.leftCenterX, 0) a.core.radius p = 0})
    · intro p hp
      change circleValue (a.core.leftCenterX, 0) a.core.radius p = 0
      unfold circleValue
      dsimp only
      nlinarith [hp.1]
    · exact volume_circleValue_eq_zero _ _
  have hright :
      volume (StripCore.rightArcTrace a.core) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue (a.core.rightCenterX, 0) a.core.radius p = 0})
    · intro p hp
      change circleValue (a.core.rightCenterX, 0) a.core.radius p = 0
      unfold circleValue
      dsimp only
      nlinarith [hp.1]
    · exact volume_circleValue_eq_zero _ _
  have hupper :
      volume (OneSidedCircularCap.arcTrace a.upperCap) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue a.upperCap.center a.upperCap.radius p = 0})
    · intro p hp
      change circleValue a.upperCap.center a.upperCap.radius p = 0
      have heq := hp.1
      unfold OneSidedCircularCap.radiusSquaredAt at heq
      unfold circleValue
      nlinarith [heq]
    · exact volume_circleValue_eq_zero _ _
  have hlower :
      volume (OneSidedCircularCap.arcTrace a.lowerCap) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue a.lowerCap.center a.lowerCap.radius p = 0})
    · intro p hp
      change circleValue a.lowerCap.center a.lowerCap.radius p = 0
      have heq := hp.1
      unfold OneSidedCircularCap.radiusSquaredAt at heq
      unfold circleValue
      nlinarith [heq]
    · exact volume_circleValue_eq_zero _ _
  rw [a.frontier_carrier, FourArcAssembly.boundaryTrace]
  apply le_antisymm
  · calc
      volume (StripCore.leftArcTrace a.core ∪
          (StripCore.rightArcTrace a.core ∪
            (OneSidedCircularCap.arcTrace a.upperCap ∪
              OneSidedCircularCap.arcTrace a.lowerCap))) ≤
          volume (StripCore.leftArcTrace a.core) +
            volume (StripCore.rightArcTrace a.core ∪
              (OneSidedCircularCap.arcTrace a.upperCap ∪
                OneSidedCircularCap.arcTrace a.lowerCap)) :=
        measure_union_le _ _
      _ ≤ volume (StripCore.leftArcTrace a.core) +
          (volume (StripCore.rightArcTrace a.core) +
            volume (OneSidedCircularCap.arcTrace a.upperCap ∪
              OneSidedCircularCap.arcTrace a.lowerCap)) := by
        gcongr
        exact measure_union_le _ _
      _ ≤ volume (StripCore.leftArcTrace a.core) +
          (volume (StripCore.rightArcTrace a.core) +
            (volume (OneSidedCircularCap.arcTrace a.upperCap) +
              volume (OneSidedCircularCap.arcTrace a.lowerCap))) := by
        gcongr
        exact measure_union_le _ _
      _ = 0 := by rw [hleft, hright, hupper, hlower]; norm_num
  · exact bot_le

/-- The open interior of a four-arc carrier agrees almost everywhere with its
literal closed carrier. -/
theorem interior_fourArcAssembly_ae_eq_carrier (a : FourArcAssembly) :
    interior a.carrier =ᵐ[volume] a.carrier := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpInterior, hpNotCarrier⟩
      exact (hpNotCarrier (interior_subset hpInterior)).elim
    · exact measure_empty
  · apply measure_mono_null (t := frontier a.carrier)
    · rintro p ⟨hpCarrier, hpNotInterior⟩
      rw [mem_frontier_iff_notMem_interior hpCarrier]
      exact hpNotInterior
    · exact volume_frontier_fourArcAssembly a

/-- The literal closed four-arc carrier and its bounded open interior form an
actual source representative. -/
theorem fourArcSourceRepresentative (a : FourArcAssembly) :
    SourceRepresentative a.carrier (interior a.carrier) where
  representative_open := isOpen_interior
  representative_bounded :=
    (isBounded_fourArcAssembly_carrier a).subset interior_subset
  source_ae_representative :=
    (interior_fourArcAssembly_ae_eq_carrier a).symm

/-- A local identification with a closed disk identifies the open interior
with the strict disk side whenever the local circle itself is frontier. -/
theorem locallyOneSided_interior_of_local_closedDisk
    {C V : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hCclosed : IsClosed C) (hVopen : IsOpen V) (hpV : p ∈ V)
    (hlocal :
      C ∩ V = V ∩ {q | circleValue center radius q ≤ 0})
    (hzero :
      V ∩ {q | circleValue center radius q = 0} ⊆ frontier C) :
    LocallyOneSided (interior C) center radius p := by
  refine ⟨.inside, V, hVopen, hpV, ?_⟩
  ext q
  simp only [mem_inter_iff, mem_ofPred_eq, CircleSide.sign, one_mul]
  constructor
  · rintro ⟨hqInterior, hqV⟩
    have hqC : q ∈ C := interior_subset hqInterior
    have hqDisk :
        q ∈ V ∩ {z | circleValue center radius z ≤ 0} := by
      rw [← hlocal]
      exact ⟨hqC, hqV⟩
    refine ⟨hqV, ?_⟩
    by_contra hnlt
    have heq : circleValue center radius q = 0 :=
      le_antisymm hqDisk.2 (le_of_not_gt hnlt)
    have hqFrontier := hzero ⟨hqV, heq⟩
    exact
      ((mem_frontier_iff_notMem_interior
        (hCclosed.frontier_subset hqFrontier)).mp hqFrontier) hqInterior
  · rintro ⟨hqV, hqStrict⟩
    refine ⟨?_, hqV⟩
    let W : Set PlanePoint :=
      V ∩ {z | circleValue center radius z < 0}
    have hCircleContinuous :
        Continuous (fun z => circleValue center radius z) := by
      unfold circleValue
      fun_prop
    have hWopen : IsOpen W :=
      hVopen.inter (isOpen_lt hCircleContinuous continuous_const)
    have hWsub : W ⊆ C := by
      intro z hz
      have hzlt : circleValue center radius z < 0 := hz.2
      have hzClosed :
          z ∈ V ∩ {w | circleValue center radius w ≤ 0} :=
        ⟨hz.1, hzlt.le⟩
      rw [← hlocal] at hzClosed
      exact hzClosed.1
    exact interior_maximal hWsub hWopen ⟨hqV, hqStrict⟩


/-- Removing the two chord endpoints from a cap trace makes its half-plane
constraint strict. -/
theorem OneSidedCircularCap.arcTrace_strict_side_of_ne_endpoints
    (c : OneSidedCircularCap) {p : PlanePoint}
    (hp : p ∈ c.arcTrace)
    (hleft : p ≠ c.leftEndpoint) (hright : p ≠ c.rightEndpoint) :
    match c.side with
    | .upper => c.baseY < p.2
    | .lower => p.2 < c.baseY := by
  have htrig := Real.sin_sq_add_cos_sq c.theta
  have hscaled := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hrs := c.radius_mul_sin
  cases hside : c.side with
  | upper =>
      simp only [OneSidedCircularCap.arcTrace, hside, mem_ofPred_eq] at hp
      by_contra hn
      have hyeq : p.2 = c.baseY := le_antisymm (le_of_not_gt hn) hp.2
      have hcircle := hp.1
      simp only [OneSidedCircularCap.radiusSquaredAt,
        OneSidedCircularCap.center, hside, hyeq] at hcircle
      have hxsq :
          (p.1 - c.midpointX) ^ 2 = (c.chord / 2) ^ 2 := by
        rw [← hrs]
        nlinarith
      by_cases hx : p.1 ≤ c.midpointX
      · apply hleft
        rw [OneSidedCircularCap.leftEndpoint]
        apply Prod.ext
        · dsimp only
          nlinarith [c.chord_pos]
        · exact hyeq
      · apply hright
        rw [OneSidedCircularCap.rightEndpoint]
        apply Prod.ext
        · dsimp only
          nlinarith [c.chord_pos]
        · exact hyeq
  | lower =>
      simp only [OneSidedCircularCap.arcTrace, hside, mem_ofPred_eq] at hp
      by_contra hn
      have hyeq : p.2 = c.baseY := le_antisymm hp.2 (le_of_not_gt hn)
      have hcircle := hp.1
      simp only [OneSidedCircularCap.radiusSquaredAt,
        OneSidedCircularCap.center, hside, hyeq] at hcircle
      have hxsq :
          (p.1 - c.midpointX) ^ 2 = (c.chord / 2) ^ 2 := by
        rw [← hrs]
        nlinarith
      by_cases hx : p.1 ≤ c.midpointX
      · apply hleft
        rw [OneSidedCircularCap.leftEndpoint]
        apply Prod.ext
        · dsimp only
          nlinarith [c.chord_pos]
        · exact hyeq
      · apply hright
        rw [OneSidedCircularCap.rightEndpoint]
        apply Prod.ext
        · dsimp only
          nlinarith [c.chord_pos]
        · exact hyeq

/-- A left strip-circle trace point away from its two junctions has strict
strip height. -/
theorem StripCore.leftArcTrace_strict_height_of_ne_endpoints
    (c : StripCore) {p : PlanePoint}
    (hp : p ∈ StripCore.leftArcTrace c)
    (hupper : p ≠ (-c.chord / 2, 1))
    (hlower : p ≠ (-c.chord / 2, -1)) :
    |p.2| < 1 := by
  by_contra hn
  have hyabs : |p.2| = 1 :=
    le_antisymm hp.2.2 (le_of_not_gt hn)
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
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hcosSq :
      (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
    nlinarith [sq_nonneg (c.radius * c.curvature - 1)]
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hdiff :
      p.1 - c.leftCenterX ≤ -(c.radius * cos c.sideAngle) := by
    rw [StripCore.leftCenterX]
    linarith [hp.2.1]
  have hdiff0 : p.1 - c.leftCenterX ≤ 0 := by
    nlinarith [c.radius_pos]
  have hsq :
      (p.1 - c.leftCenterX) ^ 2 =
        (c.radius * cos c.sideAngle) ^ 2 := by
    nlinarith [hp.1, hcosSq]
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (p.1 - c.leftCenterX) (c.radius * cos c.sideAngle)).mp hsq
  rw [abs_of_nonpos hdiff0,
    abs_of_nonneg (mul_nonneg c.radius_pos.le hcos)] at habs
  have hx : p.1 = -c.chord / 2 := by
    rw [StripCore.leftCenterX] at habs
    linarith
  rcases hy with hy | hy
  · apply hupper
    exact Prod.ext hx hy
  · apply hlower
    exact Prod.ext hx hy

/-- A right strip-circle trace point away from its two junctions has strict
strip height. -/
theorem StripCore.rightArcTrace_strict_height_of_ne_endpoints
    (c : StripCore) {p : PlanePoint}
    (hp : p ∈ StripCore.rightArcTrace c)
    (hupper : p ≠ (c.chord / 2, 1))
    (hlower : p ≠ (c.chord / 2, -1)) :
    |p.2| < 1 := by
  by_contra hn
  have hyabs : |p.2| = 1 :=
    le_antisymm hp.2.2 (le_of_not_gt hn)
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
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hcosSq :
      (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
    nlinarith [sq_nonneg (c.radius * c.curvature - 1)]
  have hcos : 0 ≤ cos c.sideAngle := by
    rw [c.cos_sideAngle]
    positivity
  have hdiff :
      c.radius * cos c.sideAngle ≤ p.1 - c.rightCenterX := by
    rw [StripCore.rightCenterX]
    linarith [hp.2.1]
  have hdiff0 : 0 ≤ p.1 - c.rightCenterX := by
    nlinarith [c.radius_pos]
  have hsq :
      (p.1 - c.rightCenterX) ^ 2 =
        (c.radius * cos c.sideAngle) ^ 2 := by
    nlinarith [hp.1, hcosSq]
  have habs := (sq_eq_sq_iff_abs_eq_abs
    (p.1 - c.rightCenterX) (c.radius * cos c.sideAngle)).mp hsq
  rw [abs_of_nonneg hdiff0,
    abs_of_nonneg (mul_nonneg c.radius_pos.le hcos)] at habs
  have hx : p.1 = c.chord / 2 := by
    rw [StripCore.rightCenterX] at habs
    linarith
  rcases hy with hy | hy
  · apply hupper
    exact Prod.ext hx hy
  · apply hlower
    exact Prod.ext hx hy

/-- The actual open four-arc interior is locally the inside of the upper
supporting circle away from its two junctions. -/
theorem FourArcAssembly.upper_locallyOneSided
    (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ a.upperCap.arcTrace)
    (hleft : p ≠ a.upperCap.leftEndpoint)
    (hright : p ≠ a.upperCap.rightEndpoint) :
    LocallyOneSided (interior a.carrier) a.upperCap.center
      a.upperCap.radius p := by
  let V : Set PlanePoint := {q | 1 < q.2}
  have hVopen : IsOpen V := isOpen_lt continuous_const continuous_snd
  have hpV : p ∈ V := by
    have hstrict :=
      CMVFigureFour.OneSidedCircularCap.arcTrace_strict_side_of_ne_endpoints
        a.upperCap hp hleft hright
    simpa [V, FourArcAssembly.upperCap] using hstrict
  have hlocal :
      a.carrier ∩ V =
        V ∩ {q | circleValue a.upperCap.center a.upperCap.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqy⟩
      refine ⟨hqy, ?_⟩
      rw [FourArcAssembly.carrier] at hqCarrier
      rcases hqCarrier with (hqCore | hqUpper) | hqLower
      · have hy := a.core.carrier_y_bounds hqCore
        change 1 < q.2 at hqy
        exact (by nlinarith [le_abs_self q.2])
      · have hle := hqUpper.1
        unfold OneSidedCircularCap.radiusSquaredAt at hle
        unfold circleValue
        nlinarith [hle]
      · have hy : q.2 ≤ (-1 : ℝ) := by
          simpa [FourArcAssembly.lowerCap] using hqLower.2
        change 1 < q.2 at hqy
        linarith
    · rintro ⟨hqy, hqCircle⟩
      refine ⟨?_, hqy⟩
      rw [FourArcAssembly.carrier]
      apply Or.inl
      apply Or.inr
      constructor
      · unfold OneSidedCircularCap.radiusSquaredAt
        unfold circleValue at hqCircle
        nlinarith
      · unfold V at hqy
        simpa [FourArcAssembly.upperCap] using hqy.le
  have hzero :
      V ∩ {q | circleValue a.upperCap.center a.upperCap.radius q = 0} ⊆
        frontier a.carrier := by
    intro q hq
    apply _root_.FourArcAssembly.boundaryTrace_subset_frontier_carrier a
    apply Or.inr
    apply Or.inr
    apply Or.inl
    constructor
    · have hz := hq.2
      unfold OneSidedCircularCap.radiusSquaredAt
      unfold circleValue at hz
      exact sub_eq_zero.mp hz
    · unfold V at hq
      simpa [FourArcAssembly.upperCap] using hq.1.le
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- The actual open four-arc interior is locally the inside of the lower
supporting circle away from its two junctions. -/
theorem FourArcAssembly.lower_locallyOneSided
    (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ a.lowerCap.arcTrace)
    (hleft : p ≠ a.lowerCap.leftEndpoint)
    (hright : p ≠ a.lowerCap.rightEndpoint) :
    LocallyOneSided (interior a.carrier) a.lowerCap.center
      a.lowerCap.radius p := by
  let V : Set PlanePoint := {q | q.2 < -1}
  have hVopen : IsOpen V := isOpen_lt continuous_snd continuous_const
  have hpV : p ∈ V := by
    have hstrict :=
      CMVFigureFour.OneSidedCircularCap.arcTrace_strict_side_of_ne_endpoints
        a.lowerCap hp hleft hright
    simpa [V, FourArcAssembly.lowerCap] using hstrict
  have hlocal :
      a.carrier ∩ V =
        V ∩ {q | circleValue a.lowerCap.center a.lowerCap.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqy⟩
      refine ⟨hqy, ?_⟩
      rw [FourArcAssembly.carrier] at hqCarrier
      rcases hqCarrier with (hqCore | hqUpper) | hqLower
      · have hy := a.core.carrier_y_bounds hqCore
        change q.2 < -1 at hqy
        exact (by nlinarith [neg_le_abs q.2])
      · have hy : (1 : ℝ) ≤ q.2 := by
          simpa [FourArcAssembly.upperCap] using hqUpper.2
        change q.2 < -1 at hqy
        linarith
      · have hle := hqLower.1
        unfold OneSidedCircularCap.radiusSquaredAt at hle
        unfold circleValue
        nlinarith [hle]
    · rintro ⟨hqy, hqCircle⟩
      refine ⟨?_, hqy⟩
      rw [FourArcAssembly.carrier]
      apply Or.inr
      constructor
      · unfold OneSidedCircularCap.radiusSquaredAt
        unfold circleValue at hqCircle
        nlinarith
      · unfold V at hqy
        simpa [FourArcAssembly.lowerCap] using hqy.le
  have hzero :
      V ∩ {q | circleValue a.lowerCap.center a.lowerCap.radius q = 0} ⊆
        frontier a.carrier := by
    intro q hq
    apply _root_.FourArcAssembly.boundaryTrace_subset_frontier_carrier a
    apply Or.inr
    apply Or.inr
    apply Or.inr
    constructor
    · have hz := hq.2
      unfold OneSidedCircularCap.radiusSquaredAt
      unfold circleValue at hz
      exact sub_eq_zero.mp hz
    · unfold V at hq
      simpa [FourArcAssembly.lowerCap] using hq.1.le
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- The actual open four-arc interior is locally the inside of the left strip
circle away from its two interface junctions. -/
theorem FourArcAssembly.left_locallyOneSided
    (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.leftArcTrace a.core)
    (hupper : p ≠ (-a.core.chord / 2, 1))
    (hlower : p ≠ (-a.core.chord / 2, -1)) :
    LocallyOneSided (interior a.carrier)
      (a.core.leftCenterX, 0) a.core.radius p := by
  have hpHeight :=
    CMVFigureFour.StripCore.leftArcTrace_strict_height_of_ne_endpoints
      a.core hp hupper hlower
  have hpLeft : p.1 < -a.core.chord / 2 := by
    have hcosSq :
        (a.core.radius * cos a.core.sideAngle) ^ 2 =
          a.core.radius ^ 2 - 1 := by
      have hrc : a.core.radius * a.core.curvature = 1 := by
        rw [StripCore.radius]
        field_simp [ne_of_gt a.core.curvature_pos]
      have htrig := Real.sin_sq_add_cos_sq a.core.sideAngle
      rw [a.core.sin_sideAngle] at htrig
      have hscale :=
        congrArg (fun z : ℝ => a.core.radius ^ 2 * z) htrig
      nlinarith [sq_nonneg (a.core.radius * a.core.curvature - 1)]
    by_contra hn
    have hx : p.1 = -a.core.chord / 2 :=
      le_antisymm hp.2.1 (le_of_not_gt hn)
    have heq := hp.1
    rw [hx, StripCore.leftCenterX] at heq
    have hy := abs_lt.mp hpHeight
    nlinarith
  let V : Set PlanePoint :=
    {q | |q.2| < 1 ∧ q.1 < -a.core.chord / 2}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_snd.abs continuous_const).inter
      (isOpen_lt continuous_fst continuous_const)
  have hpV : p ∈ V := ⟨hpHeight, hpLeft⟩
  have hlocal :
      a.carrier ∩ V =
        V ∩ {q |
          circleValue (a.core.leftCenterX, 0) a.core.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      refine ⟨hqV, ?_⟩
      rw [FourArcAssembly.carrier] at hqCarrier
      rcases hqCarrier with (hqCore | hqUpper) | hqLower
      · rcases hqCore with (hqRect | hqLeft) | hqRight
        · exact (by linarith [hqRect.1, hqV.2])
        · have hle := hqLeft.1
          change
            circleValue (a.core.leftCenterX, 0) a.core.radius q ≤ 0
          unfold circleValue
          dsimp only
          nlinarith
        · exact (by
            have := hqRight.2.1
            linarith [hqV.2, a.core.chord_pos])
      · have hy : (1 : ℝ) ≤ q.2 := by
          simpa [FourArcAssembly.upperCap] using hqUpper.2
        exact (by linarith [(abs_lt.mp hqV.1).2])
      · have hy : q.2 ≤ (-1 : ℝ) := by
          simpa [FourArcAssembly.lowerCap] using hqLower.2
        exact (by linarith [(abs_lt.mp hqV.1).1])
    · rintro ⟨hqV, hqCircle⟩
      refine ⟨?_, hqV⟩
      have hleftCarrier : q ∈ a.core.leftCapCarrier := by
        constructor
        · unfold circleValue at hqCircle
          dsimp only at hqCircle
          nlinarith
        · exact ⟨hqV.2.le, hqV.1.le⟩
      exact Or.inl (Or.inl (Or.inl (Or.inr hleftCarrier)))
  have hzero :
      V ∩ {q |
        circleValue (a.core.leftCenterX, 0) a.core.radius q = 0} ⊆
          frontier a.carrier := by
    intro q hq
    apply _root_.FourArcAssembly.boundaryTrace_subset_frontier_carrier a
    apply Or.inl
    constructor
    · have hz : circleValue (a.core.leftCenterX, 0) a.core.radius q = 0 :=
        hq.2
      unfold circleValue at hz
      dsimp only at hz
      nlinarith
    · exact ⟨hq.1.2.le, hq.1.1.le⟩
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- The actual open four-arc interior is locally the inside of the right strip
circle away from its two interface junctions. -/
theorem FourArcAssembly.right_locallyOneSided
    (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.rightArcTrace a.core)
    (hupper : p ≠ (a.core.chord / 2, 1))
    (hlower : p ≠ (a.core.chord / 2, -1)) :
    LocallyOneSided (interior a.carrier)
      (a.core.rightCenterX, 0) a.core.radius p := by
  have hpHeight :=
    CMVFigureFour.StripCore.rightArcTrace_strict_height_of_ne_endpoints
      a.core hp hupper hlower
  have hpRight : a.core.chord / 2 < p.1 := by
    have hcosSq :
        (a.core.radius * cos a.core.sideAngle) ^ 2 =
          a.core.radius ^ 2 - 1 := by
      have hrc : a.core.radius * a.core.curvature = 1 := by
        rw [StripCore.radius]
        field_simp [ne_of_gt a.core.curvature_pos]
      have htrig := Real.sin_sq_add_cos_sq a.core.sideAngle
      rw [a.core.sin_sideAngle] at htrig
      have hscale :=
        congrArg (fun z : ℝ => a.core.radius ^ 2 * z) htrig
      nlinarith [sq_nonneg (a.core.radius * a.core.curvature - 1)]
    by_contra hn
    have hx : p.1 = a.core.chord / 2 :=
      le_antisymm (le_of_not_gt hn) hp.2.1
    have heq := hp.1
    rw [hx, StripCore.rightCenterX] at heq
    have hy := abs_lt.mp hpHeight
    nlinarith
  let V : Set PlanePoint :=
    {q | |q.2| < 1 ∧ a.core.chord / 2 < q.1}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_snd.abs continuous_const).inter
      (isOpen_lt continuous_const continuous_fst)
  have hpV : p ∈ V := ⟨hpHeight, hpRight⟩
  have hlocal :
      a.carrier ∩ V =
        V ∩ {q |
          circleValue (a.core.rightCenterX, 0) a.core.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      refine ⟨hqV, ?_⟩
      rw [FourArcAssembly.carrier] at hqCarrier
      rcases hqCarrier with (hqCore | hqUpper) | hqLower
      · rcases hqCore with (hqRect | hqLeft) | hqRight
        · exact (by linarith [hqRect.2.1, hqV.2])
        · exact (by
            have := hqLeft.2.1
            linarith [hqV.2, a.core.chord_pos])
        · have hle := hqRight.1
          change
            circleValue (a.core.rightCenterX, 0) a.core.radius q ≤ 0
          unfold circleValue
          dsimp only
          nlinarith
      · have hy : (1 : ℝ) ≤ q.2 := by
          simpa [FourArcAssembly.upperCap] using hqUpper.2
        exact (by linarith [(abs_lt.mp hqV.1).2])
      · have hy : q.2 ≤ (-1 : ℝ) := by
          simpa [FourArcAssembly.lowerCap] using hqLower.2
        exact (by linarith [(abs_lt.mp hqV.1).1])
    · rintro ⟨hqV, hqCircle⟩
      refine ⟨?_, hqV⟩
      have hrightCarrier : q ∈ a.core.rightCapCarrier := by
        constructor
        · unfold circleValue at hqCircle
          dsimp only at hqCircle
          nlinarith
        · exact ⟨hqV.2.le, hqV.1.le⟩
      exact Or.inl (Or.inl (Or.inr hrightCarrier))
  have hzero :
      V ∩ {q |
        circleValue (a.core.rightCenterX, 0) a.core.radius q = 0} ⊆
          frontier a.carrier := by
    intro q hq
    apply _root_.FourArcAssembly.boundaryTrace_subset_frontier_carrier a
    apply Or.inr
    apply Or.inl
    constructor
    · have hz : circleValue (a.core.rightCenterX, 0) a.core.radius q = 0 :=
        hq.2
      unfold circleValue at hz
      dsimp only at hz
      nlinarith
    · exact ⟨hq.1.2.le, hq.1.1.le⟩
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- Both literal chord endpoints lie on a cap's selected circular trace. -/
theorem OneSidedCircularCap.leftEndpoint_mem_arcTrace
    (c : OneSidedCircularCap) : c.leftEndpoint ∈ c.arcTrace := by
  have htrig := Real.sin_sq_add_cos_sq c.theta
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  ring_nf at hscale
  have hrs := c.radius_mul_sin
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
  ring_nf at hrsSq
  cases hside : c.side <;>
    simp only [OneSidedCircularCap.arcTrace,
      OneSidedCircularCap.radiusSquaredAt, OneSidedCircularCap.leftEndpoint,
      OneSidedCircularCap.center, hside, mem_ofPred_eq]
  all_goals constructor
  all_goals try simp
  all_goals nlinarith

theorem OneSidedCircularCap.rightEndpoint_mem_arcTrace
    (c : OneSidedCircularCap) : c.rightEndpoint ∈ c.arcTrace := by
  have htrig := Real.sin_sq_add_cos_sq c.theta
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  ring_nf at hscale
  have hrs := c.radius_mul_sin
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) hrs
  ring_nf at hrsSq
  cases hside : c.side <;>
    simp only [OneSidedCircularCap.arcTrace,
      OneSidedCircularCap.radiusSquaredAt, OneSidedCircularCap.rightEndpoint,
      OneSidedCircularCap.center, hside, mem_ofPred_eq]
  all_goals constructor
  all_goals try simp
  all_goals nlinarith

/-- The strip constructor's horizontal radial offset has the endpoint square
forced by unit interface height. -/
theorem StripCore.radius_mul_cos_sq (c : StripCore) :
    (c.radius * cos c.sideAngle) ^ 2 = c.radius ^ 2 - 1 := by
  have hrc : c.radius * c.curvature = 1 := by
    rw [StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have htrig := Real.sin_sq_add_cos_sq c.sideAngle
  rw [c.sin_sideAngle] at htrig
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  nlinarith [sq_nonneg (c.radius * c.curvature - 1)]

/-- The four strip-interface endpoints lie on their respective side traces. -/
theorem StripCore.upperLeft_mem_leftArcTrace (c : StripCore) :
    (-c.chord / 2, 1) ∈ c.leftArcTrace := by
  change
    ((-c.chord / 2 - c.leftCenterX) ^ 2 + (1 : ℝ) ^ 2 =
      c.radius ^ 2) ∧
      -c.chord / 2 ≤ -c.chord / 2 ∧ |(1 : ℝ)| ≤ 1
  rw [StripCore.leftCenterX]
  constructor
  · nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq c]
  · norm_num

theorem StripCore.lowerLeft_mem_leftArcTrace (c : StripCore) :
    (-c.chord / 2, -1) ∈ c.leftArcTrace := by
  change
    ((-c.chord / 2 - c.leftCenterX) ^ 2 + (-1 : ℝ) ^ 2 =
      c.radius ^ 2) ∧
      -c.chord / 2 ≤ -c.chord / 2 ∧ |(-1 : ℝ)| ≤ 1
  rw [StripCore.leftCenterX]
  constructor
  · nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq c]
  · norm_num

theorem StripCore.upperRight_mem_rightArcTrace (c : StripCore) :
    (c.chord / 2, 1) ∈ c.rightArcTrace := by
  change
    ((c.chord / 2 - c.rightCenterX) ^ 2 + (1 : ℝ) ^ 2 =
      c.radius ^ 2) ∧
      c.chord / 2 ≤ c.chord / 2 ∧ |(1 : ℝ)| ≤ 1
  rw [StripCore.rightCenterX]
  constructor
  · nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq c]
  · norm_num

theorem StripCore.lowerRight_mem_rightArcTrace (c : StripCore) :
    (c.chord / 2, -1) ∈ c.rightArcTrace := by
  change
    ((c.chord / 2 - c.rightCenterX) ^ 2 + (-1 : ℝ) ^ 2 =
      c.radius ^ 2) ∧
      c.chord / 2 ≤ c.chord / 2 ∧ |(-1 : ℝ)| ≤ 1
  rw [StripCore.rightCenterX]
  constructor
  · nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq c]
  · norm_num

/-- The constructor's left arc is exactly the source-facing closed left
circle branch in the strip. -/
theorem FourArcAssembly.leftArcTrace_eq_stripCircleTrace
    (a : FourArcAssembly) :
    StripCore.leftArcTrace a.core =
      stripCircleTrace .left (a.core.leftCenterX, 0) a.core.radius := by
  ext p
  constructor
  · intro hp
    refine ⟨?_, hp.2.2, ?_⟩
    · simpa [circleValue] using sub_eq_zero.mpr hp.1
    · change p.1 ≤ a.core.leftCenterX
      rw [StripCore.leftCenterX]
      have hcos : 0 ≤ cos a.core.sideAngle := by
        rw [a.core.cos_sideAngle]
        positivity
      nlinarith [mul_nonneg a.core.radius_pos.le hcos, hp.2.1]
  · rintro ⟨hcircle, hy, hx⟩
    have heq :
        (p.1 - a.core.leftCenterX) ^ 2 + p.2 ^ 2 =
          a.core.radius ^ 2 := by
      simpa [circleValue] using sub_eq_zero.mp hcircle
    have hysq : p.2 ^ 2 ≤ 1 := by
      have hb := abs_le.mp hy
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p.2)
        (by linarith : 0 ≤ 1 + p.2)]
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hbranch : p.1 ≤ -a.core.chord / 2 := by
      change p.1 ≤ a.core.leftCenterX at hx
      have hrc : 0 ≤ a.core.radius * cos a.core.sideAngle :=
        mul_nonneg a.core.radius_pos.le hcos
      have hd : p.1 - a.core.leftCenterX ≤ 0 := sub_nonpos.mpr hx
      have hsq :
          (a.core.radius * cos a.core.sideAngle) ^ 2 ≤
            (p.1 - a.core.leftCenterX) ^ 2 := by
        nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq a.core]
      have habs :
          |a.core.radius * cos a.core.sideAngle| ≤
            |p.1 - a.core.leftCenterX| := by
        apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
        simpa only [sq_abs] using hsq
      rw [abs_of_nonneg hrc, abs_of_nonpos hd] at habs
      unfold StripCore.leftCenterX at habs
      linarith
    exact ⟨heq, hbranch, hy⟩

/-- The constructor's right arc is exactly the source-facing closed right
circle branch in the strip. -/
theorem FourArcAssembly.rightArcTrace_eq_stripCircleTrace
    (a : FourArcAssembly) :
    StripCore.rightArcTrace a.core =
      stripCircleTrace .right (a.core.rightCenterX, 0) a.core.radius := by
  ext p
  constructor
  · intro hp
    refine ⟨?_, hp.2.2, ?_⟩
    · simpa [circleValue] using sub_eq_zero.mpr hp.1
    · change a.core.rightCenterX ≤ p.1
      rw [StripCore.rightCenterX]
      have hcos : 0 ≤ cos a.core.sideAngle := by
        rw [a.core.cos_sideAngle]
        positivity
      nlinarith [mul_nonneg a.core.radius_pos.le hcos, hp.2.1]
  · rintro ⟨hcircle, hy, hx⟩
    have heq :
        (p.1 - a.core.rightCenterX) ^ 2 + p.2 ^ 2 =
          a.core.radius ^ 2 := by
      simpa [circleValue] using sub_eq_zero.mp hcircle
    have hysq : p.2 ^ 2 ≤ 1 := by
      have hb := abs_le.mp hy
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p.2)
        (by linarith : 0 ≤ 1 + p.2)]
    have hcos : 0 ≤ cos a.core.sideAngle := by
      rw [a.core.cos_sideAngle]
      positivity
    have hbranch : a.core.chord / 2 ≤ p.1 := by
      change a.core.rightCenterX ≤ p.1 at hx
      have hrc : 0 ≤ a.core.radius * cos a.core.sideAngle :=
        mul_nonneg a.core.radius_pos.le hcos
      have hd : 0 ≤ p.1 - a.core.rightCenterX := sub_nonneg.mpr hx
      have hsq :
          (a.core.radius * cos a.core.sideAngle) ^ 2 ≤
            (p.1 - a.core.rightCenterX) ^ 2 := by
        nlinarith [CMVFigureFour.StripCore.radius_mul_cos_sq a.core]
      have habs :
          |a.core.radius * cos a.core.sideAngle| ≤
            |p.1 - a.core.rightCenterX| := by
        apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
        simpa only [sq_abs] using hsq
      rw [abs_of_nonneg hrc, abs_of_nonneg hd] at habs
      unfold StripCore.rightCenterX at habs
      linarith
    exact ⟨heq, hbranch, hy⟩

/-- The constructor's upper cap trace is exactly the source-facing exterior
upper circle trace. -/
theorem FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace
    (a : FourArcAssembly) :
    a.upperCap.arcTrace =
      exteriorCircleTrace .upper a.upperCap.center a.upperCap.radius := by
  ext p
  simp only [OneSidedCircularCap.arcTrace, exteriorCircleTrace, mem_ofPred_eq,
    circleValue, OneSidedCircularCap.radiusSquaredAt]
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨sub_eq_zero.mpr h, by
      simpa [FourArcAssembly.upperCap] using hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨sub_eq_zero.mp h, by
      simpa [FourArcAssembly.upperCap] using hy⟩

/-- The constructor's lower cap trace is exactly the source-facing exterior
lower circle trace. -/
theorem FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace
    (a : FourArcAssembly) :
    a.lowerCap.arcTrace =
      exteriorCircleTrace .lower a.lowerCap.center a.lowerCap.radius := by
  ext p
  simp only [OneSidedCircularCap.arcTrace, exteriorCircleTrace, mem_ofPred_eq,
    circleValue, OneSidedCircularCap.radiusSquaredAt]
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨sub_eq_zero.mpr h, by
      simpa [FourArcAssembly.lowerCap] using hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨sub_eq_zero.mp h, by
      simpa [FourArcAssembly.lowerCap] using hy⟩



/-- Either strict side of a positive-radius circle accumulates at every point
of the circle. -/
theorem circleSide_mem_closure
    (side : CircleSide) (center p : PlanePoint) (radius : ℝ)
    (hradius : 0 < radius) (hp : circleValue center radius p = 0) :
    p ∈ closure {q | side.sign * circleValue center radius q < 0} := by
  cases side with
  | inside =>
      let t : ℕ → ℝ := fun n => 1 - 1 / (n + 1 : ℝ)
      let q : ℕ → PlanePoint := fun n =>
        (center.1 + t n * (p.1 - center.1),
          center.2 + t n * (p.2 - center.2))
      have ht : Filter.Tendsto t Filter.atTop (nhds 1) := by
        dsimp [t]
        simpa using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Filter.Tendsto q Filter.atTop (nhds p) := by
        have hx := (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => center.1)
            Filter.atTop (nhds center.1)).add
          (ht.mul (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => p.1 - center.1)
              Filter.atTop (nhds (p.1 - center.1))))
        have hy := (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => center.2)
            Filter.atTop (nhds center.2)).add
          (ht.mul (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => p.2 - center.2)
              Filter.atTop (nhds (p.2 - center.2))))
        have h := hx.prodMk_nhds hy
        rw [show (center.1 + 1 * (p.1 - center.1),
            center.2 + 1 * (p.2 - center.2)) = p by
          apply Prod.ext <;> dsimp <;> ring] at h
        exact h
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hinvpos : 0 < (1 : ℝ) / (n + 1 : ℝ) :=
        div_pos zero_lt_one hn
      have hinvle : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 :=
        (div_le_one hn).2 (by norm_num)
      have ht0 : 0 ≤ t n := by dsimp [t]; linarith
      have ht1 : t n < 1 := by dsimp [t]; linarith
      change CircleSide.inside.sign *
        circleValue center radius (q n) < 0
      simp only [CircleSide.sign, one_mul]
      unfold circleValue q
      dsimp only
      have hp' := hp
      unfold circleValue at hp'
      have htsq : (t n) ^ 2 < 1 := by nlinarith
      nlinarith [sq_nonneg (p.1 - center.1),
        sq_nonneg (p.2 - center.2), sq_pos_of_pos hradius]
  | outside =>
      let t : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ)
      let q : ℕ → PlanePoint := fun n =>
        (center.1 + t n * (p.1 - center.1),
          center.2 + t n * (p.2 - center.2))
      have ht : Filter.Tendsto t Filter.atTop (nhds 1) := by
        dsimp [t]
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Filter.Tendsto q Filter.atTop (nhds p) := by
        have hx := (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => center.1)
            Filter.atTop (nhds center.1)).add
          (ht.mul (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => p.1 - center.1)
              Filter.atTop (nhds (p.1 - center.1))))
        have hy := (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => center.2)
            Filter.atTop (nhds center.2)).add
          (ht.mul (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ => p.2 - center.2)
              Filter.atTop (nhds (p.2 - center.2))))
        have h := hx.prodMk_nhds hy
        rw [show (center.1 + 1 * (p.1 - center.1),
            center.2 + 1 * (p.2 - center.2)) = p by
          apply Prod.ext <;> dsimp <;> ring] at h
        exact h
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hinvpos : 0 < (1 : ℝ) / (n + 1 : ℝ) :=
        div_pos zero_lt_one hn
      have ht1 : 1 < t n := by dsimp [t]; linarith
      change CircleSide.outside.sign *
        circleValue center radius (q n) < 0
      simp only [CircleSide.sign, neg_mul, one_mul]
      unfold circleValue q
      dsimp only
      have hp' := hp
      unfold circleValue at hp'
      have htsq : 1 < (t n) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (p.1 - center.1),
        sq_nonneg (p.2 - center.2), sq_pos_of_pos hradius]

/-- Local one-sidedness at a circle point supplies interior points arbitrarily
close to that point. -/
theorem mem_closure_of_locallyOneSided
    {a : FourArcAssembly} {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius) (hp : circleValue center radius p = 0)
    (hlocal : LocallyOneSided (interior a.carrier) center radius p) :
    p ∈ closure (interior a.carrier) := by
  rcases hlocal with ⟨side, V, hVopen, hpV, hlocal⟩
  have hside := circleSide_mem_closure side center p radius hradius hp
  rw [mem_closure_iff_frequently] at hside ⊢
  exact (hside.and_eventually (hVopen.mem_nhds hpV)).mono (by
    intro q hq
    have hmem :
        q ∈ V ∩ {z |
          side.sign * circleValue center radius z < 0} :=
      ⟨hq.2, hq.1⟩
    rw [← hlocal] at hmem
    exact hmem.1)

/-- Each of the four circle junctions is a limit of strict rectangle-interior
points. -/
theorem FourArcAssembly.endpoint_mem_closure_interior
    (a : FourArcAssembly) (horizontalSign verticalSign : ℝ)
    (hhorizontal : horizontalSign = 1 ∨ horizontalSign = -1)
    (hvertical : verticalSign = 1 ∨ verticalSign = -1) :
    (horizontalSign * (a.core.chord / 2), verticalSign) ∈
      closure (interior a.carrier) := by
  let t : ℕ → ℝ := fun n => 1 - 1 / (n + 1 : ℝ)
  let q : ℕ → PlanePoint := fun n =>
    (t n * (horizontalSign * (a.core.chord / 2)), t n * verticalSign)
  have ht : Filter.Tendsto t Filter.atTop (nhds 1) := by
    dsimp [t]
    simpa using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hq : Filter.Tendsto q Filter.atTop
      (nhds (horizontalSign * (a.core.chord / 2), verticalSign)) := by
    have hx := ht.mul (tendsto_const_nhds :
      Filter.Tendsto
        (fun _ : ℕ => horizontalSign * (a.core.chord / 2))
        Filter.atTop (nhds (horizontalSign * (a.core.chord / 2))))
    have hy := ht.mul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => verticalSign)
        Filter.atTop (nhds verticalSign))
    simpa only [q, one_mul] using hx.prodMk_nhds hy
  apply mem_closure_of_tendsto hq
  filter_upwards [] with n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hinvpos : 0 < (1 : ℝ) / (n + 1 : ℝ) :=
    div_pos zero_lt_one hn
  have hinvle : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 :=
    (div_le_one hn).2 (by norm_num)
  have ht0 : 0 ≤ t n := by dsimp [t]; linarith
  have ht1 : t n < 1 := by dsimp [t]; linarith
  let W : Set PlanePoint :=
    {z | -a.core.chord / 2 < z.1 ∧
      z.1 < a.core.chord / 2 ∧ |z.2| < 1}
  apply interior_maximal (t := W)
  · intro z hz
    exact Or.inl (Or.inl (Or.inl (Or.inl
      ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩)))
  · exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const))
  · change -a.core.chord / 2 <
        t n * (horizontalSign * (a.core.chord / 2)) ∧
      t n * (horizontalSign * (a.core.chord / 2)) <
        a.core.chord / 2 ∧
      |t n * verticalSign| < 1
    have hhalf : 0 < a.core.chord / 2 :=
      div_pos a.core.chord_pos (by norm_num)
    have hmulnonneg : 0 ≤ t n * (a.core.chord / 2) :=
      mul_nonneg ht0 hhalf.le
    have hmullt : t n * (a.core.chord / 2) < a.core.chord / 2 :=
      (mul_lt_iff_lt_one_left hhalf).2 ht1
    rcases hhorizontal with rfl | rfl <;>
      rcases hvertical with rfl | rfl <;>
      simp only [one_mul, neg_one_mul, mul_one, mul_neg, abs_neg,
        abs_of_nonneg ht0]
    all_goals
      exact ⟨by linarith, by exact ⟨by linarith, by linarith⟩⟩

/-- A four-arc carrier is the closure of its actual open interior, including
all four nonsmooth junctions. -/
theorem FourArcAssembly.closure_interior_carrier (a : FourArcAssembly) :
    closure (interior a.carrier) = a.carrier := by
  apply Subset.antisymm
  · exact closure_minimal interior_subset a.isClosed_carrier
  · intro p hp
    by_cases hpint : p ∈ interior a.carrier
    · exact subset_closure hpint
    · have hpfront : p ∈ frontier a.carrier :=
        (mem_frontier_iff_notMem_interior hp).2 hpint
      rw [a.frontier_carrier] at hpfront
      rcases hpfront with hleft | hright | hupper | hlower
      · by_cases htop : p = (-a.core.chord / 2, 1)
        · subst p
          convert
            CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
              a (-1) 1 (Or.inr rfl) (Or.inl rfl) using 1 <;> ring
        · by_cases hbottom : p = (-a.core.chord / 2, -1)
          · subst p
            convert
              CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
                a (-1) (-1) (Or.inr rfl) (Or.inr rfl) using 1 <;> ring
          · exact mem_closure_of_locallyOneSided a.core.radius_pos
              (by simpa [circleValue] using sub_eq_zero.mpr hleft.1)
              (CMVFigureFour.FourArcAssembly.left_locallyOneSided
                a hleft htop hbottom)
      · by_cases htop : p = (a.core.chord / 2, 1)
        · subst p
          simpa using
            CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
              a 1 1 (Or.inl rfl) (Or.inl rfl)
        · by_cases hbottom : p = (a.core.chord / 2, -1)
          · subst p
            simpa using
              CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
                a 1 (-1) (Or.inl rfl) (Or.inr rfl)
          · exact mem_closure_of_locallyOneSided a.core.radius_pos
              (by simpa [circleValue] using sub_eq_zero.mpr hright.1)
              (CMVFigureFour.FourArcAssembly.right_locallyOneSided
                a hright htop hbottom)
      · by_cases hleftEnd : p = (-a.core.chord / 2, 1)
        · subst p
          convert
            CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
              a (-1) 1 (Or.inr rfl) (Or.inl rfl) using 1 <;> ring
        · by_cases hrightEnd : p = (a.core.chord / 2, 1)
          · subst p
            simpa using
              CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
                a 1 1 (Or.inl rfl) (Or.inl rfl)
          · exact mem_closure_of_locallyOneSided a.upperCap.radius_pos
              (by
                simpa [circleValue,
                  OneSidedCircularCap.radiusSquaredAt] using
                    sub_eq_zero.mpr hupper.1)
              (CMVFigureFour.FourArcAssembly.upper_locallyOneSided
                a hupper (by
                  intro heq
                  apply hleftEnd
                  rw [heq]
                  simp [FourArcAssembly.upperCap,
                    OneSidedCircularCap.leftEndpoint]
                  ring)
                  (by
                    simpa [FourArcAssembly.upperCap,
                      OneSidedCircularCap.rightEndpoint] using hrightEnd))
      · by_cases hleftEnd : p = (-a.core.chord / 2, -1)
        · subst p
          convert
            CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
              a (-1) (-1) (Or.inr rfl) (Or.inr rfl) using 1 <;> ring
        · by_cases hrightEnd : p = (a.core.chord / 2, -1)
          · subst p
            simpa using
              CMVFigureFour.FourArcAssembly.endpoint_mem_closure_interior
                a 1 (-1) (Or.inl rfl) (Or.inr rfl)
          · exact mem_closure_of_locallyOneSided a.lowerCap.radius_pos
              (by
                simpa [circleValue,
                  OneSidedCircularCap.radiusSquaredAt] using
                    sub_eq_zero.mpr hlower.1)
              (CMVFigureFour.FourArcAssembly.lower_locallyOneSided
                a hlower (by
                  intro heq
                  apply hleftEnd
                  rw [heq]
                  simp [FourArcAssembly.lowerCap,
                    OneSidedCircularCap.leftEndpoint]
                  ring)
                  (by
                    simpa [FourArcAssembly.lowerCap,
                      OneSidedCircularCap.rightEndpoint] using hrightEnd))

/-- The actual bounded open representative has exactly the same four-arc
frontier as the literal closed carrier. -/
theorem FourArcAssembly.frontier_interior_carrier (a : FourArcAssembly) :
    frontier (interior a.carrier) = a.boundaryTrace := by
  rw [isOpen_interior.frontier_eq,
    CMVFigureFour.FourArcAssembly.closure_interior_carrier,
    ← a.isClosed_carrier.frontier_eq, a.frontier_carrier]

/-- Horizontal placement is an isometry of the coordinate plane. -/
theorem isometry_horizontalTranslation (t : ℝ) :
    Isometry (horizontalTranslation t) := by
  intro p q
  simp [Prod.edist_eq, horizontalTranslation_apply]

/-- Horizontal placement transports either selected strip-circle branch
exactly. -/
theorem horizontalTranslation_image_stripCircleTrace
    (t : ℝ) (branch : HorizontalCircleBranch)
    (center : PlanePoint) (radius : ℝ) :
    horizontalTranslation t ''
        stripCircleTrace branch center radius =
      stripCircleTrace branch (horizontalTranslation t center) radius := by
  ext q
  rcases (horizontalTranslation t).surjective q with ⟨p, rfl⟩
  constructor
  · rintro ⟨z, hz, hzp⟩
    have hzEq : z = p := (horizontalTranslation t).injective hzp
    subst z
    rcases hz with ⟨hcircle, hheight, hbranch⟩
    refine ⟨circleValue_horizontalTranslation t center radius p ▸ hcircle,
      ?_, ?_⟩
    · simpa only [horizontalTranslation_apply] using hheight
    · cases branch <;>
        simp only [HorizontalCircleBranch.Holds,
          horizontalTranslation_apply] at hbranch ⊢ <;> linarith
  · intro hp
    refine ⟨p, ?_, rfl⟩
    rcases hp with ⟨hcircle, hheight, hbranch⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [circleValue_horizontalTranslation] using hcircle
    · simpa only [horizontalTranslation_apply] using hheight
    · cases branch <;>
        simp only [HorizontalCircleBranch.Holds,
          horizontalTranslation_apply] at hbranch ⊢ <;> linarith

/-- Horizontal placement transports either selected exterior-circle trace
exactly. -/
theorem horizontalTranslation_image_exteriorCircleTrace
    (t : ℝ) (side : CapSide) (center : PlanePoint) (radius : ℝ) :
    horizontalTranslation t ''
        exteriorCircleTrace side center radius =
      exteriorCircleTrace side (horizontalTranslation t center) radius := by
  ext q
  rcases (horizontalTranslation t).surjective q with ⟨p, rfl⟩
  constructor
  · rintro ⟨z, hz, hzp⟩
    have hzEq : z = p := (horizontalTranslation t).injective hzp
    subst z
    rcases hz with ⟨hcircle, hside⟩
    refine ⟨circleValue_horizontalTranslation t center radius p ▸ hcircle, ?_⟩
    cases side <;> simpa only [horizontalTranslation_apply] using hside
  · intro hp
    refine ⟨p, ?_, rfl⟩
    rcases hp with ⟨hcircle, hside⟩
    refine ⟨?_, ?_⟩
    · simpa only [circleValue_horizontalTranslation] using hcircle
    · cases side <;> simpa only [horizontalTranslation_apply] using hside

/-- Local one-sided circle data is invariant under horizontal placement. -/
theorem locallyOneSided_horizontalTranslation
    {U : Set PlanePoint} {center p : PlanePoint} {radius t : ℝ}
    (h : LocallyOneSided U center radius p) :
    LocallyOneSided (horizontalTranslation t '' U)
      (horizontalTranslation t center) radius
      (horizontalTranslation t p) := by
  rcases h with ⟨side, V, hVopen, hpV, hUV⟩
  let sideSet : Set PlanePoint :=
    {q | side.sign * circleValue center radius q < 0}
  let translatedSideSet : Set PlanePoint :=
    {q | side.sign *
      circleValue (horizontalTranslation t center) radius q < 0}
  have hsideImage :
      horizontalTranslation t '' sideSet = translatedSideSet := by
    ext q
    rcases (horizontalTranslation t).surjective q with ⟨z, rfl⟩
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwEq : w = z := (horizontalTranslation t).injective hwz
      subst w
      simpa only [sideSet, translatedSideSet, mem_ofPred_eq,
        circleValue_horizontalTranslation] using hw
    · intro hz
      refine ⟨z, ?_, rfl⟩
      simpa only [sideSet, translatedSideSet, mem_ofPred_eq,
        circleValue_horizontalTranslation] using hz
  refine ⟨side, horizontalTranslation t '' V,
    (horizontalTranslation t).isOpenMap V hVopen, ⟨p, hpV, rfl⟩, ?_⟩
  calc
    (horizontalTranslation t '' U) ∩
        (horizontalTranslation t '' V) =
      horizontalTranslation t '' (U ∩ V) :=
        (Set.image_inter (horizontalTranslation t).injective).symm
    _ = horizontalTranslation t '' (V ∩ sideSet) := by
      rw [hUV]
    _ = (horizontalTranslation t '' V) ∩
        (horizontalTranslation t '' sideSet) :=
      Set.image_inter (horizontalTranslation t).injective
    _ = (horizontalTranslation t '' V) ∩ translatedSideSet := by
      rw [hsideImage]

namespace CircleRigidity

/-- Two distinct points of equal height on one circle have the circle center as
the midpoint of their abscissae.  This uses only squared circle incidence. -/
theorem chord_abscissae_add_eq_two_mul_center
    {center p q : PlanePoint} {radius : ℝ}
    (hp : circleValue center radius p = 0)
    (hq : circleValue center radius q = 0)
    (hheight : p.2 = q.2)
    (hdistinct : p.1 ≠ q.1) :
    p.1 + q.1 = 2 * center.1 := by
  have hvertical :
      (p.2 - center.2) ^ 2 = (q.2 - center.2) ^ 2 := by
    rw [hheight]
  have hsquares :
      (p.1 - center.1) ^ 2 = (q.1 - center.1) ^ 2 := by
    unfold circleValue at hp hq
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with heq | heq
  · exfalso
    apply hdistinct
    linarith
  · linarith

/-- Equal-radius circles with equal center heights give equal horizontal radial
lengths at equal-height points when the points lie on opposite horizontal
branches.  Neither offset is required to be positive. -/
theorem opposite_horizontal_offsets_eq
    {leftCenter rightCenter leftPoint rightPoint : PlanePoint} {radius : ℝ}
    (hcenterHeight : leftCenter.2 = rightCenter.2)
    (hpointHeight : leftPoint.2 = rightPoint.2)
    (hleftCircle : circleValue leftCenter radius leftPoint = 0)
    (hrightCircle : circleValue rightCenter radius rightPoint = 0)
    (hleftBranch : leftPoint.1 ≤ leftCenter.1)
    (hrightBranch : rightCenter.1 ≤ rightPoint.1) :
    leftCenter.1 - leftPoint.1 = rightPoint.1 - rightCenter.1 := by
  have hvertical :
      (leftPoint.2 - leftCenter.2) ^ 2 =
        (rightPoint.2 - rightCenter.2) ^ 2 := by
    rw [hcenterHeight, hpointHeight]
  have hsquares :
      (leftCenter.1 - leftPoint.1) ^ 2 =
        (rightPoint.1 - rightCenter.1) ^ 2 := by
    unfold circleValue at hleftCircle hrightCircle
    nlinarith
  nlinarith

end CircleRigidity

/-- Figure-4 source incidence before any global vertical-reflection data is
available.  The carrier, representative, complete frontier, and local
one-sidedness fields are the unchanged actual-source inputs of
`SourceGeometry`.  Common radius and three independent signed Snell laws remain
explicit upstream hypotheses; the fourth law is derived below.

There is deliberately no symmetry axis, center alignment, reflected point,
normalized width, or target carrier in this structure. -/
structure BilateralSourceIncidence (lam : ℝ) where
  sourceCarrier : Set PlanePoint
  representative : Set PlanePoint
  sourceRepresentative : SourceRepresentative sourceCarrier representative
  sourceRadius : ℝ
  upperCenter : PlanePoint
  lowerCenter : PlanePoint
  leftStripCenter : PlanePoint
  rightStripCenter : PlanePoint
  upperLeft : PlanePoint
  lowerLeft : PlanePoint
  upperRight : PlanePoint
  lowerRight : PlanePoint
  density_jump : 1 < lam
  sourceRadius_pos : 0 < sourceRadius
  upperLeft_height : upperLeft.2 = 1
  upperRight_height : upperRight.2 = 1
  lowerLeft_height : lowerLeft.2 = -1
  lowerRight_height : lowerRight.2 = -1
  upper_endpoints_order : upperLeft.1 < upperRight.1
  lower_endpoints_order : lowerLeft.1 < lowerRight.1
  upperLeft_mem_upper :
    upperLeft ∈ exteriorCircleTrace .upper upperCenter sourceRadius
  upperRight_mem_upper :
    upperRight ∈ exteriorCircleTrace .upper upperCenter sourceRadius
  lowerLeft_mem_lower :
    lowerLeft ∈ exteriorCircleTrace .lower lowerCenter sourceRadius
  lowerRight_mem_lower :
    lowerRight ∈ exteriorCircleTrace .lower lowerCenter sourceRadius
  upperLeft_mem_left :
    upperLeft ∈ stripCircleTrace .left leftStripCenter sourceRadius
  lowerLeft_mem_left :
    lowerLeft ∈ stripCircleTrace .left leftStripCenter sourceRadius
  upperRight_mem_right :
    upperRight ∈ stripCircleTrace .right rightStripCenter sourceRadius
  lowerRight_mem_right :
    lowerRight ∈ stripCircleTrace .right rightStripCenter sourceRadius
  upper_left_signed_snell :
    (1 - leftStripCenter.2) / sourceRadius =
      lam * ((1 - upperCenter.2) / sourceRadius)
  lower_left_signed_snell :
    (1 + leftStripCenter.2) / sourceRadius =
      lam * ((1 + lowerCenter.2) / sourceRadius)
  upper_right_signed_snell :
    (1 - rightStripCenter.2) / sourceRadius =
      lam * ((1 - upperCenter.2) / sourceRadius)
  frontier_eq_four_circles :
    frontier representative =
      exteriorCircleTrace .upper upperCenter sourceRadius ∪
        exteriorCircleTrace .lower lowerCenter sourceRadius ∪
          stripCircleTrace .left leftStripCenter sourceRadius ∪
            stripCircleTrace .right rightStripCenter sourceRadius
  upper_one_sided : ∀ p,
    p ∈ exteriorCircleTrace .upper upperCenter sourceRadius →
    p ≠ upperLeft → p ≠ upperRight →
      LocallyOneSided representative upperCenter sourceRadius p
  lower_one_sided : ∀ p,
    p ∈ exteriorCircleTrace .lower lowerCenter sourceRadius →
    p ≠ lowerLeft → p ≠ lowerRight →
      LocallyOneSided representative lowerCenter sourceRadius p
  left_one_sided : ∀ p,
    p ∈ stripCircleTrace .left leftStripCenter sourceRadius →
    p ≠ upperLeft → p ≠ lowerLeft →
      LocallyOneSided representative leftStripCenter sourceRadius p
  right_one_sided : ∀ p,
    p ∈ stripCircleTrace .right rightStripCenter sourceRadius →
    p ≠ upperRight → p ≠ lowerRight →
      LocallyOneSided representative rightStripCenter sourceRadius p


namespace BilateralSourceIncidence

private theorem fourArcCandidate_upper_signed_snell
    {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    1 / candidate.assembly.core.radius =
      lam * ((1 - candidate.assembly.upperCap.center.2) /
        candidate.assembly.core.radius) := by
  have hcommon :
      candidate.assembly.upperCap.radius =
        candidate.assembly.core.radius := by
    simpa using candidate.four_arcs_common_radius.1
  have hcenter :
      candidate.assembly.upperCap.center.2 =
        1 - candidate.assembly.upperCap.radius *
          cos candidate.alpha := rfl
  have hrh :
      candidate.assembly.core.radius * candidate.h = 1 := by
    simp [FourArcCandidate.assembly, FourArcCandidate.stripCore,
      StripCore.radius]
    field_simp [ne_of_gt candidate.h_pos]
  calc
    1 / candidate.assembly.core.radius = candidate.h := by
      apply (div_eq_iff (ne_of_gt candidate.assembly.core.radius_pos)).2
      nlinarith
    _ = lam * cos candidate.alpha := hcandidate.snell_incidence.symm
    _ = lam * ((1 - candidate.assembly.upperCap.center.2) /
        candidate.assembly.core.radius) := by
      rw [hcenter, hcommon]
      have hcancel :
          candidate.assembly.core.radius * cos candidate.alpha /
              candidate.assembly.core.radius =
            cos candidate.alpha :=
        mul_div_cancel_left₀ _ (ne_of_gt candidate.assembly.core.radius_pos)
      have hnumerator :
          1 - (1 - candidate.assembly.core.radius * cos candidate.alpha) =
            candidate.assembly.core.radius * cos candidate.alpha := by ring
      rw [hnumerator, hcancel]

private theorem fourArcCandidate_lower_signed_snell
    {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    1 / candidate.assembly.core.radius =
      lam * ((1 + candidate.assembly.lowerCap.center.2) /
        candidate.assembly.core.radius) := by
  have hcommon :
      candidate.assembly.lowerCap.radius =
        candidate.assembly.core.radius := by
    simpa using candidate.four_arcs_common_radius.2
  have hcenter :
      candidate.assembly.lowerCap.center.2 =
        -1 + candidate.assembly.lowerCap.radius *
          cos candidate.alpha := rfl
  have hrh :
      candidate.assembly.core.radius * candidate.h = 1 := by
    simp [FourArcCandidate.assembly, FourArcCandidate.stripCore,
      StripCore.radius]
    field_simp [ne_of_gt candidate.h_pos]
  calc
    1 / candidate.assembly.core.radius = candidate.h := by
      apply (div_eq_iff (ne_of_gt candidate.assembly.core.radius_pos)).2
      nlinarith
    _ = lam * cos candidate.alpha := hcandidate.snell_incidence.symm
    _ = lam * ((1 + candidate.assembly.lowerCap.center.2) /
        candidate.assembly.core.radius) := by
      rw [hcenter, hcommon]
      have hcancel :
          candidate.assembly.core.radius * cos candidate.alpha /
              candidate.assembly.core.radius =
            cos candidate.alpha :=
        mul_div_cancel_left₀ _ (ne_of_gt candidate.assembly.core.radius_pos)
      have hnumerator :
          1 + (-1 + candidate.assembly.core.radius * cos candidate.alpha) =
            candidate.assembly.core.radius * cos candidate.alpha := by ring
      rw [hnumerator, hcancel]

/-- Every closed-Snell four-arc candidate is an actual bilateral source:
the source carrier is literal, while its representative is the bounded open
interior with the same complete four-arc frontier. -/
def ofFourArcCandidate {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    BilateralSourceIncidence lam where
  sourceCarrier := candidate.assembly.carrier
  representative := interior candidate.assembly.carrier
  sourceRepresentative := fourArcSourceRepresentative candidate.assembly
  sourceRadius := candidate.assembly.core.radius
  upperCenter := candidate.assembly.upperCap.center
  lowerCenter := candidate.assembly.lowerCap.center
  leftStripCenter := (candidate.assembly.core.leftCenterX, 0)
  rightStripCenter := (candidate.assembly.core.rightCenterX, 0)
  upperLeft := (-candidate.assembly.core.chord / 2, 1)
  lowerLeft := (-candidate.assembly.core.chord / 2, -1)
  upperRight := (candidate.assembly.core.chord / 2, 1)
  lowerRight := (candidate.assembly.core.chord / 2, -1)
  density_jump := hcandidate.density_jump
  sourceRadius_pos := candidate.assembly.core.radius_pos
  upperLeft_height := rfl
  upperRight_height := rfl
  lowerLeft_height := rfl
  lowerRight_height := rfl
  upper_endpoints_order := by
    nlinarith [candidate.assembly.core.chord_pos]
  lower_endpoints_order := by
    nlinarith [candidate.assembly.core.chord_pos]
  upperLeft_mem_upper := by
    have hcommon :
        candidate.assembly.upperCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.1
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace]
    convert
      CMVFigureFour.OneSidedCircularCap.leftEndpoint_mem_arcTrace
        candidate.assembly.upperCap using 1 <;>
      simp [FourArcAssembly.upperCap,
        OneSidedCircularCap.leftEndpoint] <;> ring
  upperRight_mem_upper := by
    have hcommon :
        candidate.assembly.upperCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.1
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace]
    simpa [FourArcAssembly.upperCap,
      OneSidedCircularCap.rightEndpoint] using
        CMVFigureFour.OneSidedCircularCap.rightEndpoint_mem_arcTrace
          candidate.assembly.upperCap
  lowerLeft_mem_lower := by
    have hcommon :
        candidate.assembly.lowerCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.2
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace]
    convert
      CMVFigureFour.OneSidedCircularCap.leftEndpoint_mem_arcTrace
        candidate.assembly.lowerCap using 1 <;>
      simp [FourArcAssembly.lowerCap,
        OneSidedCircularCap.leftEndpoint] <;> ring
  lowerRight_mem_lower := by
    have hcommon :
        candidate.assembly.lowerCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.2
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace]
    simpa [FourArcAssembly.lowerCap,
      OneSidedCircularCap.rightEndpoint] using
        CMVFigureFour.OneSidedCircularCap.rightEndpoint_mem_arcTrace
          candidate.assembly.lowerCap
  upperLeft_mem_left := by
    rw [← CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace]
    exact CMVFigureFour.StripCore.upperLeft_mem_leftArcTrace
      candidate.assembly.core
  lowerLeft_mem_left := by
    rw [← CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace]
    exact CMVFigureFour.StripCore.lowerLeft_mem_leftArcTrace
      candidate.assembly.core
  upperRight_mem_right := by
    rw [← CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace]
    exact CMVFigureFour.StripCore.upperRight_mem_rightArcTrace
      candidate.assembly.core
  lowerRight_mem_right := by
    rw [← CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace]
    exact CMVFigureFour.StripCore.lowerRight_mem_rightArcTrace
      candidate.assembly.core
  upper_left_signed_snell := by
    simpa only [sub_zero] using
      fourArcCandidate_upper_signed_snell candidate hcandidate
  lower_left_signed_snell := by
    simpa only [add_zero] using
      fourArcCandidate_lower_signed_snell candidate hcandidate
  upper_right_signed_snell := by
    simpa only [sub_zero] using
      fourArcCandidate_upper_signed_snell candidate hcandidate
  frontier_eq_four_circles := by
    rw [CMVFigureFour.FourArcAssembly.frontier_interior_carrier,
      FourArcAssembly.boundaryTrace,
      CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace,
      CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace,
      CMVFigureFour.FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace,
      CMVFigureFour.FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace,
      candidate.four_arcs_common_radius.1,
      candidate.four_arcs_common_radius.2]
    ac_rfl
  upper_one_sided := by
    intro p hp hleft hright
    have hcommon :
        candidate.assembly.upperCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.1
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace]
      at hp
    rw [← hcommon]
    exact CMVFigureFour.FourArcAssembly.upper_locallyOneSided
      candidate.assembly hp
        (by
          intro heq
          apply hleft
          rw [heq]
          simp [FourArcAssembly.upperCap,
            OneSidedCircularCap.leftEndpoint]
          ring)
        (by
          simpa [FourArcAssembly.upperCap,
            OneSidedCircularCap.rightEndpoint] using hright)
  lower_one_sided := by
    intro p hp hleft hright
    have hcommon :
        candidate.assembly.lowerCap.radius =
          candidate.assembly.core.radius := by
      simpa using candidate.four_arcs_common_radius.2
    rw [← hcommon,
      ← CMVFigureFour.FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace]
      at hp
    rw [← hcommon]
    exact CMVFigureFour.FourArcAssembly.lower_locallyOneSided
      candidate.assembly hp
        (by
          intro heq
          apply hleft
          rw [heq]
          simp [FourArcAssembly.lowerCap,
            OneSidedCircularCap.leftEndpoint]
          ring)
        (by
          simpa [FourArcAssembly.lowerCap,
            OneSidedCircularCap.rightEndpoint] using hright)
  left_one_sided := by
    intro p hp hupper hlower
    rw [← CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace]
      at hp
    exact CMVFigureFour.FourArcAssembly.left_locallyOneSided
      candidate.assembly hp hupper hlower
  right_one_sided := by
    intro p hp hupper hlower
    rw [← CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace]
      at hp
    exact CMVFigureFour.FourArcAssembly.right_locallyOneSided
      candidate.assembly hp hupper hlower

variable {lam : ℝ} (g : BilateralSourceIncidence lam)
/-- Translate a bilateral specimen while keeping its representative open.
For this transport constructor the translated open representative itself is
used as the source carrier, so almost-everywhere agreement is definitional. -/
def horizontalTranslate (t : ℝ) : BilateralSourceIncidence lam where
  sourceCarrier := horizontalTranslation t '' g.representative
  representative := horizontalTranslation t '' g.representative
  sourceRepresentative := {
    representative_open :=
      (horizontalTranslation t).isOpenMap g.representative
        g.sourceRepresentative.representative_open
    representative_bounded :=
      (isometry_horizontalTranslation t).lipschitz.isBounded_image
        g.sourceRepresentative.representative_bounded
    source_ae_representative :=
      Filter.Eventually.of_forall (fun _ => rfl) }
  sourceRadius := g.sourceRadius
  upperCenter := horizontalTranslation t g.upperCenter
  lowerCenter := horizontalTranslation t g.lowerCenter
  leftStripCenter := horizontalTranslation t g.leftStripCenter
  rightStripCenter := horizontalTranslation t g.rightStripCenter
  upperLeft := horizontalTranslation t g.upperLeft
  lowerLeft := horizontalTranslation t g.lowerLeft
  upperRight := horizontalTranslation t g.upperRight
  lowerRight := horizontalTranslation t g.lowerRight
  density_jump := g.density_jump
  sourceRadius_pos := g.sourceRadius_pos
  upperLeft_height := by
    simpa only [horizontalTranslation_apply] using g.upperLeft_height
  upperRight_height := by
    simpa only [horizontalTranslation_apply] using g.upperRight_height
  lowerLeft_height := by
    simpa only [horizontalTranslation_apply] using g.lowerLeft_height
  lowerRight_height := by
    simpa only [horizontalTranslation_apply] using g.lowerRight_height
  upper_endpoints_order := by
    simp only [horizontalTranslation_apply]
    linarith [g.upper_endpoints_order]
  lower_endpoints_order := by
    simp only [horizontalTranslation_apply]
    linarith [g.lower_endpoints_order]
  upperLeft_mem_upper := by
    rw [← horizontalTranslation_image_exteriorCircleTrace]
    exact ⟨g.upperLeft, g.upperLeft_mem_upper, rfl⟩
  upperRight_mem_upper := by
    rw [← horizontalTranslation_image_exteriorCircleTrace]
    exact ⟨g.upperRight, g.upperRight_mem_upper, rfl⟩
  lowerLeft_mem_lower := by
    rw [← horizontalTranslation_image_exteriorCircleTrace]
    exact ⟨g.lowerLeft, g.lowerLeft_mem_lower, rfl⟩
  lowerRight_mem_lower := by
    rw [← horizontalTranslation_image_exteriorCircleTrace]
    exact ⟨g.lowerRight, g.lowerRight_mem_lower, rfl⟩
  upperLeft_mem_left := by
    rw [← horizontalTranslation_image_stripCircleTrace]
    exact ⟨g.upperLeft, g.upperLeft_mem_left, rfl⟩
  lowerLeft_mem_left := by
    rw [← horizontalTranslation_image_stripCircleTrace]
    exact ⟨g.lowerLeft, g.lowerLeft_mem_left, rfl⟩
  upperRight_mem_right := by
    rw [← horizontalTranslation_image_stripCircleTrace]
    exact ⟨g.upperRight, g.upperRight_mem_right, rfl⟩
  lowerRight_mem_right := by
    rw [← horizontalTranslation_image_stripCircleTrace]
    exact ⟨g.lowerRight, g.lowerRight_mem_right, rfl⟩
  upper_left_signed_snell := by
    simpa only [horizontalTranslation_apply] using g.upper_left_signed_snell
  lower_left_signed_snell := by
    simpa only [horizontalTranslation_apply] using g.lower_left_signed_snell
  upper_right_signed_snell := by
    simpa only [horizontalTranslation_apply] using g.upper_right_signed_snell
  frontier_eq_four_circles := by
    calc
      frontier (horizontalTranslation t '' g.representative) =
          horizontalTranslation t '' frontier g.representative :=
        ((horizontalTranslation t).image_frontier
          g.representative).symm
      _ = horizontalTranslation t ''
          (exteriorCircleTrace .upper g.upperCenter g.sourceRadius ∪
            exteriorCircleTrace .lower g.lowerCenter g.sourceRadius ∪
              stripCircleTrace .left g.leftStripCenter g.sourceRadius ∪
                stripCircleTrace .right g.rightStripCenter g.sourceRadius) := by
        rw [g.frontier_eq_four_circles]
      _ = exteriorCircleTrace .upper
            (horizontalTranslation t g.upperCenter) g.sourceRadius ∪
          exteriorCircleTrace .lower
            (horizontalTranslation t g.lowerCenter) g.sourceRadius ∪
            stripCircleTrace .left
              (horizontalTranslation t g.leftStripCenter) g.sourceRadius ∪
              stripCircleTrace .right
                (horizontalTranslation t g.rightStripCenter) g.sourceRadius := by
        rw [image_union, image_union, image_union,
          horizontalTranslation_image_exteriorCircleTrace,
          horizontalTranslation_image_exteriorCircleTrace,
          horizontalTranslation_image_stripCircleTrace,
          horizontalTranslation_image_stripCircleTrace]
  upper_one_sided := by
    intro p hp hpLeft hpRight
    rw [← horizontalTranslation_image_exteriorCircleTrace] at hp
    rcases hp with ⟨q, hq, rfl⟩
    apply locallyOneSided_horizontalTranslation
    apply g.upper_one_sided q hq
    · intro hqLeft
      exact hpLeft (congrArg (horizontalTranslation t) hqLeft)
    · intro hqRight
      exact hpRight (congrArg (horizontalTranslation t) hqRight)
  lower_one_sided := by
    intro p hp hpLeft hpRight
    rw [← horizontalTranslation_image_exteriorCircleTrace] at hp
    rcases hp with ⟨q, hq, rfl⟩
    apply locallyOneSided_horizontalTranslation
    apply g.lower_one_sided q hq
    · intro hqLeft
      exact hpLeft (congrArg (horizontalTranslation t) hqLeft)
    · intro hqRight
      exact hpRight (congrArg (horizontalTranslation t) hqRight)
  left_one_sided := by
    intro p hp hpUpper hpLower
    rw [← horizontalTranslation_image_stripCircleTrace] at hp
    rcases hp with ⟨q, hq, rfl⟩
    apply locallyOneSided_horizontalTranslation
    apply g.left_one_sided q hq
    · intro hqUpper
      exact hpUpper (congrArg (horizontalTranslation t) hqUpper)
    · intro hqLower
      exact hpLower (congrArg (horizontalTranslation t) hqLower)
  right_one_sided := by
    intro p hp hpUpper hpLower
    rw [← horizontalTranslation_image_stripCircleTrace] at hp
    rcases hp with ⟨q, hq, rfl⟩
    apply locallyOneSided_horizontalTranslation
    apply g.right_one_sided q hq
    · intro hqUpper
      exact hpUpper (congrArg (horizontalTranslation t) hqUpper)
    · intro hqLower
      exact hpLower (congrArg (horizontalTranslation t) hqLower)


/-- The upper-left and upper-right Snell laws already force the same
strip-center height.  The proof only cancels the supplied positive common
radius; it does not use either lower law, a reflection, or an axis. -/
theorem stripCenter_heights_eq :
    g.leftStripCenter.2 = g.rightStripCenter.2 := by
  have hupper :
      (1 - g.leftStripCenter.2) / g.sourceRadius =
        (1 - g.rightStripCenter.2) / g.sourceRadius :=
    g.upper_left_signed_snell.trans g.upper_right_signed_snell.symm
  field_simp [ne_of_gt g.sourceRadius_pos] at hupper
  linarith

/-- The lower-right Snell equation is a consequence, not a fourth primitive
contact-law input: transport the lower-left law across the already forced
strip-center height. -/
theorem lower_right_signed_snell :
    (1 + g.rightStripCenter.2) / g.sourceRadius =
      lam * ((1 + g.lowerCenter.2) / g.sourceRadius) := by
  rw [← g.stripCenter_heights_eq]
  exact g.lower_left_signed_snell

/-- The source vertical axis forced by the two strip-circle centers. -/
def symmetryAxisX : ℝ :=
  (g.leftStripCenter.1 + g.rightStripCenter.1) / 2

@[simp] theorem horizontalTranslate_symmetryAxisX (t : ℝ) :
    (g.horizontalTranslate t).symmetryAxisX = g.symmetryAxisX + t := by
  simp [symmetryAxisX, horizontalTranslate, horizontalTranslation_apply]
  ring

/-- Opposite strip-circle branches have equal upper horizontal offsets.  Zero
offsets remain allowed at this intermediate step. -/
theorem upper_horizontal_offsets_eq :
    g.leftStripCenter.1 - g.upperLeft.1 =
      g.upperRight.1 - g.rightStripCenter.1 := by
  apply CircleRigidity.opposite_horizontal_offsets_eq
    g.stripCenter_heights_eq
  · rw [g.upperLeft_height, g.upperRight_height]
  · exact g.upperLeft_mem_left.1
  · exact g.upperRight_mem_right.1
  · exact g.upperLeft_mem_left.2.2
  · exact g.upperRight_mem_right.2.2

/-- Opposite strip-circle branches have equal lower horizontal offsets. -/
theorem lower_horizontal_offsets_eq :
    g.leftStripCenter.1 - g.lowerLeft.1 =
      g.lowerRight.1 - g.rightStripCenter.1 := by
  apply CircleRigidity.opposite_horizontal_offsets_eq
    g.stripCenter_heights_eq
  · rw [g.lowerLeft_height, g.lowerRight_height]
  · exact g.lowerLeft_mem_left.1
  · exact g.lowerRight_mem_right.1
  · exact g.lowerLeft_mem_left.2.2
  · exact g.lowerRight_mem_right.2.2

theorem upper_junction_abscissae_add :
    g.upperLeft.1 + g.upperRight.1 =
      g.leftStripCenter.1 + g.rightStripCenter.1 := by
  linarith [g.upper_horizontal_offsets_eq]

theorem lower_junction_abscissae_add :
    g.lowerLeft.1 + g.lowerRight.1 =
      g.leftStripCenter.1 + g.rightStripCenter.1 := by
  linarith [g.lower_horizontal_offsets_eq]

/-- The upper exterior-circle center lies on the forced axis. -/
theorem upperCenter_on_axis :
    g.upperCenter.1 = g.symmetryAxisX := by
  have hchord :=
    CircleRigidity.chord_abscissae_add_eq_two_mul_center
      g.upperLeft_mem_upper.1 g.upperRight_mem_upper.1
      (by rw [g.upperLeft_height, g.upperRight_height])
      (ne_of_lt g.upper_endpoints_order)
  unfold symmetryAxisX
  linarith [g.upper_junction_abscissae_add]

/-- The lower exterior-circle center lies on the same forced axis. -/
theorem lowerCenter_on_axis :
    g.lowerCenter.1 = g.symmetryAxisX := by
  have hchord :=
    CircleRigidity.chord_abscissae_add_eq_two_mul_center
      g.lowerLeft_mem_lower.1 g.lowerRight_mem_lower.1
      (by rw [g.lowerLeft_height, g.lowerRight_height])
      (ne_of_lt g.lower_endpoints_order)
  unfold symmetryAxisX
  linarith [g.lower_junction_abscissae_add]

/-- The independently placed strip-circle centers are reflections in the
forced source axis. -/
theorem rightStripCenter_reflection :
    g.rightStripCenter =
      verticalReflection g.symmetryAxisX g.leftStripCenter := by
  apply Prod.ext
  · simp only [verticalReflection]
    unfold symmetryAxisX
    ring
  · simp only [verticalReflection]
    exact g.stripCenter_heights_eq.symm

/-- The ordered upper junctions are reflected in the forced source axis. -/
theorem upperRight_reflection :
    g.upperRight = verticalReflection g.symmetryAxisX g.upperLeft := by
  apply Prod.ext
  · simp only [verticalReflection]
    unfold symmetryAxisX
    linarith [g.upper_junction_abscissae_add]
  · simp only [verticalReflection]
    rw [g.upperLeft_height, g.upperRight_height]

/-- The ordered lower junctions are reflected in the forced source axis. -/
theorem lowerRight_reflection :
    g.lowerRight = verticalReflection g.symmetryAxisX g.lowerLeft := by
  apply Prod.ext
  · simp only [verticalReflection]
    unfold symmetryAxisX
    linarith [g.lower_junction_abscissae_add]
  · simp only [verticalReflection]
    rw [g.lowerLeft_height, g.lowerRight_height]

/-- Endpoint order makes the upper-left junction strictly left of the forced
axis; no strict branch-offset hypothesis is used. -/
theorem upperLeft_strictly_left_of_axis :
    g.upperLeft.1 < g.symmetryAxisX := by
  unfold symmetryAxisX
  linarith [g.upper_endpoints_order, g.upper_junction_abscissae_add]

/-- Endpoint order gives the corresponding lower strict inequality. -/
theorem lowerLeft_strictly_left_of_axis :
    g.lowerLeft.1 < g.symmetryAxisX := by
  unfold symmetryAxisX
  linarith [g.lower_endpoints_order, g.lower_junction_abscissae_add]

/-- Package the derived bilateral rigidity as the unchanged actual-source
`SourceGeometry`.  Carrier, representative, complete frontier, and local
one-sidedness data are passed through definitionally. -/
def toSourceGeometry : SourceGeometry lam where
  sourceCarrier := g.sourceCarrier
  representative := g.representative
  sourceRepresentative := g.sourceRepresentative
  sourceRadius := g.sourceRadius
  symmetryAxisX := g.symmetryAxisX
  upperCenter := g.upperCenter
  lowerCenter := g.lowerCenter
  leftStripCenter := g.leftStripCenter
  rightStripCenter := g.rightStripCenter
  upperLeft := g.upperLeft
  lowerLeft := g.lowerLeft
  upperRight := g.upperRight
  lowerRight := g.lowerRight
  density_jump := g.density_jump
  sourceRadius_pos := g.sourceRadius_pos
  upperLeft_height := g.upperLeft_height
  upperRight_height := g.upperRight_height
  lowerLeft_height := g.lowerLeft_height
  lowerRight_height := g.lowerRight_height
  upperLeft_strictly_left_of_axis := g.upperLeft_strictly_left_of_axis
  lowerLeft_strictly_left_of_axis := g.lowerLeft_strictly_left_of_axis
  upper_center_on_axis := g.upperCenter_on_axis
  lower_center_on_axis := g.lowerCenter_on_axis
  right_center_reflection := g.rightStripCenter_reflection
  upperRight_reflection := g.upperRight_reflection
  lowerRight_reflection := g.lowerRight_reflection
  upperLeft_mem_upper := g.upperLeft_mem_upper
  upperRight_mem_upper := g.upperRight_mem_upper
  lowerLeft_mem_lower := g.lowerLeft_mem_lower
  lowerRight_mem_lower := g.lowerRight_mem_lower
  upperLeft_mem_left := g.upperLeft_mem_left
  lowerLeft_mem_left := g.lowerLeft_mem_left
  upperRight_mem_right := g.upperRight_mem_right
  lowerRight_mem_right := g.lowerRight_mem_right
  upper_signed_snell := g.upper_left_signed_snell
  lower_signed_snell := g.lower_left_signed_snell
  frontier_eq_four_circles := g.frontier_eq_four_circles
  upper_one_sided := g.upper_one_sided
  lower_one_sided := g.lower_one_sided
  left_one_sided := g.left_one_sided
  right_one_sided := g.right_one_sided

@[simp] theorem toSourceGeometry_sourceCarrier :
    g.toSourceGeometry.sourceCarrier = g.sourceCarrier := rfl

@[simp] theorem toSourceGeometry_representative :
    g.toSourceGeometry.representative = g.representative := rfl

end BilateralSourceIncidence

end CMVFigureFour
