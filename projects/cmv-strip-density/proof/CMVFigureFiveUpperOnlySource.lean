/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveExamples
import CMVSharpLocalTangentDensity
open Set
open Real
open Filter
open MeasureTheory
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVFigureFive.UpperOnlySource

open CMVFigureFour

/-- A replacement carrier is bounded, independently of its cap angle. -/
theorem replacementCarrier_isBounded (a : ReplacementAssembly) :
    Bornology.IsBounded a.carrier := by
  have hrect : Bornology.IsBounded a.core.rectangleCarrier := by
    apply ((Metric.isBounded_Icc (-a.core.chord / 2)
        (a.core.chord / 2)).prod
      (Metric.isBounded_Icc (-1 : ℝ) 1)).subset
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, abs_le.mp hp.2.2⟩
  have hleft : Bornology.IsBounded a.core.leftCapCarrier := by
    apply (isBounded_circleValue_le_zero
      (a.core.leftCenterX, 0) a.core.radius_pos.le).subset
    intro p hp
    change circleValue (a.core.leftCenterX, 0) a.core.radius p ≤ 0
    unfold circleValue
    dsimp only
    nlinarith [hp.1]
  have hright : Bornology.IsBounded a.core.rightCapCarrier := by
    apply (isBounded_circleValue_le_zero
      (a.core.rightCenterX, 0) a.core.radius_pos.le).subset
    intro p hp
    change circleValue (a.core.rightCenterX, 0) a.core.radius p ≤ 0
    unfold circleValue
    dsimp only
    nlinarith [hp.1]
  have hcore : Bornology.IsBounded a.core.carrier :=
    (hrect.union hleft).union hright
  have hupper : Bornology.IsBounded a.upperCap.carrier := by
    apply (isBounded_circleValue_le_zero
      a.upperCap.center a.upperCap.radius_pos.le).subset
    intro p hp
    change circleValue a.upperCap.center a.upperCap.radius p ≤ 0
    have hle := hp.1
    unfold OneSidedCircularCap.radiusSquaredAt at hle
    unfold circleValue
    nlinarith
  exact hcore.union hupper

/-- The complete replacement frontier is planar-null. -/
theorem volume_frontier_replacement (a : ReplacementAssembly) :
    volume (frontier a.carrier) = 0 := by
  have hleft : volume (StripCore.leftArcTrace a.core) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue (a.core.leftCenterX, 0) a.core.radius p = 0})
    · intro p hp
      change circleValue (a.core.leftCenterX, 0) a.core.radius p = 0
      unfold circleValue
      dsimp only
      nlinarith [hp.1]
    · exact volume_circleValue_eq_zero _ _
  have hright : volume (StripCore.rightArcTrace a.core) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        circleValue (a.core.rightCenterX, 0) a.core.radius p = 0})
    · intro p hp
      change circleValue (a.core.rightCenterX, 0) a.core.radius p = 0
      unfold circleValue
      dsimp only
      nlinarith [hp.1]
    · exact volume_circleValue_eq_zero _ _
  have hupper : volume a.upperCap.arcTrace = 0 := by
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
  have hlower : volume a.exposedLowerChord.carrier = 0 := by
    apply measure_mono_null (t := {p : PlanePoint | p.2 = -1})
    · intro p hp
      simpa [ReplacementAssembly.exposedLowerChord,
        HorizontalSegment.carrier] using hp.1
    · exact volume_horizontalLine (-1)
  rw [a.frontier_carrier, ReplacementAssembly.boundaryTrace]
  apply le_antisymm
  · calc
      volume (StripCore.leftArcTrace a.core ∪
          (StripCore.rightArcTrace a.core ∪
            (a.upperCap.arcTrace ∪ a.exposedLowerChord.carrier))) ≤
          volume (StripCore.leftArcTrace a.core) +
            volume (StripCore.rightArcTrace a.core ∪
              (a.upperCap.arcTrace ∪ a.exposedLowerChord.carrier)) :=
        measure_union_le _ _
      _ ≤ volume (StripCore.leftArcTrace a.core) +
          (volume (StripCore.rightArcTrace a.core) +
            volume (a.upperCap.arcTrace ∪ a.exposedLowerChord.carrier)) := by
        gcongr
        exact measure_union_le _ _
      _ ≤ volume (StripCore.leftArcTrace a.core) +
          (volume (StripCore.rightArcTrace a.core) +
            (volume a.upperCap.arcTrace +
              volume a.exposedLowerChord.carrier)) := by
        gcongr
        exact measure_union_le _ _
      _ = 0 := by rw [hleft, hright, hupper, hlower]; norm_num
  · exact bot_le

/-- The open interior is an actual representative of a replacement carrier. -/
theorem replacementSourceRepresentative (a : ReplacementAssembly) :
    SourceRepresentative a.carrier (interior a.carrier) where
  representative_open := isOpen_interior
  representative_bounded := replacementCarrier_isBounded a |>.subset interior_subset
  source_ae_representative := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null (t := frontier a.carrier)
      · rintro p ⟨hpCarrier, hpNotInterior⟩
        rw [mem_frontier_iff_notMem_interior hpCarrier]
        exact hpNotInterior
      · exact volume_frontier_replacement a
    · apply measure_mono_null (t := ∅)
      · rintro p ⟨hpInterior, hpNotCarrier⟩
        exact (hpNotCarrier (interior_subset hpInterior)).elim
      · exact measure_empty
/-- The upper cap of a replacement carrier has the occupied disk side locally. -/
theorem replacement_upper_locallyOneSided
    (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ a.upperCap.arcTrace)
    (hleft : p ≠ a.upperCap.leftEndpoint)
    (hright : p ≠ a.upperCap.rightEndpoint) :
    LocallyOneSided (interior a.carrier) a.upperCap.center
      a.upperCap.radius p := by
  let V : Set PlanePoint := {q | 1 < q.2}
  have hVopen : IsOpen V := isOpen_lt continuous_const continuous_snd
  have hpV : p ∈ V := by
    have hstrict :=
      OneSidedCircularCap.arcTrace_strict_side_of_ne_endpoints
        a.upperCap hp hleft hright
    simpa [V, ReplacementAssembly.upperCap] using hstrict
  have hlocal :
      a.carrier ∩ V =
        V ∩ {q | circleValue a.upperCap.center a.upperCap.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqy⟩
      refine ⟨hqy, ?_⟩
      rw [ReplacementAssembly.carrier] at hqCarrier
      rcases hqCarrier with hqCore | hqUpper
      · have hy := a.core.carrier_y_bounds hqCore
        change 1 < q.2 at hqy
        exact (by nlinarith [le_abs_self q.2])
      · have hle := hqUpper.1
        unfold OneSidedCircularCap.radiusSquaredAt at hle
        unfold circleValue
        nlinarith [hle]
    · rintro ⟨hqy, hqCircle⟩
      refine ⟨?_, hqy⟩
      rw [ReplacementAssembly.carrier]
      apply Or.inr
      constructor
      · unfold OneSidedCircularCap.radiusSquaredAt
        unfold circleValue at hqCircle
        nlinarith
      · unfold V at hqy
        simpa [ReplacementAssembly.upperCap] using hqy.le
  have hzero :
      V ∩ {q | circleValue a.upperCap.center a.upperCap.radius q = 0} ⊆
        frontier a.carrier := by
    intro q hq
    apply a.boundaryTrace_subset_frontier_carrier
    apply Or.inr
    apply Or.inr
    apply Or.inl
    constructor
    · have hz := hq.2
      unfold OneSidedCircularCap.radiusSquaredAt
      unfold circleValue at hz
      exact sub_eq_zero.mp hz
    · unfold V at hq
      simpa [ReplacementAssembly.upperCap] using hq.1.le
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- The retained left strip arc has the occupied disk side locally. -/
theorem replacement_left_locallyOneSided
    (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.leftArcTrace a.core)
    (hupper : p ≠ (-a.core.chord / 2, 1))
    (hlower : p ≠ (-a.core.chord / 2, -1)) :
    LocallyOneSided (interior a.carrier)
      (a.core.leftCenterX, 0) a.core.radius p := by
  have hpHeight := StripCore.leftArcTrace_strict_height_of_ne_endpoints
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
      have hscale := congrArg (fun z : ℝ => a.core.radius ^ 2 * z) htrig
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
        V ∩ {q | circleValue (a.core.leftCenterX, 0) a.core.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      refine ⟨hqV, ?_⟩
      rw [ReplacementAssembly.carrier] at hqCarrier
      rcases hqCarrier with hqCore | hqUpper
      · rcases hqCore with (hqRect | hqLeft) | hqRight
        · exact (by linarith [hqRect.1, hqV.2])
        · have hle := hqLeft.1
          change circleValue (a.core.leftCenterX, 0) a.core.radius q ≤ 0
          unfold circleValue
          dsimp only
          nlinarith
        · exact (by
            have := hqRight.2.1
            linarith [hqV.2, a.core.chord_pos])
      · have hy : (1 : ℝ) ≤ q.2 := by
          simpa [ReplacementAssembly.upperCap] using hqUpper.2
        exact (by linarith [(abs_lt.mp hqV.1).2])
    · rintro ⟨hqV, hqCircle⟩
      refine ⟨?_, hqV⟩
      have hleftCarrier : q ∈ a.core.leftCapCarrier := by
        constructor
        · unfold circleValue at hqCircle
          dsimp only at hqCircle
          nlinarith
        · exact ⟨hqV.2.le, hqV.1.le⟩
      exact Or.inl (Or.inl (Or.inr hleftCarrier))
  have hzero :
      V ∩ {q | circleValue (a.core.leftCenterX, 0) a.core.radius q = 0} ⊆
        frontier a.carrier := by
    intro q hq
    apply a.boundaryTrace_subset_frontier_carrier
    apply Or.inl
    constructor
    · have hz := hq.2
      change circleValue (a.core.leftCenterX, 0) a.core.radius q = 0 at hz
      unfold circleValue at hz
      dsimp only at hz
      exact sub_eq_zero.mp (by simpa only [sub_zero] using hz)
    · exact ⟨hq.1.2.le, hq.1.1.le⟩
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- The retained right strip arc has the occupied disk side locally. -/
theorem replacement_right_locallyOneSided
    (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p ∈ StripCore.rightArcTrace a.core)
    (hupper : p ≠ (a.core.chord / 2, 1))
    (hlower : p ≠ (a.core.chord / 2, -1)) :
    LocallyOneSided (interior a.carrier)
      (a.core.rightCenterX, 0) a.core.radius p := by
  have hpHeight := StripCore.rightArcTrace_strict_height_of_ne_endpoints
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
      have hscale := congrArg (fun z : ℝ => a.core.radius ^ 2 * z) htrig
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
        V ∩ {q | circleValue (a.core.rightCenterX, 0) a.core.radius q ≤ 0} := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      refine ⟨hqV, ?_⟩
      rw [ReplacementAssembly.carrier] at hqCarrier
      rcases hqCarrier with hqCore | hqUpper
      · rcases hqCore with (hqRect | hqLeft) | hqRight
        · exact (by linarith [hqRect.2.1, hqV.2])
        · exact (by
            have := hqLeft.2.1
            linarith [hqV.2, a.core.chord_pos])
        · have hle := hqRight.1
          change circleValue (a.core.rightCenterX, 0) a.core.radius q ≤ 0
          unfold circleValue
          dsimp only
          nlinarith
      · have hy : (1 : ℝ) ≤ q.2 := by
          simpa [ReplacementAssembly.upperCap] using hqUpper.2
        exact (by linarith [(abs_lt.mp hqV.1).2])
    · rintro ⟨hqV, hqCircle⟩
      refine ⟨?_, hqV⟩
      have hrightCarrier : q ∈ a.core.rightCapCarrier := by
        constructor
        · unfold circleValue at hqCircle
          dsimp only at hqCircle
          nlinarith
        · exact ⟨hqV.2.le, hqV.1.le⟩
      exact Or.inl (Or.inr hrightCarrier)
  have hzero :
      V ∩ {q | circleValue (a.core.rightCenterX, 0) a.core.radius q = 0} ⊆
        frontier a.carrier := by
    intro q hq
    apply a.boundaryTrace_subset_frontier_carrier
    apply Or.inr
    apply Or.inl
    constructor
    · have hz := hq.2
      change circleValue (a.core.rightCenterX, 0) a.core.radius q = 0 at hz
      unfold circleValue at hz
      dsimp only at hz
      exact sub_eq_zero.mp (by simpa only [sub_zero] using hz)
    · exact ⟨hq.1.2.le, hq.1.1.le⟩
  exact locallyOneSided_interior_of_local_closedDisk
    a.isClosed_carrier hVopen hpV hlocal hzero

/-- Local one-sidedness supplies interior points converging to the circle point. -/
private theorem replacement_mem_closure_of_locallyOneSided
    {a : ReplacementAssembly} {center p : PlanePoint} {radius : ℝ}
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

/-- Each retained-core junction is approached through the strict rectangle. -/
private theorem replacement_endpoint_mem_closure
    (a : ReplacementAssembly) (horizontalSign verticalSign : ℝ)
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
    exact Or.inl (Or.inl (Or.inl
      ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩))
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

/-- A strict point of the lower chord is approached from the core interior. -/
private theorem replacement_strictLower_mem_closure
    (a : ReplacementAssembly) {p : PlanePoint}
    (hy : p.2 = -1) (hx : |p.1| < a.core.chord / 2) :
    p ∈ closure (interior a.carrier) := by
  let t : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let q : ℕ → PlanePoint := fun n => (p.1, -1 + t n)
  have ht : Filter.Tendsto t Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hq : Filter.Tendsto q Filter.atTop (nhds p) := by
    have hxlim : Filter.Tendsto (fun _ : ℕ => p.1)
        Filter.atTop (nhds p.1) := tendsto_const_nhds
    have hylim : Filter.Tendsto (fun n : ℕ => (-1 : ℝ) + t n)
        Filter.atTop (nhds ((-1 : ℝ) + 0)) :=
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (-1 : ℝ))
        Filter.atTop (nhds (-1))).add ht
    rw [show (-1 : ℝ) + 0 = p.2 by rw [hy]; norm_num] at hylim
    exact hxlim.prodMk_nhds hylim
  apply mem_closure_of_tendsto hq
  filter_upwards [] with n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have htpos : 0 < t n := div_pos zero_lt_one hn
  have htle : t n ≤ 1 := (div_le_one hn).2 (by norm_num)
  let W : Set PlanePoint :=
    {z | -a.core.chord / 2 < z.1 ∧
      z.1 < a.core.chord / 2 ∧ |z.2| < 1}
  apply interior_maximal (t := W)
  · intro z hz
    exact Or.inl (Or.inl (Or.inl
      ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩))
  · exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_snd.abs continuous_const))
  · change -a.core.chord / 2 < p.1 ∧
      p.1 < a.core.chord / 2 ∧ |-1 + t n| < 1
    have hxbounds := abs_lt.mp hx
    exact ⟨by simpa only [neg_div] using hxbounds.1, hxbounds.2,
      abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- A replacement carrier is the closure of its open interior. -/
theorem replacement_closure_interior (a : ReplacementAssembly) :
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
          simpa only [neg_one_mul, neg_div] using
            replacement_endpoint_mem_closure a (-1) 1
              (Or.inr rfl) (Or.inl rfl)
        · by_cases hbottom : p = (-a.core.chord / 2, -1)
          · subst p
            simpa only [neg_one_mul, neg_div] using
              replacement_endpoint_mem_closure a (-1) (-1)
                (Or.inr rfl) (Or.inr rfl)
          · exact replacement_mem_closure_of_locallyOneSided a.core.radius_pos
              (by simpa [circleValue] using sub_eq_zero.mpr hleft.1)
              (replacement_left_locallyOneSided a hleft htop hbottom)
      · by_cases htop : p = (a.core.chord / 2, 1)
        · subst p
          simpa using replacement_endpoint_mem_closure a 1 1
            (Or.inl rfl) (Or.inl rfl)
        · by_cases hbottom : p = (a.core.chord / 2, -1)
          · subst p
            simpa using replacement_endpoint_mem_closure a 1 (-1)
              (Or.inl rfl) (Or.inr rfl)
          · exact replacement_mem_closure_of_locallyOneSided a.core.radius_pos
              (by simpa [circleValue] using sub_eq_zero.mpr hright.1)
              (replacement_right_locallyOneSided a hright htop hbottom)
      · by_cases hleftEnd : p = (-a.core.chord / 2, 1)
        · subst p
          simpa only [neg_one_mul, neg_div] using
            replacement_endpoint_mem_closure a (-1) 1
              (Or.inr rfl) (Or.inl rfl)
        · by_cases hrightEnd : p = (a.core.chord / 2, 1)
          · subst p
            simpa using replacement_endpoint_mem_closure a 1 1
              (Or.inl rfl) (Or.inl rfl)
          · exact replacement_mem_closure_of_locallyOneSided
              a.upperCap.radius_pos
              (by simpa [circleValue,
                OneSidedCircularCap.radiusSquaredAt] using
                  sub_eq_zero.mpr hupper.1)
              (replacement_upper_locallyOneSided a hupper
                (by
                  intro heq
                  apply hleftEnd
                  rw [heq]
                  simp [ReplacementAssembly.upperCap,
                    OneSidedCircularCap.leftEndpoint]
                  ring)
                (by
                  simpa [ReplacementAssembly.upperCap,
                    OneSidedCircularCap.rightEndpoint] using hrightEnd))
      · have hy : p.2 = -1 := by
          simpa [ReplacementAssembly.exposedLowerChord,
            HorizontalSegment.carrier] using hlower.1
        have hx : |p.1| ≤ a.core.chord / 2 := by
          simpa [ReplacementAssembly.exposedLowerChord,
            HorizontalSegment.carrier] using hlower.2
        by_cases hstrict : |p.1| < a.core.chord / 2
        · exact replacement_strictLower_mem_closure a hy hstrict
        · have habs : |p.1| = a.core.chord / 2 :=
            le_antisymm hx (le_of_not_gt hstrict)
          have hhalf : 0 < a.core.chord / 2 :=
            div_pos a.core.chord_pos (by norm_num)
          rcases (abs_eq hhalf.le).mp habs with hxright | hxleft
          · have hpEq : p = (a.core.chord / 2, -1) :=
              Prod.ext hxright hy
            subst p
            simpa using replacement_endpoint_mem_closure a 1 (-1)
              (Or.inl rfl) (Or.inr rfl)
          · have hpEq : p = (-(a.core.chord / 2), -1) :=
              Prod.ext hxleft hy
            subst p
            simpa only [neg_one_mul, neg_div] using
              replacement_endpoint_mem_closure a (-1) (-1)
                (Or.inr rfl) (Or.inr rfl)
theorem replacement_frontier_interior (a : ReplacementAssembly) :
    frontier (interior a.carrier) = a.boundaryTrace := by
  rw [isOpen_interior.frontier_eq, replacement_closure_interior,
    ← a.isClosed_carrier.frontier_eq, a.frontier_carrier]

open CMVFigureFive.Examples

/-- The endpoint candidate with only its upper cap retained. -/
def upperOnlyAssembly : ReplacementAssembly where
  core := endpointCandidate.stripCore
  replacementAngle := endpointCandidate.alpha
  replacementAngle_pos := endpointCandidate.alpha_pos
  replacementAngle_lt_pi :=
    endpointCandidate.alpha_lt_pi_div_two.trans (by linarith [Real.pi_pos])

private def pointSegment (x y : ℝ) :
    CMVFigureThree.DegenerateHorizontalSegment where
  leftX := x
  rightX := x
  baseY := y
  left_le_right := le_rfl

@[simp] private theorem pointSegment_carrier (x y : ℝ) :
    (pointSegment x y).carrier = {(x, y)} := by
  ext p
  simp only [CMVFigureThree.DegenerateHorizontalSegment.carrier,
    pointSegment, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hy, hleft, hright⟩
    exact Prod.ext (le_antisymm hright hleft) hy
  · rintro rfl
    exact ⟨rfl, le_rfl, le_rfl⟩

private theorem endpoint_h_eq_one : endpointCandidate.h = 1 := by
  have hne : endpointCandidate.h ≠ 0 := ne_of_gt endpointCandidate.h_pos
  have hr := endpointCandidate_radius
  change 1 / endpointCandidate.h = 1 at hr
  simpa only [one_mul] using ((div_eq_iff hne).mp hr).symm

private theorem endpoint_core_cos_eq_zero :
    cos endpointCandidate.stripCore.sideAngle = 0 := by
  rw [endpointCandidate.stripCore.cos_sideAngle]
  rw [show endpointCandidate.stripCore.curvature = endpointCandidate.h by rfl,
    endpoint_h_eq_one]
  norm_num

private theorem endpoint_leftCenterX_eq_negHalf :
    upperOnlyAssembly.core.leftCenterX =
      -upperOnlyAssembly.core.chord / 2 := by
  simp [upperOnlyAssembly, StripCore.leftCenterX, endpoint_core_cos_eq_zero]

private theorem endpoint_rightCenterX_eq_half :
    upperOnlyAssembly.core.rightCenterX =
      upperOnlyAssembly.core.chord / 2 := by
  simp [upperOnlyAssembly, StripCore.rightCenterX, endpoint_core_cos_eq_zero]

private theorem endpoint_leftCenterX :
    endpointCandidate.stripCore.leftCenterX =
      upperOnlyAssembly.upperCap.leftEndpoint.1 := by
  rw [StripCore.leftCenterX, endpoint_core_cos_eq_zero]
  simp [upperOnlyAssembly, ReplacementAssembly.upperCap,
    OneSidedCircularCap.leftEndpoint]
  ring

private theorem endpoint_rightCenterX :
    endpointCandidate.stripCore.rightCenterX =
      upperOnlyAssembly.upperCap.rightEndpoint.1 := by
  rw [StripCore.rightCenterX, endpoint_core_cos_eq_zero]
  simp [upperOnlyAssembly, ReplacementAssembly.upperCap,
    OneSidedCircularCap.rightEndpoint]

/-- The upper cap meets both strip tangencies and obeys the lambda-two law. -/
def upperBoundary : CappedInterface 2 upperOnlyAssembly.core.radius
    upperOnlyAssembly.core.leftCenterX upperOnlyAssembly.core.rightCenterX .upper where
  cap := upperOnlyAssembly.upperCap
  leftSegment := pointSegment upperOnlyAssembly.core.leftCenterX 1
  rightSegment := pointSegment upperOnlyAssembly.core.rightCenterX 1
  cap_side := rfl
  cap_base := rfl
  cap_radius := by
    change endpointCandidate.assembly.upperCap.radius =
      endpointCandidate.stripCore.radius
    exact endpointCandidate.four_arcs_common_radius.1
  signed_contact_law := by
    change 2 * cos endpointCandidate.alpha = 1
    simpa [endpointCandidate,
      CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
      CMVSourceClassification.RawFourArcCoordinates.curvature,
      CMVFigureFour.Examples.endpointRaw] using
      CMVFigureFour.Examples.endpointRaw_satisfiesClosedSnell.snell_incidence
  left_segment_base := rfl
  right_segment_base := rfl
  left_segment_starts_at_tangency := rfl
  left_segment_ends_at_cap := endpoint_leftCenterX
  right_segment_starts_at_cap := endpoint_rightCenterX
  right_segment_ends_at_tangency := rfl

/-- The full lower chord is exposed, rather than replaced by a lower cap. -/
def lowerExposed : ExposedInterface upperOnlyAssembly.core.leftCenterX
    upperOnlyAssembly.core.rightCenterX .lower where
  segment :=
    { leftX := upperOnlyAssembly.core.leftCenterX
      rightX := upperOnlyAssembly.core.rightCenterX
      baseY := -1
      left_le_right := by
        rw [show upperOnlyAssembly.core.leftCenterX =
            -upperOnlyAssembly.core.chord / 2 by
          simp [upperOnlyAssembly, StripCore.leftCenterX,
            endpoint_core_cos_eq_zero]]
        rw [show upperOnlyAssembly.core.rightCenterX =
            upperOnlyAssembly.core.chord / 2 by
          simp [upperOnlyAssembly, StripCore.rightCenterX,
            endpoint_core_cos_eq_zero]]
        linarith [upperOnlyAssembly.core.chord_pos] }
  segment_base := rfl
  segment_starts_at_left_tangency := rfl
  segment_ends_at_right_tangency := rfl

private theorem lowerExposed_trace :
    lowerExposed.segment.carrier = upperOnlyAssembly.exposedLowerChord.carrier := by
  ext p
  simp only [lowerExposed,
    CMVFigureThree.DegenerateHorizontalSegment.carrier,
    ReplacementAssembly.exposedLowerChord, HorizontalSegment.carrier,
    mem_ofPred_eq, sub_zero]
  rw [show upperOnlyAssembly.core.leftCenterX =
      -upperOnlyAssembly.core.chord / 2 by
    simp [upperOnlyAssembly, StripCore.leftCenterX, endpoint_core_cos_eq_zero]]
  rw [show upperOnlyAssembly.core.rightCenterX =
      upperOnlyAssembly.core.chord / 2 by
    simp [upperOnlyAssembly, StripCore.rightCenterX, endpoint_core_cos_eq_zero]]
  constructor
  · rintro ⟨hy, hleft, hright⟩
    refine ⟨hy, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · rintro ⟨hy, hx⟩
    rw [abs_le] at hx
    exact ⟨hy, by simpa only [neg_div] using hx.1, hx.2⟩

private theorem upperBoundary_trace :
    upperBoundary.trace = upperOnlyAssembly.upperCap.arcTrace := by
  rw [CappedInterface.trace]
  simp only [upperBoundary, pointSegment_carrier]
  ext p
  simp only [mem_union, mem_singleton_iff]
  constructor
  · rintro (rfl | hp | rfl)
    · convert
        OneSidedCircularCap.leftEndpoint_mem_arcTrace upperOnlyAssembly.upperCap
        using 1
      apply Prod.ext
      · exact endpoint_leftCenterX
      · rfl
    · exact hp
    · convert
        OneSidedCircularCap.rightEndpoint_mem_arcTrace upperOnlyAssembly.upperCap
        using 1
      apply Prod.ext
      · exact endpoint_rightCenterX
      · rfl
  · exact fun hp => Or.inr (Or.inl hp)

private theorem upperOnly_leftArcTrace :
    upperOnlyAssembly.core.leftArcTrace =
      stripCircleTrace .left
        (upperOnlyAssembly.core.leftCenterX, 0)
        upperOnlyAssembly.core.radius := by
  simpa [upperOnlyAssembly] using
    FourArcAssembly.leftArcTrace_eq_stripCircleTrace endpointCandidate.assembly

private theorem upperOnly_rightArcTrace :
    upperOnlyAssembly.core.rightArcTrace =
      stripCircleTrace .right
        (upperOnlyAssembly.core.rightCenterX, 0)
        upperOnlyAssembly.core.radius := by
  simpa [upperOnlyAssembly] using
    FourArcAssembly.rightArcTrace_eq_stripCircleTrace endpointCandidate.assembly

/-- Full lambda-two Figure-5 source with one upper cap and a genuinely exposed
positive-length lower interface. -/
def source : SourceGeometry 2 where
  sourceCarrier := upperOnlyAssembly.carrier
  representative := interior upperOnlyAssembly.carrier
  sourceRepresentative := replacementSourceRepresentative upperOnlyAssembly
  sourceRadius := upperOnlyAssembly.core.radius
  leftStripCenter := (upperOnlyAssembly.core.leftCenterX, 0)
  rightStripCenter := (upperOnlyAssembly.core.rightCenterX, 0)
  upperLeftTangent := (upperOnlyAssembly.core.leftCenterX, 1)
  upperRightTangent := (upperOnlyAssembly.core.rightCenterX, 1)
  lowerLeftTangent := (upperOnlyAssembly.core.leftCenterX, -1)
  lowerRightTangent := (upperOnlyAssembly.core.rightCenterX, -1)
  density_jump := by norm_num
  sourceRadius_pos := upperOnlyAssembly.core.radius_pos
  strip_centers_ordered := by
    rw [show upperOnlyAssembly.core.leftCenterX =
        -upperOnlyAssembly.core.chord / 2 by
      simp [upperOnlyAssembly, StripCore.leftCenterX, endpoint_core_cos_eq_zero]]
    rw [show upperOnlyAssembly.core.rightCenterX =
        upperOnlyAssembly.core.chord / 2 by
      simp [upperOnlyAssembly, StripCore.rightCenterX, endpoint_core_cos_eq_zero]]
    linarith [upperOnlyAssembly.core.chord_pos]
  upper_left_tangent_coordinate := rfl
  upper_right_tangent_coordinate := rfl
  lower_left_tangent_coordinate := rfl
  lower_right_tangent_coordinate := rfl
  upper_left_on_strip_circle := by
    unfold circleValue
    dsimp only
    rw [show upperOnlyAssembly.core.radius = 1 by
      exact endpointCandidate_radius]
    norm_num
  upper_right_on_strip_circle := by
    unfold circleValue
    dsimp only
    rw [show upperOnlyAssembly.core.radius = 1 by
      exact endpointCandidate_radius]
    norm_num
  lower_left_on_strip_circle := by
    unfold circleValue
    dsimp only
    rw [show upperOnlyAssembly.core.radius = 1 by
      exact endpointCandidate_radius]
    norm_num
  lower_right_on_strip_circle := by
    unfold circleValue
    dsimp only
    rw [show upperOnlyAssembly.core.radius = 1 by
      exact endpointCandidate_radius]
    norm_num
  upperBoundary := .capped upperBoundary
  lowerBoundary := .exposed lowerExposed
  has_exterior_cap := Or.inl trivial
  frontier_eq_components := by
    rw [replacement_frontier_interior,
      ReplacementAssembly.boundaryTrace,
      upperOnly_leftArcTrace, upperOnly_rightArcTrace]
    simp only [InterfaceBoundary.trace]
    rw [upperBoundary_trace, lowerExposed_trace]
  left_strip_one_sided := by
    intro p hp hupper hlower
    apply replacement_left_locallyOneSided upperOnlyAssembly
    · rw [upperOnly_leftArcTrace]
      exact hp
    · intro heq
      apply hupper
      rw [heq]
      exact Prod.ext endpoint_leftCenterX_eq_negHalf.symm rfl
    · intro heq
      apply hlower
      rw [heq]
      exact Prod.ext endpoint_leftCenterX_eq_negHalf.symm rfl
  right_strip_one_sided := by
    intro p hp hupper hlower
    apply replacement_right_locallyOneSided upperOnlyAssembly
    · rw [upperOnly_rightArcTrace]
      exact hp
    · intro heq
      apply hupper
      rw [heq]
      exact Prod.ext endpoint_rightCenterX_eq_half.symm rfl
    · intro heq
      apply hlower
      rw [heq]
      exact Prod.ext endpoint_rightCenterX_eq_half.symm rfl
  upper_cap_one_sided := by
    intro p hp hleft hright
    change LocallyOneSided (interior upperOnlyAssembly.carrier)
      upperOnlyAssembly.upperCap.center upperOnlyAssembly.core.radius p
    rw [← upperBoundary.cap_radius]
    exact replacement_upper_locallyOneSided upperOnlyAssembly hp hleft hright
  lower_cap_one_sided := trivial

@[simp] theorem source_upper_isCapped : source.upperBoundary.IsCapped := trivial

@[simp] theorem source_lower_isExposed : ¬ source.lowerBoundary.IsCapped := by
  simp [source, InterfaceBoundary.IsCapped]

/-- The exposed lower boundary has the strictly positive core chord as length. -/
theorem source_lowerBoundary_positiveLength :
    source.lowerBoundary.trace = upperOnlyAssembly.exposedLowerChord.carrier ∧
      0 < upperOnlyAssembly.exposedLowerChord.euclideanLength := by
  constructor
  · simpa [source, InterfaceBoundary.trace] using lowerExposed_trace
  · simpa [ReplacementAssembly.exposedLowerChord,
      HorizontalSegment.euclideanLength] using upperOnlyAssembly.core.chord_pos

/-- The required threshold equation is visible on the actual source cap. -/
theorem source_upper_threshold :
    2 * cos upperBoundary.cap.theta = 1 :=
  upperBoundary.signed_contact_law

/-- Existing Figure-5 section reconstruction applies unchanged to the specimen,
so the occupied strict-strip side is derived from `SourceGeometry`. -/
theorem source_strictStripSection {y : ℝ} (hy : |y| < 1) :
    CMVSourceClassification.horizontalSection source.representative y =
      Ioo ((source.leftStripBoundaryPoint y).1)
        ((source.rightStripBoundaryPoint y).1) :=
  source.actual_strictStripSection hy

/-- The exposed lower side has no occupied exterior section below it. -/
theorem source_lowerExterior_empty {y : ℝ} (hy : y < -1) :
    CMVSourceClassification.horizontalSection source.representative y = ∅ :=
  source.actual_lowerExposedSection_empty lowerExposed rfl hy


/-- The midpoint of the exposed lower chord lies strictly between its two
strip junctions. -/
theorem source_leftStripCenter_lt_zero : source.leftStripCenter.1 < 0 := by
  change upperOnlyAssembly.core.leftCenterX < 0
  rw [endpoint_leftCenterX_eq_negHalf]
  linarith [upperOnlyAssembly.core.chord_pos]

theorem source_zero_lt_rightStripCenter : 0 < source.rightStripCenter.1 := by
  change 0 < upperOnlyAssembly.core.rightCenterX
  rw [endpoint_rightCenterX_eq_half]
  linarith [upperOnlyAssembly.core.chord_pos]

/-- At the midpoint of the exposed segment, the occupied side is locally the
side above the retained lower section. -/
theorem source_lowerExposed_eventually_mem_iff_above :
    ∀ᶠ q in 𝓝 ((0, -1) : PlanePoint),
      q ∈ source.representative ↔ -1 < q.2 :=
  source.lowerExposed_eventually_mem_iff_above lowerExposed rfl
    source_leftStripCenter_lt_zero source_zero_lt_rightStripCenter

/-- The concrete exposed midpoint realizes the sharp coefficient-one lower
density bound for every converging smooth sequence. -/
theorem source_lowerExposed_sharp_limitDensity
    {A : CMVRelaxation.SmoothSequence} {K : Set PlanePoint}
    (L : CMVRelaxation.CompactCoreEnergy.Limit 2 A K)
    (hconv : A.ConvergesTo source.representative)
    (hpK : ((0, -1) : PlanePoint) ∈ interior K) :
    (1 : ℝ≥0∞) ≤
      liminf
        (CMVRelaxation.CompactCoreEnergy.euclideanClosedBallDensity
          L (0, -1)) (𝓝[>] (0 : ℝ)) :=
  source.lowerExposed_sharp_limitDensity lowerExposed rfl
    source_leftStripCenter_lt_zero source_zero_lt_rightStripCenter
    L hconv hpK

/-- Before either endpoint enters the ball, the concrete exposed segment has
exact Euclidean `H¹` density one at its midpoint. -/
theorem source_lowerExposed_euclideanH1_inter_closedBall_eq
    {r : ℝ} (hr : r ≤ upperOnlyAssembly.core.chord / 2) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' lowerExposed.segment.carrier ∩
          Metric.closedBall (planeEuclideanHomeomorph (0, -1)) r) =
      ENNReal.ofReal (2 * r) := by
  apply source.lowerExposed_euclideanH1_inter_closedBall_eq lowerExposed
  · change r ≤ 0 - upperOnlyAssembly.core.leftCenterX
    rw [endpoint_leftCenterX_eq_negHalf]
    linarith
  · change r ≤ upperOnlyAssembly.core.rightCenterX - 0
    rw [endpoint_rightCenterX_eq_half]
    linarith

end CMVFigureFive.UpperOnlySource
