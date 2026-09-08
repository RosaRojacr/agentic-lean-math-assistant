/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceSectionClassification

/-!
# Source-facing geometry for CMV Figure 4

This module freezes the primitive input for Cañete--Miranda--Vittone,
Lemma 3.8, Step 2 (printed pages 16--17, equations (24)--(25), Figure 4).
It starts from an actual source set and a bounded open representative, four
literal common-radius circle traces, vertical-line reflection, signed Snell
laws, endpoint incidence, and local one-sidedness at regular arc points.

The signature does not contain raw four-arc coordinates, a modeled assembly,
horizontal-axis symmetry, the scalar height or radical-alignment conclusions,
a principal exterior angle, target section endpoints or measures, carrier
identification, or a comparison theorem.  Those are downstream obligations.
It does not assume interval sections, section connectedness, or a target
frontier.  These must be derived from bounded openness, the literal complete
frontier, and transverse local one-sidedness.  Proposition 3.9 (printed page 18)
supplies only the permitted vertical-line reflection data.  No global
smooth-domain condition is imposed at the four Snell junctions.
-/

open Set
open Real
open MeasureTheory

noncomputable section

namespace CMVFigureFour

/-- Squared circle equation, with the boundary normalized to value zero. -/
def circleValue (center : PlanePoint) (radius : ℝ) (p : PlanePoint) : ℝ :=
  (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 - radius ^ 2

/-- Which horizontal branch of a supporting circle is used by a strip-side
arc.  This is source branch data, not a normalized width formula. -/
inductive HorizontalCircleBranch where
  | left
  | right
  deriving DecidableEq, Repr

namespace HorizontalCircleBranch

/-- The closed branch inequality. -/
def Holds (branch : HorizontalCircleBranch) (center p : PlanePoint) : Prop :=
  match branch with
  | .left => p.1 ≤ center.1
  | .right => center.1 ≤ p.1

end HorizontalCircleBranch

/-- Literal strip-side circle trace between the two density interfaces. -/
def stripCircleTrace (branch : HorizontalCircleBranch)
    (center : PlanePoint) (radius : ℝ) : Set PlanePoint :=
  {p | circleValue center radius p = 0 ∧ |p.2| ≤ 1 ∧ branch.Holds center p}

/-- Literal exterior circle trace on the selected side of a density
interface.  Minor and major branches are not conflated at this level. -/
def exteriorCircleTrace (side : CapSide) (center : PlanePoint)
    (radius : ℝ) : Set PlanePoint :=
  {p | circleValue center radius p = 0 ∧
    match side with
    | .upper => 1 ≤ p.2
    | .lower => p.2 ≤ -1}

/-- Reflection in the source vertical line `x = axis`.  It is deliberately
not reflection in the horizontal axis. -/
def verticalReflection (axis : ℝ) (p : PlanePoint) : PlanePoint :=
  (2 * axis - p.1, p.2)

/-- The two possible local sides of a regular circle.  `inside` uses
`circleValue < 0`; `outside` uses `-circleValue < 0`. -/
inductive CircleSide where
  | inside
  | outside
  deriving DecidableEq, Repr

namespace CircleSide

/-- Multiplier in the explicit local one-sided equation. -/
def sign : CircleSide → ℝ
  | .inside => 1
  | .outside => -1

@[simp] theorem sign_eq_one_or_neg_one (side : CircleSide) :
    side.sign = 1 ∨ side.sign = -1 := by
  cases side <;> simp [sign]

end CircleSide

/-- Local equality with one side of the literal circle equation.  The side may
be either orientation and the condition concerns only a neighborhood of one
actual regular boundary point. -/
def LocallyOneSided (U : Set PlanePoint) (center : PlanePoint)
    (radius : ℝ) (p : PlanePoint) : Prop :=
  ∃ (side : CircleSide) (V : Set PlanePoint),
    IsOpen V ∧ p ∈ V ∧
      U ∩ V = V ∩ {q | side.sign * circleValue center radius q < 0}

/-- A reusable topological bridge: two horizontal sequences approaching an
actual source point from opposite membership sides place its abscissa on the
frontier of the actual horizontal section. -/
theorem mem_frontier_horizontalSection_of_two_sided_sequences
    {U : Set PlanePoint} {p : PlanePoint}
    {inside outside : ℕ → ℝ}
    (hinside : Filter.Tendsto inside Filter.atTop (nhds p.1))
    (houtside : Filter.Tendsto outside Filter.atTop (nhds p.1))
    (hinside_mem : ∀ᶠ n in Filter.atTop, (inside n, p.2) ∈ U)
    (houtside_not_mem : ∀ᶠ n in Filter.atTop, (outside n, p.2) ∉ U) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection U p.2) := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · apply mem_closure_of_tendsto hinside
    filter_upwards [hinside_mem] with n hn
    exact hn
  · apply mem_closure_of_tendsto houtside
    filter_upwards [houtside_not_mem] with n hn
    exact hn

/-- Local one-sided circle geometry plus nonvertical circle tangent produces
an actual boundary point of the horizontal section.  This is the reverse
direction missing from the general continuous-preimage frontier inclusion. -/
theorem circlePoint_mem_frontier_horizontalSection_of_localOneSided
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (htransverse : p.1 ≠ center.1)
    (hlocal : LocallyOneSided U center radius p) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection U p.2) := by
  rcases hlocal with ⟨side, V, hVopen, hpV, hUV⟩
  let d : ℝ := p.1 - center.1
  let step : ℕ → ℝ := fun n => d / ((n : ℝ) + 1)
  let minus : ℕ → ℝ := fun n => p.1 - step n
  let plus : ℕ → ℝ := fun n => p.1 + step n
  have hd : d ≠ 0 := sub_ne_zero.mpr htransverse
  have hstep : Filter.Tendsto step Filter.atTop (nhds 0) := by
    dsimp only [step]
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      ((tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℕ => d) Filter.atTop (nhds d)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hminus : Filter.Tendsto minus Filter.atTop (nhds p.1) := by
    dsimp only [minus]
    simpa only [sub_zero] using tendsto_const_nhds.sub hstep
  have hplus : Filter.Tendsto plus Filter.atTop (nhds p.1) := by
    dsimp only [plus]
    simpa only [add_zero] using tendsto_const_nhds.add hstep
  have hminusPlane :
      Filter.Tendsto (fun n => (minus n, p.2)) Filter.atTop (nhds p) := by
    simpa only [Prod.eta] using
      hminus.prodMk_nhds (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => p.2) Filter.atTop (nhds p.2))
  have hplusPlane :
      Filter.Tendsto (fun n => (plus n, p.2)) Filter.atTop (nhds p) := by
    simpa only [Prod.eta] using
      hplus.prodMk_nhds (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => p.2) Filter.atTop (nhds p.2))
  have hminusV : ∀ᶠ n in Filter.atTop, (minus n, p.2) ∈ V :=
    hminusPlane.eventually (hVopen.mem_nhds hpV)
  have hplusV : ∀ᶠ n in Filter.atTop, (plus n, p.2) ∈ V :=
    hplusPlane.eventually (hVopen.mem_nhds hpV)
  have hminusValue (n : ℕ) :
      circleValue center radius (minus n, p.2) =
        d ^ 2 * (1 - 2 * ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc
      circleValue center radius (minus n, p.2) =
          circleValue center radius p - 2 * d * step n + (step n) ^ 2 := by
            simp only [circleValue]
            dsimp only [minus, d]
            ring
      _ = d ^ 2 * (1 - 2 * ((n : ℝ) + 1)) /
          ((n : ℝ) + 1) ^ 2 := by
            rw [hcircle]
            dsimp only [step]
            field_simp [ne_of_gt hden]
            ring
  have hplusValue (n : ℕ) :
      circleValue center radius (plus n, p.2) =
        d ^ 2 * (2 * ((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) ^ 2 := by
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc
      circleValue center radius (plus n, p.2) =
          circleValue center radius p + 2 * d * step n + (step n) ^ 2 := by
            simp only [circleValue]
            dsimp only [plus, d]
            ring
      _ = d ^ 2 * (2 * ((n : ℝ) + 1) + 1) /
          ((n : ℝ) + 1) ^ 2 := by
            rw [hcircle]
            dsimp only [step]
            field_simp [ne_of_gt hden]
            ring
  have hminusNegative (n : ℕ) :
      circleValue center radius (minus n, p.2) < 0 := by
    rw [hminusValue]
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfactor : 1 - 2 * ((n : ℝ) + 1) < 0 := by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hd) hfactor)
      (sq_pos_of_pos hden)
  have hplusPositive (n : ℕ) :
      0 < circleValue center radius (plus n, p.2) := by
    rw [hplusValue]
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfactor : 0 < 2 * ((n : ℝ) + 1) + 1 := by positivity
    exact div_pos
      (mul_pos (sq_pos_of_ne_zero hd) hfactor)
      (sq_pos_of_pos hden)
  have hmem_iff {q : PlanePoint} (hqV : q ∈ V) :
      q ∈ U ↔ side.sign * circleValue center radius q < 0 := by
    constructor
    · intro hqU
      have hq : q ∈ U ∩ V := ⟨hqU, hqV⟩
      rw [hUV] at hq
      exact hq.2
    · intro hqSide
      have hq : q ∈ V ∩
          {z | side.sign * circleValue center radius z < 0} :=
        ⟨hqV, hqSide⟩
      rw [← hUV] at hq
      exact hq.1
  cases side with
  | inside =>
      apply mem_frontier_horizontalSection_of_two_sided_sequences
        hminus hplus
      · filter_upwards [hminusV] with n hn
        apply (hmem_iff hn).2
        simpa [CircleSide.sign] using hminusNegative n
      · filter_upwards [hplusV] with n hn
        intro hmem
        have hsign := (hmem_iff hn).1 hmem
        simp only [CircleSide.sign, one_mul] at hsign
        exact (not_lt_of_ge (hplusPositive n).le) hsign
  | outside =>
      apply mem_frontier_horizontalSection_of_two_sided_sequences
        hplus hminus
      · filter_upwards [hplusV] with n hn
        apply (hmem_iff hn).2
        simp only [CircleSide.sign, neg_one_mul]
        linarith [hplusPositive n]
      · filter_upwards [hminusV] with n hn
        intro hmem
        have hsign := (hmem_iff hn).1 hmem
        simp only [CircleSide.sign, neg_one_mul] at hsign
        linarith [hminusNegative n]

namespace FiniteCrossingExample

/-- An independently constructed Euclidean open unit disk used to exercise the
finite-crossing reconstruction without a supplied section formula. -/
def openUnitDisk : Set PlanePoint :=
  {p | p.1 ^ 2 + p.2 ^ 2 < 1}

theorem isOpen_openUnitDisk : IsOpen openUnitDisk := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem isBounded_openUnitDisk : Bornology.IsBounded openUnitDisk := by
  have hIcc : Bornology.IsBounded (Icc (-1 : ℝ) 1) :=
    Metric.isBounded_Icc (-1) 1
  apply (hIcc.prod hIcc).subset
  rintro ⟨x, y⟩ hxy
  change x ^ 2 + y ^ 2 < 1 at hxy
  constructor
  · constructor
    · nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
    · nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  · constructor
    · nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
    · nlinarith [sq_nonneg x, sq_nonneg (y - 1)]

theorem openUnitDisk_locallyOneSided (p : PlanePoint) :
    LocallyOneSided openUnitDisk (0, 0) 1 p := by
  refine ⟨.inside, Set.univ, isOpen_univ, mem_univ p, ?_⟩
  ext q
  change
    (q.1 ^ 2 + q.2 ^ 2 < 1 ∧ q ∈ Set.univ) ↔
      (q ∈ Set.univ ∧
        CircleSide.inside.sign * circleValue (0, 0) 1 q < 0)
  simp only [mem_univ, and_true, true_and, CircleSide.sign, one_mul]
  unfold circleValue
  norm_num

/-- The complete zero-height section frontier of the independent disk is
derived from the planar frontier and two local transverse circle crossings. -/
theorem frontier_horizontalSection_openUnitDisk_zero :
    frontier
        (CMVSourceClassification.horizontalSection openUnitDisk 0) =
      {(-1 : ℝ), 1} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hp :=
      CMVSourceClassification.frontier_horizontalSection_subset
        openUnitDisk 0 hx
    have hpCircle : x ^ 2 = (1 : ℝ) ^ 2 := by
      have hzero :=
        frontier_lt_subset_eq
          (show Continuous (fun q : PlanePoint => q.1 ^ 2 + q.2 ^ 2) by
            fun_prop)
          continuous_const hp
      change x ^ 2 + 0 ^ 2 = 1 at hzero
      norm_num at hzero ⊢
      exact hzero
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hpCircle with hpos | hneg
    · exact Or.inr hpos
    · exact Or.inl hneg
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact circlePoint_mem_frontier_horizontalSection_of_localOneSided
        (by norm_num [circleValue])
        (by norm_num)
        (openUnitDisk_locallyOneSided (-1, 0))
    · subst x
      exact circlePoint_mem_frontier_horizontalSection_of_localOneSided
        (by norm_num [circleValue])
        (by norm_num)
        (openUnitDisk_locallyOneSided (1, 0))

/-- The general bounded-open two-crossing theorem reconstructs the independent
disk section; no interval-section identity is an input. -/
theorem horizontalSection_openUnitDisk_zero :
    CMVSourceClassification.horizontalSection openUnitDisk 0 =
      Ioo (-1 : ℝ) 1 := by
  exact CMVSourceClassification.IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    (CMVSourceClassification.isOpen_horizontalSection
      isOpen_openUnitDisk 0)
    (CMVSourceClassification.isBounded_horizontalSection
      isBounded_openUnitDisk 0)
    (by norm_num)
    frontier_horizontalSection_openUnitDisk_zero

end FiniteCrossingExample

/-- A horizontal line is transverse to a circle away from its two horizontal
tangent heights. -/
theorem circle_horizontal_transverse_of_height_ne_extrema
    {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (hlower : p.2 ≠ center.2 - radius)
    (hupper : p.2 ≠ center.2 + radius) :
    p.1 ≠ center.1 := by
  intro hx
  have hsq : (p.2 - center.2) ^ 2 = radius ^ 2 := by
    unfold circleValue at hcircle
    rw [hx] at hcircle
    norm_num at hcircle ⊢
    linarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hpos | hneg
  · apply hupper
    linarith
  · apply hlower
    linarith

/-- Two ordered actual boundary points determine the endpoints of a generic
open interval section.  The target endpoints are conclusions, not inputs. -/
theorem openInterval_endpoints_of_ordered_frontier
    {U : Set PlanePoint} {y left right xLeft xRight : ℝ}
    (hleft_le_right : left ≤ right)
    (hsection :
      CMVSourceClassification.horizontalSection U y = Ioo left right)
    (hxLeft : xLeft ∈ frontier
      (CMVSourceClassification.horizontalSection U y))
    (hxRight : xRight ∈ frontier
      (CMVSourceClassification.horizontalSection U y))
    (horder : xLeft < xRight) :
    left = xLeft ∧ right = xRight := by
  have hleft_lt_right : left < right := by
    rcases hleft_le_right.eq_or_lt with hEq | hlt
    · rw [hsection, ← hEq] at hxLeft
      simp at hxLeft
    · exact hlt
  rw [hsection, frontier_Ioo hleft_lt_right] at hxLeft hxRight
  simp only [mem_insert_iff, mem_singleton_iff] at hxLeft hxRight
  rcases hxLeft with hxLeft | hxLeft <;>
    rcases hxRight with hxRight | hxRight
  · linarith
  · exact ⟨hxLeft.symm, hxRight.symm⟩
  · linarith
  · linarith

/-- Source representative data before Figure-4 normalization.  The
representative contract contains only bounded openness and almost-everywhere
agreement with the source carrier; all section geometry is derived later. -/
structure SourceRepresentative (sourceCarrier representative : Set PlanePoint) : Prop where
  representative_open : IsOpen representative
  representative_bounded : Bornology.IsBounded representative
  source_ae_representative : sourceCarrier =ᵐ[volume] representative

/-- Frozen primitive Figure-4 geometry on an actual source representative.

`upperLeft`, `lowerLeft`, `upperRight`, and `lowerRight` are the actual four
Snell junctions.  Membership in the four literal circle traces records circle
incidence and branch selection.  Local one-sidedness is required away from
those junctions, but no global smoothness is imposed. -/
structure SourceGeometry (lam : ℝ) where
  sourceCarrier : Set PlanePoint
  representative : Set PlanePoint
  sourceRepresentative : SourceRepresentative sourceCarrier representative
  sourceRadius : ℝ
  symmetryAxisX : ℝ
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
  upperLeft_strictly_left_of_axis : upperLeft.1 < symmetryAxisX
  lowerLeft_strictly_left_of_axis : lowerLeft.1 < symmetryAxisX
  upper_center_on_axis : upperCenter.1 = symmetryAxisX
  lower_center_on_axis : lowerCenter.1 = symmetryAxisX
  right_center_reflection :
    rightStripCenter = verticalReflection symmetryAxisX leftStripCenter
  upperRight_reflection : upperRight = verticalReflection symmetryAxisX upperLeft
  lowerRight_reflection : lowerRight = verticalReflection symmetryAxisX lowerLeft
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
  upper_signed_snell :
    (1 - leftStripCenter.2) / sourceRadius =
      lam * ((1 - upperCenter.2) / sourceRadius)
  lower_signed_snell :
    (1 + leftStripCenter.2) / sourceRadius =
      lam * ((1 + lowerCenter.2) / sourceRadius)
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

namespace SourceGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- Signed strip component at the upper-left junction.  Negative values remain
permitted before the scalar rigidity theorem is applied. -/
def upperStripComponent : ℝ :=
  (1 - g.leftStripCenter.2) / g.sourceRadius

/-- Signed strip component at the lower-left junction. -/
def lowerStripComponent : ℝ :=
  (1 + g.leftStripCenter.2) / g.sourceRadius

/-- Signed upper exterior component. -/
def upperExteriorComponent : ℝ :=
  (1 - g.upperCenter.2) / g.sourceRadius

/-- Signed lower exterior component. -/
def lowerExteriorComponent : ℝ :=
  (1 + g.lowerCenter.2) / g.sourceRadius

/-- Heights where a horizontal line can meet a density interface or be tangent
to one of the four supporting circles.  This finite set is the only exception
policy used by the later section reconstruction.  It does not remove the
parameter branch `sourceRadius = 1`. -/
def exceptionalHeights : Finset ℝ :=
  {-1, 1,
    g.upperCenter.2 - g.sourceRadius, g.upperCenter.2 + g.sourceRadius,
    g.lowerCenter.2 - g.sourceRadius, g.lowerCenter.2 + g.sourceRadius,
    g.leftStripCenter.2 - g.sourceRadius,
    g.leftStripCenter.2 + g.sourceRadius,
    g.rightStripCenter.2 - g.sourceRadius,
    g.rightStripCenter.2 + g.sourceRadius}

/-- The frozen exceptional-height policy is null. -/
theorem measure_exceptionalHeights :
    (volume : Measure ℝ) (g.exceptionalHeights : Set ℝ) = 0 := by
  exact g.exceptionalHeights.finite_toSet.measure_zero volume

/-- The actual source set is null measurable because it agrees almost
everywhere with the open representative. -/
theorem sourceCarrier_nullMeasurableSet :
    NullMeasurableSet g.sourceCarrier volume :=
  g.sourceRepresentative.representative_open.measurableSet.nullMeasurableSet.congr
    g.sourceRepresentative.source_ae_representative.symm

/-- The signed Snell laws are exposed in exactly the scalar convention used by
`figure4_scalar_reduction`; neither side has yet been proved positive. -/
theorem signed_snell_components :
    g.upperStripComponent = lam * g.upperExteriorComponent ∧
      g.lowerStripComponent = lam * g.lowerExteriorComponent := by
  exact ⟨g.upper_signed_snell, g.lower_signed_snell⟩

/-- The local one-sided source model is applied to every nonexceptional point
of the actual upper exterior circle, producing a boundary point of the actual
horizontal section. -/
theorem upperTrace_abscissa_mem_frontier_horizontalSection
    {p : PlanePoint}
    (hp : p ∈ exteriorCircleTrace .upper g.upperCenter g.sourceRadius)
    (hy : p.2 ∉ g.exceptionalHeights) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection g.representative p.2) := by
  have hpNeLeft : p ≠ g.upperLeft := by
    intro hpEq
    apply hy
    rw [hpEq, g.upperLeft_height]
    simp [exceptionalHeights]
  have hpNeRight : p ≠ g.upperRight := by
    intro hpEq
    apply hy
    rw [hpEq, g.upperRight_height]
    simp [exceptionalHeights]
  have hLower : p.2 ≠ g.upperCenter.2 - g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  have hUpper : p.2 ≠ g.upperCenter.2 + g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  apply circlePoint_mem_frontier_horizontalSection_of_localOneSided hp.1
    (circle_horizontal_transverse_of_height_ne_extrema hp.1 hLower hUpper)
  exact g.upper_one_sided p hp hpNeLeft hpNeRight

/-- Source-circle application for the actual lower exterior piece. -/
theorem lowerTrace_abscissa_mem_frontier_horizontalSection
    {p : PlanePoint}
    (hp : p ∈ exteriorCircleTrace .lower g.lowerCenter g.sourceRadius)
    (hy : p.2 ∉ g.exceptionalHeights) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection g.representative p.2) := by
  have hpNeLeft : p ≠ g.lowerLeft := by
    intro hpEq
    apply hy
    rw [hpEq, g.lowerLeft_height]
    simp [exceptionalHeights]
  have hpNeRight : p ≠ g.lowerRight := by
    intro hpEq
    apply hy
    rw [hpEq, g.lowerRight_height]
    simp [exceptionalHeights]
  have hLower : p.2 ≠ g.lowerCenter.2 - g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  have hUpper : p.2 ≠ g.lowerCenter.2 + g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  apply circlePoint_mem_frontier_horizontalSection_of_localOneSided hp.1
    (circle_horizontal_transverse_of_height_ne_extrema hp.1 hLower hUpper)
  exact g.lower_one_sided p hp hpNeLeft hpNeRight

/-- Source-circle application for the actual left strip-side piece. -/
theorem leftTrace_abscissa_mem_frontier_horizontalSection
    {p : PlanePoint}
    (hp : p ∈ stripCircleTrace .left g.leftStripCenter g.sourceRadius)
    (hy : p.2 ∉ g.exceptionalHeights) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection g.representative p.2) := by
  have hpNeUpper : p ≠ g.upperLeft := by
    intro hpEq
    apply hy
    rw [hpEq, g.upperLeft_height]
    simp [exceptionalHeights]
  have hpNeLower : p ≠ g.lowerLeft := by
    intro hpEq
    apply hy
    rw [hpEq, g.lowerLeft_height]
    simp [exceptionalHeights]
  have hLower : p.2 ≠ g.leftStripCenter.2 - g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  have hUpper : p.2 ≠ g.leftStripCenter.2 + g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  apply circlePoint_mem_frontier_horizontalSection_of_localOneSided hp.1
    (circle_horizontal_transverse_of_height_ne_extrema hp.1 hLower hUpper)
  exact g.left_one_sided p hp hpNeUpper hpNeLower

/-- Source-circle application for the actual right strip-side piece. -/
theorem rightTrace_abscissa_mem_frontier_horizontalSection
    {p : PlanePoint}
    (hp : p ∈ stripCircleTrace .right g.rightStripCenter g.sourceRadius)
    (hy : p.2 ∉ g.exceptionalHeights) :
    p.1 ∈ frontier
      (CMVSourceClassification.horizontalSection g.representative p.2) := by
  have hpNeUpper : p ≠ g.upperRight := by
    intro hpEq
    apply hy
    rw [hpEq, g.upperRight_height]
    simp [exceptionalHeights]
  have hpNeLower : p ≠ g.lowerRight := by
    intro hpEq
    apply hy
    rw [hpEq, g.lowerRight_height]
    simp [exceptionalHeights]
  have hLower : p.2 ≠ g.rightStripCenter.2 - g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  have hUpper : p.2 ≠ g.rightStripCenter.2 + g.sourceRadius := by
    intro hpEq
    apply hy
    rw [hpEq]
    simp [exceptionalHeights]
  apply circlePoint_mem_frontier_horizontalSection_of_localOneSided hp.1
    (circle_horizontal_transverse_of_height_ne_extrema hp.1 hLower hUpper)
  exact g.right_one_sided p hp hpNeUpper hpNeLower

end SourceGeometry

end CMVFigureFour
