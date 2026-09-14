/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchStationarity

/-!
# Exact-area transverse contact variations

This module treats a boundary written in the branch-neutral form `x = g(y)`
across one strip interface.  Coordinate exchange is used only for Euclidean
volume; the strip density is evaluated in the original coordinates.  The two
contact traces share one displaced endpoint, while an internally normalized,
disjoint constant-density patch compensates their exact weighted-area change.

The construction is conditional on a literal local decomposition of an actual
bounded carrier.  It assumes no Snell law, curvature equation, stationarity,
minimality, selected CMV configuration, or perimeter comparison.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval symmDiff

noncomputable section

namespace CMVTransverseContactVariation

open CMVTwoPatchGraphVariation

/-- A horizontal ribbon is a genuine planar set in the original coordinates.
Only its volume calculation is transported through coordinate exchange. -/
def horizontalRegionBetween (f g : ℝ → ℝ) (s : Set ℝ) : Set PlanePoint :=
  Prod.swap ⁻¹' regionBetween f g s

@[simp] theorem mem_horizontalRegionBetween
    {f g : ℝ → ℝ} {s : Set ℝ} {p : PlanePoint} :
    p ∈ horizontalRegionBetween f g s ↔
      p.2 ∈ s ∧ p.1 ∈ Ioo (f p.2) (g p.2) :=
  Iff.rfl

lemma measurableSet_horizontalRegionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (horizontalRegionBetween f g s) :=
  (measurableSet_regionBetween hf hg hs).preimage measurable_swap

/-- Coordinate swap preserves Euclidean volume.  This lemma deliberately says
nothing about `StripDensity`, which is not coordinate-swap invariant. -/
theorem volume_horizontalRegionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume (horizontalRegionBetween f g s) =
      ∫⁻ y in s, ENNReal.ofReal ((g - f) y) := by
  rw [horizontalRegionBetween, Measure.volume_eq_prod ℝ ℝ]
  rw [Measure.measurePreserving_swap.measure_preimage
    (measurableSet_regionBetween hf hg hs).nullMeasurableSet]
  exact volume_regionBetween_eq_lintegral' hf hg hs

/-- A bounded graph ribbon with the second coordinate as parameter.  The
existing `OccupiedSide.below` label means occupied to the left after swapping
coordinates; `above` means occupied to the right.  Density localization is
stated for the literal unswapped planar carrier. -/
structure HorizontalGraphPatch where
  a : ℝ
  b : ℝ
  base : ℝ
  graph : ℝ → ℝ
  lowerBound : ℝ
  upperBound : ℝ
  zone : DensityZone
  side : OccupiedSide
  a_lt_b : a < b
  graph_contDiff : ContDiff ℝ 2 graph
  base_order_graph : ∀ y ∈ Ioo a b,
    match side with
    | .below => base < graph y
    | .above => graph y < base
  lowerBound_le_base : lowerBound ≤ base
  base_le_upperBound : base ≤ upperBound
  graph_bounds : ∀ y ∈ Ioo a b,
    lowerBound ≤ graph y ∧ graph y ≤ upperBound
  carrier_in_zone : ∀ p ∈
    match side with
    | .below => horizontalRegionBetween (fun _ : ℝ => base) graph (Ioo a b)
    | .above => horizontalRegionBetween graph (fun _ : ℝ => base) (Ioo a b),
    zone.Contains p

namespace HorizontalGraphPatch

/-- Literal occupied horizontal ribbon. -/
def carrier (P : HorizontalGraphPatch) : Set PlanePoint :=
  match P.side with
  | .below => horizontalRegionBetween (fun _ : ℝ => P.base) P.graph (Ioo P.a P.b)
  | .above => horizontalRegionBetween P.graph (fun _ : ℝ => P.base) (Ioo P.a P.b)

/-- Horizontal displacement of the graph `x = graph y`. -/
def variedGraph (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t y : ℝ) : ℝ :=
  P.graph y + t * v y

/-- Literal occupied ribbon after horizontal graph displacement. -/
def variedCarrier (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t : ℝ) : Set PlanePoint :=
  match P.side with
  | .below =>
      horizontalRegionBetween (fun _ : ℝ => P.base) (P.variedGraph v t) (Ioo P.a P.b)
  | .above =>
      horizontalRegionBetween (P.variedGraph v t) (fun _ : ℝ => P.base) (Ioo P.a P.b)

/-- Nonnegative horizontal thickness with the occupied-side sign included. -/
def horizontalThickness (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t y : ℝ) : ℝ :=
  P.side.areaSign * (P.variedGraph v t y - P.base)

@[simp] theorem variedGraph_zero (P : HorizontalGraphPatch) (v : ℝ → ℝ) :
    P.variedGraph v 0 = P.graph := by
  funext y
  simp [variedGraph]

@[simp] theorem variedCarrier_zero (P : HorizontalGraphPatch) (v : ℝ → ℝ) :
    P.variedCarrier v 0 = P.carrier := by
  cases P.side <;> simp [variedCarrier, carrier]

lemma measurableSet_carrier (P : HorizontalGraphPatch) : MeasurableSet P.carrier := by
  cases hside : P.side with
  | below =>
      simpa only [carrier, hside] using
        (measurableSet_horizontalRegionBetween measurable_const
          P.graph_contDiff.continuous.measurable measurableSet_Ioo)
  | above =>
      simpa only [carrier, hside] using
        (measurableSet_horizontalRegionBetween
          P.graph_contDiff.continuous.measurable measurable_const measurableSet_Ioo)

lemma measurableSet_variedCarrier (P : HorizontalGraphPatch) {v : ℝ → ℝ}
    (hv : Measurable v) (t : ℝ) : MeasurableSet (P.variedCarrier v t) := by
  have hgraph : Measurable (P.variedGraph v t) :=
    P.graph_contDiff.continuous.measurable.add (measurable_const.mul hv)
  cases hside : P.side with
  | below =>
      simpa only [variedCarrier, hside] using
        (measurableSet_horizontalRegionBetween measurable_const hgraph measurableSet_Ioo)
  | above =>
      simpa only [variedCarrier, hside] using
        (measurableSet_horizontalRegionBetween hgraph measurable_const measurableSet_Ioo)

/-- Validity keeps the varied ribbon ordered, in its original density zone, and
inside one fixed horizontal box. -/
def ValidAt (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t : ℝ) : Prop :=
  (∀ y ∈ Ioo P.a P.b,
    match P.side with
    | .below => P.base < P.variedGraph v t y
    | .above => P.variedGraph v t y < P.base) ∧
  (∀ p ∈ P.variedCarrier v t, P.zone.Contains p) ∧
  (∀ y ∈ Ioo P.a P.b,
    P.lowerBound ≤ P.variedGraph v t y ∧
      P.variedGraph v t y ≤ P.upperBound)

lemma validAt_zero (P : HorizontalGraphPatch) (v : ℝ → ℝ) : P.ValidAt v 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [variedGraph] using P.base_order_graph
  · rw [variedCarrier_zero]
    simpa only [carrier] using P.carrier_in_zone
  · intro y hy
    simpa [variedGraph] using P.graph_bounds y hy

/-- A support tube around a horizontal graph.  The open parameter interval
omits both zero-area endpoints, including the density-interface contact
singleton. -/
structure Tube (P : HorizontalGraphPatch) where
  radius : ℝ
  radius_pos : 0 < radius
  order_clearance : ∀ y ∈ Ioo P.a P.b,
    match P.side with
    | .below => P.base + radius < P.graph y
    | .above => P.graph y + radius < P.base
  graph_lower_clearance : ∀ y ∈ Ioo P.a P.b,
    P.lowerBound ≤ P.graph y - radius
  graph_upper_clearance : ∀ y ∈ Ioo P.a P.b,
    P.graph y + radius ≤ P.upperBound
  tube_in_zone : ∀ y ∈ Ioo P.a P.b, ∀ x : ℝ,
    |x - P.graph y| ≤ radius → P.zone.Contains (x, y)

/-- Open horizontal displacement tube containing every changed point. -/
def graphTube (P : HorizontalGraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.2 ∈ Ioo P.a P.b ∧ |p.1 - P.graph p.2| < T.radius}

/-- Closed-in-the-displacement-coordinate support tube. -/
def closedGraphTube (P : HorizontalGraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.2 ∈ Ioo P.a P.b ∧ |p.1 - P.graph p.2| ≤ T.radius}

lemma graphTube_subset_closedGraphTube (P : HorizontalGraphPatch) (T : P.Tube) :
    P.graphTube T ⊆ P.closedGraphTube T := by
  rintro p ⟨hy, hx⟩
  exact ⟨hy, hx.le⟩

lemma closedGraphTube_in_zone (P : HorizontalGraphPatch) (T : P.Tube) :
    P.closedGraphTube T ⊆ {p | P.zone.Contains p} := by
  rintro p ⟨hy, hx⟩
  exact T.tube_in_zone p.2 hy p.1 hx

lemma validAt_of_pointwise_mul_lt (P : HorizontalGraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hshift : ∀ y ∈ Ioo P.a P.b, |t * v y| < T.radius) :
    P.ValidAt v t := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hclear := T.order_clearance y hy
    have hbounds := abs_lt.mp (hshift y hy)
    cases hside : P.side <;>
      simp only [hside] at hclear ⊢ <;>
      simp only [variedGraph] <;> linarith
  · intro p hp
    cases hside : P.side with
    | below =>
        simp only [variedCarrier, hside, mem_horizontalRegionBetween] at hp
        by_cases hold : p.1 < P.graph p.2
        · apply P.carrier_in_zone
          simpa only [carrier, hside, mem_horizontalRegionBetween] using
            ⟨hp.1, hp.2.1, hold⟩
        · apply T.tube_in_zone p.2 hp.1 p.1
          have hnonneg : 0 ≤ p.1 - P.graph p.2 :=
            sub_nonneg.mpr (le_of_not_gt hold)
          rw [abs_of_nonneg hnonneg]
          have hupper := hp.2.2
          dsimp [variedGraph] at hupper
          have habs := (abs_lt.mp (hshift p.2 hp.1)).2
          linarith
    | above =>
        simp only [variedCarrier, hside, mem_horizontalRegionBetween] at hp
        by_cases hold : P.graph p.2 < p.1
        · apply P.carrier_in_zone
          simpa only [carrier, hside, mem_horizontalRegionBetween] using
            ⟨hp.1, hold, hp.2.2⟩
        · apply T.tube_in_zone p.2 hp.1 p.1
          have hnonpos : p.1 - P.graph p.2 ≤ 0 :=
            sub_nonpos.mpr (le_of_not_gt hold)
          rw [abs_of_nonpos hnonpos]
          have hlower := hp.2.1
          dsimp [variedGraph] at hlower
          have habs := (abs_lt.mp (hshift p.2 hp.1)).1
          linarith
  · intro y hy
    have hbounds := abs_lt.mp (hshift y hy)
    have hlower := T.graph_lower_clearance y hy
    have hupper := T.graph_upper_clearance y hy
    dsimp only [variedGraph]
    constructor <;> linarith

/-- Every changed point lies in the certified horizontal graph tube. -/
lemma variedCarrier_symmDiff_subset_graphTube
    (P : HorizontalGraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hshift : ∀ y ∈ Ioo P.a P.b, |t * v y| < T.radius) :
    P.variedCarrier v t ∆ P.carrier ⊆ P.graphTube T := by
  intro p hp
  cases hside : P.side with
  | below =>
      simp only [Set.mem_symmDiff, variedCarrier, carrier, hside,
        mem_horizontalRegionBetween] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨⟨hy, hbase, hnew⟩, hold⟩
        refine ⟨hy, ?_⟩
        have hnotold : ¬ p.1 < P.graph p.2 := fun h => hold ⟨hy, hbase, h⟩
        have hnonneg : 0 ≤ p.1 - P.graph p.2 :=
          sub_nonneg.mpr (le_of_not_gt hnotold)
        rw [abs_of_nonneg hnonneg]
        dsimp [variedGraph] at hnew
        have hupper := (abs_lt.mp (hshift p.2 hy)).2
        linarith
      · rcases hp with ⟨⟨hy, hbase, hold⟩, hnew⟩
        refine ⟨hy, ?_⟩
        have hnotnew : ¬ p.1 < P.variedGraph v t p.2 :=
          fun h => hnew ⟨hy, hbase, h⟩
        have hneg : p.1 - P.graph p.2 < 0 := sub_neg.mpr hold
        rw [abs_of_neg hneg]
        dsimp [variedGraph] at hnotnew
        have hnewle := le_of_not_gt hnotnew
        have hlower := (abs_lt.mp (hshift p.2 hy)).1
        linarith
  | above =>
      simp only [Set.mem_symmDiff, variedCarrier, carrier, hside,
        mem_horizontalRegionBetween] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨⟨hy, hnew, hbase⟩, hold⟩
        refine ⟨hy, ?_⟩
        have hnotold : ¬ P.graph p.2 < p.1 := fun h => hold ⟨hy, h, hbase⟩
        have hnonpos : p.1 - P.graph p.2 ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hnotold)
        rw [abs_of_nonpos hnonpos]
        dsimp [variedGraph] at hnew
        have hlower := (abs_lt.mp (hshift p.2 hy)).1
        linarith
      · rcases hp with ⟨⟨hy, hold, hbase⟩, hnew⟩
        refine ⟨hy, ?_⟩
        have hnotnew : ¬ P.variedGraph v t p.2 < p.1 :=
          fun h => hnew ⟨hy, h, hbase⟩
        have hpos : 0 < p.1 - P.graph p.2 := sub_pos.mpr hold
        rw [abs_of_pos hpos]
        dsimp [variedGraph] at hnotnew
        have hnewle := le_of_not_gt hnotnew
        have hupper := (abs_lt.mp (hshift p.2 hy)).2
        linarith

lemma variedCarrier_symmDiff_subset_closedGraphTube
    (P : HorizontalGraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hshift : ∀ y ∈ Ioo P.a P.b, |t * v y| < T.radius) :
    P.variedCarrier v t ∆ P.carrier ⊆ P.closedGraphTube T :=
  (P.variedCarrier_symmDiff_subset_graphTube T hshift).trans
    (P.graphTube_subset_closedGraphTube T)

lemma variedCarrier_subset_box (P : HorizontalGraphPatch)
    {v : ℝ → ℝ} {t : ℝ} (hvalid : P.ValidAt v t) :
    P.variedCarrier v t ⊆
      Ioo P.lowerBound P.upperBound ×ˢ Ioo P.a P.b := by
  intro p hp
  cases hside : P.side with
  | below =>
      simp only [variedCarrier, hside, mem_horizontalRegionBetween] at hp
      exact ⟨⟨lt_of_le_of_lt P.lowerBound_le_base hp.2.1,
        lt_of_lt_of_le hp.2.2 (hvalid.2.2 p.2 hp.1).2⟩, hp.1⟩
  | above =>
      simp only [variedCarrier, hside, mem_horizontalRegionBetween] at hp
      exact ⟨⟨lt_of_le_of_lt (hvalid.2.2 p.2 hp.1).1 hp.2.1,
        lt_of_lt_of_le hp.2.2 P.base_le_upperBound⟩, hp.1⟩

lemma volume_variedCarrier_ne_top (P : HorizontalGraphPatch)
    {v : ℝ → ℝ} {t : ℝ} (hvalid : P.ValidAt v t) :
    volume (P.variedCarrier v t) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (P.variedCarrier_subset_box hvalid))
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ioo_lt_top.ne measure_Ioo_lt_top.ne

lemma integrableOn_stripDensity_variedCarrier (P : HorizontalGraphPatch)
    {lam t : ℝ} {v : ℝ → ℝ} (hvalid : P.ValidAt v t) :
    IntegrableOn (StripDensity lam) (P.variedCarrier v t) :=
  stripDensity_integrableOn_of_volume_ne_top lam (P.volume_variedCarrier_ne_top hvalid)

/-- Exact weighted area of a valid horizontal graph ribbon, derived from the
literal planar set. -/
theorem weightedArea_variedCarrier (P : HorizontalGraphPatch)
    {lam t : ℝ} {v : ℝ → ℝ}
    (hv : Continuous v) (hvalid : P.ValidAt v t) :
    WeightedArea lam (P.variedCarrier v t) =
      P.zone.weight lam *
        ∫ y in P.a..P.b, P.horizontalThickness v t y := by
  rw [WeightedArea]
  calc
    (∫ p in P.variedCarrier v t, StripDensity lam p) =
        ∫ _p in P.variedCarrier v t, P.zone.weight lam := by
      apply setIntegral_congr_fun (P.measurableSet_variedCarrier hv.measurable t)
      intro p hp
      exact DensityZone.stripDensity_eq_weight (hvalid.2.1 p hp)
    _ = P.zone.weight lam * volume.real (P.variedCarrier v t) := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = P.zone.weight lam *
        ∫ y in P.a..P.b, P.horizontalThickness v t y := by
      congr 1
      have hgraphMeas : Measurable (P.variedGraph v t) :=
        P.graph_contDiff.continuous.measurable.add
          (measurable_const.mul hv.measurable)
      cases hside : P.side with
      | below =>
          have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo P.a P.b)]
              fun y => P.variedGraph v t y - P.base := by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
            have hord := hvalid.1 y hy
            simp only [hside] at hord
            exact sub_nonneg.mpr hord.le
          have hmeas : AEStronglyMeasurable
              (fun y => P.variedGraph v t y - P.base)
              (volume.restrict (Ioo P.a P.b)) :=
            ((P.graph_contDiff.continuous.add (continuous_const.mul hv)).sub
              continuous_const).aestronglyMeasurable.restrict
          have hintegral :
              ∫ y in Ioo P.a P.b, (P.variedGraph v t y - P.base) =
                (∫⁻ y in Ioo P.a P.b,
                  ENNReal.ofReal (P.variedGraph v t y - P.base)).toReal :=
            integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
          rw [measureReal_def, variedCarrier, hside,
            volume_horizontalRegionBetween measurable_const hgraphMeas measurableSet_Ioo]
          simp only [Pi.sub_apply]
          rw [← hintegral, intervalIntegral.integral_of_le P.a_lt_b.le,
            MeasureTheory.integral_Ioc_eq_integral_Ioo]
          apply setIntegral_congr_fun measurableSet_Ioo
          intro y _hy
          simp [horizontalThickness, hside]
      | above =>
          have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo P.a P.b)]
              fun y => P.base - P.variedGraph v t y := by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
            have hord := hvalid.1 y hy
            simp only [hside] at hord
            exact sub_nonneg.mpr hord.le
          have hmeas : AEStronglyMeasurable
              (fun y => P.base - P.variedGraph v t y)
              (volume.restrict (Ioo P.a P.b)) :=
            (continuous_const.sub
              (P.graph_contDiff.continuous.add
                (continuous_const.mul hv))).aestronglyMeasurable.restrict
          have hintegral :
              ∫ y in Ioo P.a P.b, (P.base - P.variedGraph v t y) =
                (∫⁻ y in Ioo P.a P.b,
                  ENNReal.ofReal (P.base - P.variedGraph v t y)).toReal :=
            integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
          rw [measureReal_def, variedCarrier, hside,
            volume_horizontalRegionBetween hgraphMeas measurable_const measurableSet_Ioo]
          simp only [Pi.sub_apply]
          rw [← hintegral, intervalIntegral.integral_of_le P.a_lt_b.le,
            MeasureTheory.integral_Ioc_eq_integral_Ioo]
          apply setIntegral_congr_fun measurableSet_Ioo
          intro y _hy
          simp only [horizontalThickness, hside, OccupiedSide.areaSign_above]
          ring

/-- The exact oriented horizontal thickness is affine in the variation
parameter. -/
lemma intervalIntegral_horizontalThickness (P : HorizontalGraphPatch)
    {v : ℝ → ℝ} (hv : Continuous v) (t : ℝ) :
    (∫ y in P.a..P.b, P.horizontalThickness v t y) =
      (∫ y in P.a..P.b, P.horizontalThickness v 0 y) +
        t * P.side.areaSign * ∫ y in P.a..P.b, v y := by
  have hbaseCont : Continuous (P.horizontalThickness v 0) := by
    unfold horizontalThickness variedGraph
    exact continuous_const.mul
      ((P.graph_contDiff.continuous.add (continuous_const.mul hv)).sub
        continuous_const)
  have hbase : IntervalIntegrable (P.horizontalThickness v 0)
      volume P.a P.b := hbaseCont.intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun y => (t * P.side.areaSign) * v y) volume P.a P.b :=
    (continuous_const.mul hv).intervalIntegrable _ _
  rw [show (fun y => P.horizontalThickness v t y) =
      fun y => P.horizontalThickness v 0 y +
        (t * P.side.areaSign) * v y by
        funext y
        unfold horizontalThickness variedGraph
        ring,
    intervalIntegral.integral_add hbase hvar,
    intervalIntegral.integral_const_mul]

/-- Canonical normalized bump on a horizontal patch. -/
def compensationKernel (P : HorizontalGraphPatch) :
    ContDiffBump ((P.a + P.b) / 2) where
  rIn := (P.b - P.a) / 8
  rOut := (P.b - P.a) / 4
  rIn_pos := by linarith [P.a_lt_b]
  rIn_lt_rOut := by linarith [P.a_lt_b]

/-- Smooth nonnegative compensation bump with whole-line integral one. -/
def compensationBump (P : HorizontalGraphPatch) : ℝ → ℝ :=
  P.compensationKernel.normed volume

lemma compensationBump_contDiff (P : HorizontalGraphPatch) :
    ContDiff ℝ ∞ P.compensationBump :=
  P.compensationKernel.contDiff_normed

lemma compensationBump_nonneg (P : HorizontalGraphPatch) (y : ℝ) :
    0 ≤ P.compensationBump y :=
  P.compensationKernel.nonneg_normed y

lemma tsupport_compensationBump_subset (P : HorizontalGraphPatch) :
    tsupport P.compensationBump ⊆ Ioo P.a P.b := by
  rw [compensationBump, P.compensationKernel.tsupport_normed_eq]
  intro y hy
  rw [mem_closedBall, Real.dist_eq, abs_le] at hy
  dsimp [compensationKernel] at hy
  constructor <;> linarith [P.a_lt_b]

lemma support_compensationBump_subset_Ioc (P : HorizontalGraphPatch) :
    support P.compensationBump ⊆ Ioc P.a P.b :=
  (subset_tsupport _).trans <|
    P.tsupport_compensationBump_subset.trans Ioo_subset_Ioc_self

lemma integral_compensationBump (P : HorizontalGraphPatch) :
    ∫ y, P.compensationBump y = 1 :=
  P.compensationKernel.integral_normed

lemma intervalIntegral_compensationBump (P : HorizontalGraphPatch) :
    ∫ y in P.a..P.b, P.compensationBump y = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    P.support_compensationBump_subset_Ioc]
  exact P.integral_compensationBump

end HorizontalGraphPatch


/-! ## A branch-neutral contact pair and its remote compensation -/

/-- Two actual graph neighborhoods meeting at `interfaceY`, plus a remote
constant-density compensation patch.  The two incident graph pieces have one
common occupied side but may lie in different density zones. -/
structure ContactData where
  interfaceY : ℝ
  rho : ℝ
  rho_pos : 0 < rho
  interface_eq : interfaceY = 1 ∨ interfaceY = -1
  minus : HorizontalGraphPatch
  plus : HorizontalGraphPatch
  compensation : HorizontalGraphPatch
  minus_a : minus.a = interfaceY - rho
  minus_b : minus.b = interfaceY
  plus_a : plus.a = interfaceY
  plus_b : plus.b = interfaceY + rho
  common_side : minus.side = plus.side
  different_zones : minus.zone ≠ plus.zone
  graphs_meet : minus.graph interfaceY = plus.graph interfaceY
  compensation_vertical_disjoint :
    Disjoint (Icc compensation.a compensation.b)
      (Icc (interfaceY - rho) (interfaceY + rho))

namespace ContactData

/-- Smooth displacement from an unchanged outer collar to unit displacement
at the contact. -/
def minusVelocity (D : ContactData) (y : ℝ) : ℝ :=
  Real.smoothTransition
    (2 * (y - (D.interfaceY - D.rho / 2)) / D.rho)

/-- Smooth displacement from unit displacement at the contact to an unchanged
outer collar. -/
def plusVelocity (D : ContactData) (y : ℝ) : ℝ :=
  Real.smoothTransition
    (2 * ((D.interfaceY + D.rho / 2) - y) / D.rho)

lemma minusVelocity_contDiff (D : ContactData) :
    ContDiff ℝ 2 D.minusVelocity := by
  unfold minusVelocity
  apply Real.smoothTransition.contDiff.comp
  fun_prop

lemma plusVelocity_contDiff (D : ContactData) :
    ContDiff ℝ 2 D.plusVelocity := by
  unfold plusVelocity
  apply Real.smoothTransition.contDiff.comp
  fun_prop

lemma minusVelocity_nonneg (D : ContactData) (y : ℝ) :
    0 ≤ D.minusVelocity y :=
  Real.smoothTransition.nonneg _

lemma plusVelocity_nonneg (D : ContactData) (y : ℝ) :
    0 ≤ D.plusVelocity y :=
  Real.smoothTransition.nonneg _

lemma minusVelocity_le_one (D : ContactData) (y : ℝ) :
    D.minusVelocity y ≤ 1 :=
  Real.smoothTransition.le_one _

lemma plusVelocity_le_one (D : ContactData) (y : ℝ) :
    D.plusVelocity y ≤ 1 :=
  Real.smoothTransition.le_one _

lemma abs_minusVelocity_le_one (D : ContactData) (y : ℝ) :
    |D.minusVelocity y| ≤ 1 := by
  rw [abs_of_nonneg (D.minusVelocity_nonneg y)]
  exact D.minusVelocity_le_one y

lemma abs_plusVelocity_le_one (D : ContactData) (y : ℝ) :
    |D.plusVelocity y| ≤ 1 := by
  rw [abs_of_nonneg (D.plusVelocity_nonneg y)]
  exact D.plusVelocity_le_one y

@[simp] theorem minusVelocity_contact (D : ContactData) :
    D.minusVelocity D.interfaceY = 1 := by
  have harg :
      2 * (D.interfaceY - (D.interfaceY - D.rho / 2)) / D.rho = 1 := by
    field_simp [ne_of_gt D.rho_pos]
    ring
  rw [minusVelocity, harg, Real.smoothTransition.one]

@[simp] theorem plusVelocity_contact (D : ContactData) :
    D.plusVelocity D.interfaceY = 1 := by
  have harg :
      2 * ((D.interfaceY + D.rho / 2) - D.interfaceY) / D.rho = 1 := by
    field_simp [ne_of_gt D.rho_pos]
    ring
  rw [plusVelocity, harg, Real.smoothTransition.one]

/-- The lower outer half-collar is literally fixed. -/
theorem minusVelocity_eq_zero_of_outer
    (D : ContactData) {y : ℝ}
    (hy : y ≤ D.interfaceY - D.rho / 2) :
    D.minusVelocity y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) D.rho_pos.le

/-- The upper outer half-collar is literally fixed. -/
theorem plusVelocity_eq_zero_of_outer
    (D : ContactData) {y : ℝ}
    (hy : D.interfaceY + D.rho / 2 ≤ y) :
    D.plusVelocity y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) D.rho_pos.le

theorem minus_integral_nonneg (D : ContactData) :
    0 ≤ ∫ y in D.minus.a..D.minus.b, D.minusVelocity y :=
  intervalIntegral.integral_nonneg D.minus.a_lt_b.le
    (fun y _ => D.minusVelocity_nonneg y)

theorem plus_integral_nonneg (D : ContactData) :
    0 ≤ ∫ y in D.plus.a..D.plus.b, D.plusVelocity y :=
  intervalIntegral.integral_nonneg D.plus.a_lt_b.le
    (fun y _ => D.plusVelocity_nonneg y)

/-- Each incident displacement has integral at most the contact support radius.
No exact value of the smooth transition integral is assumed. -/
theorem minus_integral_le_rho (D : ContactData) :
    (∫ y in D.minus.a..D.minus.b, D.minusVelocity y) ≤ D.rho := by
  calc
    (∫ y in D.minus.a..D.minus.b, D.minusVelocity y) ≤
        ∫ _y in D.minus.a..D.minus.b, (1 : ℝ) :=
      intervalIntegral.integral_mono_on D.minus.a_lt_b.le
        (D.minusVelocity_contDiff.continuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
        (fun y _ => D.minusVelocity_le_one y)
    _ = D.minus.b - D.minus.a := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    _ = D.rho := by rw [D.minus_a, D.minus_b]; ring

theorem plus_integral_le_rho (D : ContactData) :
    (∫ y in D.plus.a..D.plus.b, D.plusVelocity y) ≤ D.rho := by
  calc
    (∫ y in D.plus.a..D.plus.b, D.plusVelocity y) ≤
        ∫ _y in D.plus.a..D.plus.b, (1 : ℝ) :=
      intervalIntegral.integral_mono_on D.plus.a_lt_b.le
        (D.plusVelocity_contDiff.continuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
        (fun y _ => D.plusVelocity_le_one y)
    _ = D.plus.b - D.plus.a := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    _ = D.rho := by rw [D.plus_a, D.plus_b]; ring

/-- Exact weighted-area velocity of the two contact ribbons. -/
def contactAreaRate (lam : ℝ) (D : ContactData) : ℝ :=
  D.minus.side.areaSign * D.minus.zone.weight lam *
      (∫ y in D.minus.a..D.minus.b, D.minusVelocity y) +
    D.plus.side.areaSign * D.plus.zone.weight lam *
      (∫ y in D.plus.a..D.plus.b, D.plusVelocity y)

/-- The remote compensation coefficient is computed from the actual two
contact integrals and all three occupied-side and density weights. -/
def compensationCoefficient (lam : ℝ) (D : ContactData) : ℝ :=
  -D.contactAreaRate lam /
    (D.compensation.side.areaSign * D.compensation.zone.weight lam)

/-- Internally generated remote compensation velocity. -/
def compensationVelocity (lam : ℝ) (D : ContactData) (y : ℝ) : ℝ :=
  D.compensationCoefficient lam * D.compensation.compensationBump y

lemma compensationVelocity_contDiff (lam : ℝ) (D : ContactData) :
    ContDiff ℝ 2 (D.compensationVelocity lam) := by
  unfold compensationVelocity
  exact contDiff_const.mul
    (D.compensation.compensationBump_contDiff.of_le (by
      apply WithTop.coe_le_coe.mpr
      exact le_top))

lemma intervalIntegral_compensationVelocity (lam : ℝ) (D : ContactData) :
    ∫ y in D.compensation.a..D.compensation.b,
        D.compensationVelocity lam y =
      D.compensationCoefficient lam := by
  unfold compensationVelocity
  rw [intervalIntegral.integral_const_mul,
    D.compensation.intervalIntegral_compensationBump, mul_one]

/-- The three literal weighted-area velocities cancel exactly. -/
theorem weighted_area_rates_cancel
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) :
    D.contactAreaRate lam +
      D.compensation.side.areaSign * D.compensation.zone.weight lam *
        (∫ y in D.compensation.a..D.compensation.b,
          D.compensationVelocity lam y) = 0 := by
  rw [D.intervalIntegral_compensationVelocity]
  unfold compensationCoefficient
  field_simp [OccupiedSide.areaSign_ne_zero,
    DensityZone.weight_ne_zero hlam]
  ring

@[simp] theorem abs_areaSign (side : OccupiedSide) :
    |side.areaSign| = (1 : ℝ) := by
  cases side <;> norm_num

/-- Fixed coefficient multiplying the shrinking contact-support radius in the
remote compensation estimate. -/
def compensationBound (lam : ℝ) (D : ContactData) : ℝ :=
  (D.minus.zone.weight lam + D.plus.zone.weight lam) /
    D.compensation.zone.weight lam

/-- The internally computed compensation coefficient is `O(rho)`, with an
explicit constant independent of the variation parameter. -/
theorem abs_compensationCoefficient_le
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) :
    |D.compensationCoefficient lam| ≤ D.compensationBound lam * D.rho := by
  let Im : ℝ := ∫ y in D.minus.a..D.minus.b, D.minusVelocity y
  let Ip : ℝ := ∫ y in D.plus.a..D.plus.b, D.plusVelocity y
  have hIm0 : 0 ≤ Im := D.minus_integral_nonneg
  have hIp0 : 0 ≤ Ip := D.plus_integral_nonneg
  have hIm : Im ≤ D.rho := D.minus_integral_le_rho
  have hIp : Ip ≤ D.rho := D.plus_integral_le_rho
  have hwm := DensityZone.weight_pos
    (zone := D.minus.zone) hlam
  have hwp := DensityZone.weight_pos
    (zone := D.plus.zone) hlam
  have hwc := DensityZone.weight_pos
    (zone := D.compensation.zone) hlam
  have hnum :
      |D.minus.side.areaSign * D.minus.zone.weight lam * Im +
          D.plus.side.areaSign * D.plus.zone.weight lam * Ip| ≤
        (D.minus.zone.weight lam + D.plus.zone.weight lam) * D.rho := by
    calc
      |D.minus.side.areaSign * D.minus.zone.weight lam * Im +
          D.plus.side.areaSign * D.plus.zone.weight lam * Ip| ≤
          |D.minus.side.areaSign * D.minus.zone.weight lam * Im| +
            |D.plus.side.areaSign * D.plus.zone.weight lam * Ip| :=
        abs_add_le _ _
      _ = D.minus.zone.weight lam * Im +
          D.plus.zone.weight lam * Ip := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_areaSign, abs_areaSign, abs_of_pos hwm, abs_of_pos hwp,
          abs_of_nonneg hIm0, abs_of_nonneg hIp0]
        ring
      _ ≤ (D.minus.zone.weight lam + D.plus.zone.weight lam) * D.rho := by
        nlinarith
  calc
    |D.compensationCoefficient lam| =
        |D.contactAreaRate lam| / D.compensation.zone.weight lam := by
      unfold compensationCoefficient
      rw [abs_div, abs_neg, abs_mul, abs_areaSign, abs_of_pos hwc, one_mul]
    _ ≤ ((D.minus.zone.weight lam + D.plus.zone.weight lam) * D.rho) /
        D.compensation.zone.weight lam := by
      exact (div_le_div_iff_of_pos_right hwc).2 <| by
        simpa only [contactAreaRate, Im, Ip] using hnum
    _ = D.compensationBound lam * D.rho := by
      unfold compensationBound
      field_simp [ne_of_gt hwc]

/-- Because the two incident zones are distinct, the coefficient has the
branch-neutral fixed bound `(lam + 1) * rho`, whether the contact is at the
upper or lower interface and whichever density zone contains the remote patch. -/
theorem abs_compensationCoefficient_le_lam_add_one_mul_rho
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) :
    |D.compensationCoefficient lam| ≤ (lam + 1) * D.rho := by
  have hbound : D.compensationBound lam ≤ lam + 1 := by
    have hzones := D.different_zones
    cases hm : D.minus.zone <;>
      cases hp : D.plus.zone <;>
      cases hc : D.compensation.zone <;>
      simp [compensationBound, DensityZone.weight, hm, hp, hc] at hzones ⊢
    all_goals try linarith
    all_goals
      have hdiv := div_le_self (a := 1 + lam) (b := lam)
        (by linarith) (le_of_lt hlam)
      simpa [add_comm] using hdiv
  exact (D.abs_compensationCoefficient_le hlam).trans <|
    mul_le_mul_of_nonneg_right hbound D.rho_pos.le

/-- Both incident traces have exactly the same displaced contact point. -/
theorem variedGraphs_meet (D : ContactData) (t : ℝ) :
    D.minus.variedGraph D.minusVelocity t D.interfaceY =
      D.plus.variedGraph D.plusVelocity t D.interfaceY := by
  simp [HorizontalGraphPatch.variedGraph, D.graphs_meet]

/-- The minus trace is unchanged on its complete outer half-collar. -/
theorem minus_variedGraph_eq_on_outer
    (D : ContactData) (t : ℝ) {y : ℝ}
    (hy : y ≤ D.interfaceY - D.rho / 2) :
    D.minus.variedGraph D.minusVelocity t y = D.minus.graph y := by
  rw [HorizontalGraphPatch.variedGraph,
    D.minusVelocity_eq_zero_of_outer hy, mul_zero, add_zero]

/-- The plus trace is unchanged on its complete outer half-collar. -/
theorem plus_variedGraph_eq_on_outer
    (D : ContactData) (t : ℝ) {y : ℝ}
    (hy : D.interfaceY + D.rho / 2 ≤ y) :
    D.plus.variedGraph D.plusVelocity t y = D.plus.graph y := by
  rw [HorizontalGraphPatch.variedGraph,
    D.plusVelocity_eq_zero_of_outer hy, mul_zero, add_zero]

end ContactData


namespace HorizontalGraphPatch

lemma variedCarrier_snd_mem
    (P : HorizontalGraphPatch) {v : ℝ → ℝ} {t : ℝ} {p : PlanePoint}
    (hp : p ∈ P.variedCarrier v t) :
    p.2 ∈ Ioo P.a P.b := by
  cases hside : P.side <;>
    simp only [variedCarrier, hside, mem_horizontalRegionBetween] at hp <;>
    exact hp.1

end HorizontalGraphPatch

namespace ContactData

/-- The two incident ribbons with their common contact displacement. -/
def contactCarrier (D : ContactData) (t : ℝ) : Set PlanePoint :=
  D.minus.variedCarrier D.minusVelocity t ∪
    D.plus.variedCarrier D.plusVelocity t

/-- Complete moving local carrier: two contact ribbons plus the remote
compensation ribbon. -/
def variedRibbons (D : ContactData) (lam t : ℝ) : Set PlanePoint :=
  D.contactCarrier t ∪
    D.compensation.variedCarrier (D.compensationVelocity lam) t

/-- The original three ribbons before displacement. -/
def baselineRibbons (D : ContactData) : Set PlanePoint :=
  D.minus.carrier ∪ D.plus.carrier ∪ D.compensation.carrier

@[simp] theorem contactCarrier_zero (D : ContactData) :
    D.contactCarrier 0 = D.minus.carrier ∪ D.plus.carrier := by
  simp [contactCarrier]

@[simp] theorem variedRibbons_zero (D : ContactData) (lam : ℝ) :
    D.variedRibbons lam 0 = D.baselineRibbons := by
  simp [variedRibbons, baselineRibbons, contactCarrier]

lemma minus_plus_varied_disjoint
    (D : ContactData) (t : ℝ) :
    Disjoint
      (D.minus.variedCarrier D.minusVelocity t)
      (D.plus.variedCarrier D.plusVelocity t) := by
  rw [Set.disjoint_left]
  intro p hpMinus hpPlus
  have hyMinus := D.minus.variedCarrier_snd_mem hpMinus
  have hyPlus := D.plus.variedCarrier_snd_mem hpPlus
  rw [D.minus_a, D.minus_b] at hyMinus
  rw [D.plus_a, D.plus_b] at hyPlus
  linarith [hyMinus.2, hyPlus.1]

lemma contact_compensation_varied_disjoint
    (D : ContactData) (lam t : ℝ) :
    Disjoint
      (D.contactCarrier t)
      (D.compensation.variedCarrier (D.compensationVelocity lam) t) := by
  rw [Set.disjoint_left]
  intro p hpContact hpCompensation
  have hyComp := D.compensation.variedCarrier_snd_mem hpCompensation
  have hyCompClosed : p.2 ∈ Icc D.compensation.a D.compensation.b :=
    ⟨hyComp.1.le, hyComp.2.le⟩
  have hyContact :
      p.2 ∈ Icc (D.interfaceY - D.rho) (D.interfaceY + D.rho) := by
    rcases hpContact with hpMinus | hpPlus
    · have hy := D.minus.variedCarrier_snd_mem hpMinus
      rw [D.minus_a, D.minus_b] at hy
      exact ⟨hy.1.le, (hy.2.trans (by linarith [D.rho_pos])).le⟩
    · have hy := D.plus.variedCarrier_snd_mem hpPlus
      rw [D.plus_a, D.plus_b] at hy
      exact ⟨(by linarith [hy.1, D.rho_pos]), hy.2.le⟩
  exact Set.disjoint_left.1 D.compensation_vertical_disjoint
    hyCompClosed hyContact

lemma measurableSet_contactCarrier (D : ContactData) (t : ℝ) :
    MeasurableSet (D.contactCarrier t) :=
  (D.minus.measurableSet_variedCarrier
    D.minusVelocity_contDiff.continuous.measurable t).union
  (D.plus.measurableSet_variedCarrier
    D.plusVelocity_contDiff.continuous.measurable t)

lemma measurableSet_variedRibbons (D : ContactData) (lam t : ℝ) :
    MeasurableSet (D.variedRibbons lam t) :=
  (D.measurableSet_contactCarrier t).union
    (D.compensation.measurableSet_variedCarrier
      (D.compensationVelocity_contDiff lam).continuous.measurable t)

/-- Additivity of literal weighted area for the three disjoint moving
ribbons. -/
theorem weightedArea_variedRibbons
    (D : ContactData) (lam t : ℝ)
    (hminus : D.minus.ValidAt D.minusVelocity t)
    (hplus : D.plus.ValidAt D.plusVelocity t)
    (hcompensation :
      D.compensation.ValidAt (D.compensationVelocity lam) t) :
    WeightedArea lam (D.variedRibbons lam t) =
      WeightedArea lam (D.minus.variedCarrier D.minusVelocity t) +
        WeightedArea lam (D.plus.variedCarrier D.plusVelocity t) +
          WeightedArea lam
            (D.compensation.variedCarrier (D.compensationVelocity lam) t) := by
  have hiMinus :
      IntegrableOn (StripDensity lam)
        (D.minus.variedCarrier D.minusVelocity t) :=
    D.minus.integrableOn_stripDensity_variedCarrier (lam := lam) hminus
  have hiPlus :
      IntegrableOn (StripDensity lam)
        (D.plus.variedCarrier D.plusVelocity t) :=
    D.plus.integrableOn_stripDensity_variedCarrier (lam := lam) hplus
  have hiContact := hiMinus.union hiPlus
  have hiComp :
      IntegrableOn (StripDensity lam)
        (D.compensation.variedCarrier (D.compensationVelocity lam) t) :=
    D.compensation.integrableOn_stripDensity_variedCarrier
      (lam := lam) hcompensation
  unfold WeightedArea
  rw [variedRibbons,
    setIntegral_union₀
      (D.contact_compensation_varied_disjoint lam t).aedisjoint
      (D.compensation.measurableSet_variedCarrier
        (D.compensationVelocity_contDiff lam).continuous.measurable t
      ).nullMeasurableSet hiContact hiComp]
  rw [contactCarrier,
    setIntegral_union₀
      (D.minus_plus_varied_disjoint t).aedisjoint
      (D.plus.measurableSet_variedCarrier
        D.plusVelocity_contDiff.continuous.measurable t
      ).nullMeasurableSet hiMinus hiPlus]

/-- Exact preservation of literal planar weighted area for all valid positive
or negative parameters. -/
theorem weightedArea_variedRibbons_eq
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) {t : ℝ}
    (hminus : D.minus.ValidAt D.minusVelocity t)
    (hplus : D.plus.ValidAt D.plusVelocity t)
    (hcompensation :
      D.compensation.ValidAt (D.compensationVelocity lam) t) :
    WeightedArea lam (D.variedRibbons lam t) =
      WeightedArea lam D.baselineRibbons := by
  have hminus0 := D.minus.validAt_zero D.minusVelocity
  have hplus0 := D.plus.validAt_zero D.plusVelocity
  have hcomp0 :=
    D.compensation.validAt_zero (D.compensationVelocity lam)
  calc
    WeightedArea lam (D.variedRibbons lam t) =
        D.minus.zone.weight lam *
            (∫ y in D.minus.a..D.minus.b,
              D.minus.horizontalThickness D.minusVelocity t y) +
          D.plus.zone.weight lam *
            (∫ y in D.plus.a..D.plus.b,
              D.plus.horizontalThickness D.plusVelocity t y) +
          D.compensation.zone.weight lam *
            (∫ y in D.compensation.a..D.compensation.b,
              D.compensation.horizontalThickness
                (D.compensationVelocity lam) t y) := by
      rw [D.weightedArea_variedRibbons lam t hminus hplus hcompensation,
        D.minus.weightedArea_variedCarrier
          D.minusVelocity_contDiff.continuous hminus,
        D.plus.weightedArea_variedCarrier
          D.plusVelocity_contDiff.continuous hplus,
        D.compensation.weightedArea_variedCarrier
          (D.compensationVelocity_contDiff lam).continuous hcompensation]
    _ =
        D.minus.zone.weight lam *
            (∫ y in D.minus.a..D.minus.b,
              D.minus.horizontalThickness D.minusVelocity 0 y) +
          D.plus.zone.weight lam *
            (∫ y in D.plus.a..D.plus.b,
              D.plus.horizontalThickness D.plusVelocity 0 y) +
          D.compensation.zone.weight lam *
            (∫ y in D.compensation.a..D.compensation.b,
              D.compensation.horizontalThickness
                (D.compensationVelocity lam) 0 y) := by
      rw [D.minus.intervalIntegral_horizontalThickness
          D.minusVelocity_contDiff.continuous t,
        D.plus.intervalIntegral_horizontalThickness
          D.plusVelocity_contDiff.continuous t,
        D.compensation.intervalIntegral_horizontalThickness
          (D.compensationVelocity_contDiff lam).continuous t]
      have hcancel := D.weighted_area_rates_cancel hlam
      unfold contactAreaRate at hcancel
      linear_combination t * hcancel
    _ = WeightedArea lam (D.variedRibbons lam 0) := by
      rw [D.weightedArea_variedRibbons lam 0 hminus0 hplus0 hcomp0,
        D.minus.weightedArea_variedCarrier
          D.minusVelocity_contDiff.continuous hminus0,
        D.plus.weightedArea_variedCarrier
          D.plusVelocity_contDiff.continuous hplus0,
        D.compensation.weightedArea_variedCarrier
          (D.compensationVelocity_contDiff lam).continuous hcomp0]
    _ = WeightedArea lam D.baselineRibbons := by
      rw [D.variedRibbons_zero]

/-- Union of the three displacement support tubes. -/
def supportTubes (D : ContactData)
    (minusTube : D.minus.Tube) (plusTube : D.plus.Tube)
    (compensationTube : D.compensation.Tube) : Set PlanePoint :=
  D.minus.closedGraphTube minusTube ∪
    (D.plus.closedGraphTube plusTube ∪
      D.compensation.closedGraphTube compensationTube)

/-- The three-ribbon replacement changes only inside its certified support
tubes. -/
theorem variedRibbons_symmDiff_subset_supportTubes
    (D : ContactData) (lam : ℝ)
    (minusTube : D.minus.Tube) (plusTube : D.plus.Tube)
    (compensationTube : D.compensation.Tube) {t : ℝ}
    (hminus : ∀ y ∈ Ioo D.minus.a D.minus.b,
      |t * D.minusVelocity y| < minusTube.radius)
    (hplus : ∀ y ∈ Ioo D.plus.a D.plus.b,
      |t * D.plusVelocity y| < plusTube.radius)
    (hcomp : ∀ y ∈ Ioo D.compensation.a D.compensation.b,
      |t * D.compensationVelocity lam y| < compensationTube.radius) :
    D.variedRibbons lam t ∆ D.baselineRibbons ⊆
      D.supportTubes minusTube plusTube compensationTube := by
  rw [← D.variedRibbons_zero lam]
  have hOuter :
      D.variedRibbons lam t ∆ D.variedRibbons lam 0 ⊆
        (D.contactCarrier t ∆ D.contactCarrier 0) ∪
          (D.compensation.variedCarrier (D.compensationVelocity lam) t ∆
            D.compensation.variedCarrier (D.compensationVelocity lam) 0) := by
    unfold variedRibbons
    exact Set.union_symmDiff_union_subset
  have hInner :
      D.contactCarrier t ∆ D.contactCarrier 0 ⊆
        (D.minus.variedCarrier D.minusVelocity t ∆
          D.minus.variedCarrier D.minusVelocity 0) ∪
        (D.plus.variedCarrier D.plusVelocity t ∆
          D.plus.variedCarrier D.plusVelocity 0) := by
    unfold contactCarrier
    exact Set.union_symmDiff_union_subset
  intro p hp
  rcases hOuter hp with hpContact | hpCompensation
  · rcases hInner hpContact with hpMinus | hpPlus
    · exact Or.inl <| D.minus.variedCarrier_symmDiff_subset_closedGraphTube
        minusTube hminus (by simpa using hpMinus)
    · exact Or.inr <| Or.inl <|
        D.plus.variedCarrier_symmDiff_subset_closedGraphTube
          plusTube hplus (by simpa using hpPlus)
  · exact Or.inr <| Or.inr <|
      D.compensation.variedCarrier_symmDiff_subset_closedGraphTube
        compensationTube hcomp (by simpa using hpCompensation)

end ContactData

/-! ## Replacement inside an actual carrier -/

/-- A literal bounded carrier decomposed into two incident horizontal graph
ribbons, one remote compensation ribbon, and an unchanged remainder. -/
structure ActualContactData where
  contact : ContactData
  minusTube : contact.minus.Tube
  plusTube : contact.plus.Tube
  compensationTube : contact.compensation.Tube
  actualCarrier : Set PlanePoint
  fixedCarrier : Set PlanePoint
  actualCarrier_eq_fixed_union :
    actualCarrier = fixedCarrier ∪ contact.baselineRibbons
  measurableSet_actualCarrier : MeasurableSet actualCarrier
  measurableSet_fixedCarrier : MeasurableSet fixedCarrier
  actualCarrier_bounded : Bornology.IsBounded actualCarrier
  fixed_disjoint_baseline :
    Disjoint fixedCarrier contact.baselineRibbons
  fixed_disjoint_supportTubes :
    Disjoint fixedCarrier
      (contact.supportTubes minusTube plusTube compensationTube)

namespace ActualContactData

/-- Replace exactly the three local ribbons and retain the remaining carrier
literally. -/
def variedCarrier (A : ActualContactData) (lam t : ℝ) : Set PlanePoint :=
  A.fixedCarrier ∪ A.contact.variedRibbons lam t

@[simp] theorem variedCarrier_zero (A : ActualContactData) (lam : ℝ) :
    A.variedCarrier lam 0 = A.actualCarrier := by
  rw [variedCarrier, A.contact.variedRibbons_zero]
  exact A.actualCarrier_eq_fixed_union.symm

lemma fixedCarrier_subset_actualCarrier (A : ActualContactData) :
    A.fixedCarrier ⊆ A.actualCarrier := by
  intro p hp
  rw [A.actualCarrier_eq_fixed_union]
  exact Or.inl hp

lemma fixedCarrier_bounded (A : ActualContactData) :
    Bornology.IsBounded A.fixedCarrier :=
  A.actualCarrier_bounded.subset A.fixedCarrier_subset_actualCarrier

lemma integrableOn_fixedCarrier (A : ActualContactData) (lam : ℝ) :
    IntegrableOn (StripDensity lam) A.fixedCarrier :=
  stripDensity_integrableOn_of_volume_ne_top lam
    A.fixedCarrier_bounded.measure_lt_top.ne

lemma fixedCarrier_disjoint_variedRibbons
    (A : ActualContactData) (lam : ℝ) {t : ℝ}
    (hdiff :
      A.contact.variedRibbons lam t ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube) :
    Disjoint A.fixedCarrier (A.contact.variedRibbons lam t) := by
  rw [Set.disjoint_left]
  intro p hpFixed hpVaried
  by_cases hpBaseline : p ∈ A.contact.baselineRibbons
  · exact Set.disjoint_left.1 A.fixed_disjoint_baseline
      hpFixed hpBaseline
  · have hpDiff :
        p ∈ A.contact.variedRibbons lam t ∆
          A.contact.baselineRibbons := by
      simp only [Set.mem_symmDiff]
      exact Or.inl ⟨hpVaried, hpBaseline⟩
    exact Set.disjoint_left.1 A.fixed_disjoint_supportTubes
      hpFixed (hdiff hpDiff)

lemma weightedArea_variedCarrier_eq_add
    (A : ActualContactData) (lam : ℝ) {t : ℝ}
    (hminus : A.contact.minus.ValidAt A.contact.minusVelocity t)
    (hplus : A.contact.plus.ValidAt A.contact.plusVelocity t)
    (hcompensation :
      A.contact.compensation.ValidAt
        (A.contact.compensationVelocity lam) t)
    (hdiff :
      A.contact.variedRibbons lam t ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube) :
    WeightedArea lam (A.variedCarrier lam t) =
      WeightedArea lam A.fixedCarrier +
        WeightedArea lam (A.contact.variedRibbons lam t) := by
  have hRibbons :
      IntegrableOn (StripDensity lam)
        (A.contact.variedRibbons lam t) := by
    exact ((A.contact.minus.integrableOn_stripDensity_variedCarrier hminus).union
      (A.contact.plus.integrableOn_stripDensity_variedCarrier hplus)).union
        (A.contact.compensation.integrableOn_stripDensity_variedCarrier
          hcompensation)
  simpa only [WeightedArea, variedCarrier] using
    setIntegral_union₀
      (A.fixedCarrier_disjoint_variedRibbons lam hdiff).aedisjoint
      (A.contact.measurableSet_variedRibbons lam t).nullMeasurableSet
      (A.integrableOn_fixedCarrier lam) hRibbons

/-- Exact weighted-area preservation for the literal actual carrier. -/
theorem weightedArea_variedCarrier
    {lam : ℝ} (hlam : 1 < lam) (A : ActualContactData) {t : ℝ}
    (hminus : A.contact.minus.ValidAt A.contact.minusVelocity t)
    (hplus : A.contact.plus.ValidAt A.contact.plusVelocity t)
    (hcompensation :
      A.contact.compensation.ValidAt
        (A.contact.compensationVelocity lam) t)
    (hdiff :
      A.contact.variedRibbons lam t ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube) :
    WeightedArea lam (A.variedCarrier lam t) =
      WeightedArea lam A.actualCarrier := by
  have hminus0 :=
    A.contact.minus.validAt_zero A.contact.minusVelocity
  have hplus0 :=
    A.contact.plus.validAt_zero A.contact.plusVelocity
  have hcomp0 := A.contact.compensation.validAt_zero
    (A.contact.compensationVelocity lam)
  have hdiff0 :
      A.contact.variedRibbons lam 0 ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube := by
    simp
  calc
    WeightedArea lam (A.variedCarrier lam t) =
        WeightedArea lam A.fixedCarrier +
          WeightedArea lam (A.contact.variedRibbons lam t) :=
      A.weightedArea_variedCarrier_eq_add lam
        hminus hplus hcompensation hdiff
    _ = WeightedArea lam A.fixedCarrier +
          WeightedArea lam A.contact.baselineRibbons := by
      rw [A.contact.weightedArea_variedRibbons_eq
        hlam hminus hplus hcompensation]
    _ = WeightedArea lam A.fixedCarrier +
          WeightedArea lam (A.contact.variedRibbons lam 0) := by
      rw [A.contact.variedRibbons_zero]
    _ = WeightedArea lam (A.variedCarrier lam 0) :=
      (A.weightedArea_variedCarrier_eq_add lam
        hminus0 hplus0 hcomp0 hdiff0).symm
    _ = WeightedArea lam A.actualCarrier := by
      rw [A.variedCarrier_zero]

/-- Actual-carrier membership is unchanged away from all three moving
neighborhoods. -/
theorem mem_variedCarrier_iff_of_not_mem_supportTubes
    (A : ActualContactData) (lam : ℝ) {t : ℝ}
    (hdiff :
      A.contact.variedRibbons lam t ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube)
    {p : PlanePoint}
    (hp : p ∉ A.contact.supportTubes
      A.minusTube A.plusTube A.compensationTube) :
    p ∈ A.variedCarrier lam t ↔ p ∈ A.actualCarrier := by
  rw [← A.variedCarrier_zero lam]
  have hnot :
      p ∉ A.contact.variedRibbons lam t ∆
        A.contact.variedRibbons lam 0 := by
    intro hmem
    apply hp
    apply hdiff
    simpa using hmem
  simp only [variedCarrier, Set.mem_union, Set.mem_symmDiff,
    not_or, not_and, not_not] at hnot ⊢
  tauto

private theorem exists_uniform_shift
    (v : ℝ → ℝ) {radius M : ℝ}
    (hradius : 0 < radius) (hM : 0 < M)
    (hbound : ∀ y, |v y| ≤ M) :
    ∃ ε > 0, ∀ t, |t| < ε → ∀ y, |t * v y| < radius := by
  refine ⟨radius / M, div_pos hradius hM, ?_⟩
  intro t ht y
  rw [abs_mul]
  have htM : |t| * M < radius := (lt_div_iff₀ hM).mp ht
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hbound y) (abs_nonneg t)) htM

/-- The complete exact-area contact family is valid for one symmetric
neighborhood of zero.  Hence the same statement covers both positive and
negative variation parameters, with the support scale held fixed. -/
theorem transverse_contact_exact_area_checkpoint
    {lam : ℝ} (hlam : 1 < lam) (A : ActualContactData) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      A.contact.minus.ValidAt A.contact.minusVelocity t ∧
      A.contact.plus.ValidAt A.contact.plusVelocity t ∧
      A.contact.compensation.ValidAt
        (A.contact.compensationVelocity lam) t ∧
      WeightedArea lam (A.variedCarrier lam t) =
        WeightedArea lam A.actualCarrier ∧
      A.contact.variedRibbons lam t ∆ A.contact.baselineRibbons ⊆
        A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube ∧
      (∀ p ∉ A.contact.supportTubes
          A.minusTube A.plusTube A.compensationTube,
        (p ∈ A.variedCarrier lam t ↔ p ∈ A.actualCarrier)) ∧
      A.contact.minus.variedGraph A.contact.minusVelocity
          t A.contact.interfaceY =
        A.contact.plus.variedGraph A.contact.plusVelocity
          t A.contact.interfaceY ∧
      (∀ y ≤ A.contact.interfaceY - A.contact.rho / 2,
        A.contact.minus.variedGraph A.contact.minusVelocity t y =
          A.contact.minus.graph y) ∧
      (∀ y, A.contact.interfaceY + A.contact.rho / 2 ≤ y →
        A.contact.plus.variedGraph A.contact.plusVelocity t y =
          A.contact.plus.graph y) ∧
      |A.contact.compensationCoefficient lam| ≤
        (lam + 1) * A.contact.rho := by
  obtain ⟨εm, hεm, hm⟩ := exists_uniform_shift
    A.contact.minusVelocity A.minusTube.radius_pos zero_lt_one
    A.contact.abs_minusVelocity_le_one
  obtain ⟨εp, hεp, hp⟩ := exists_uniform_shift
    A.contact.plusVelocity A.plusTube.radius_pos zero_lt_one
    A.contact.abs_plusVelocity_le_one
  have hcompCompact :
      HasCompactSupport (A.contact.compensationVelocity lam) := by
    unfold ContactData.compensationVelocity
    exact A.contact.compensation.compensationKernel.hasCompactSupport_normed.mul_left
  obtain ⟨M₀, hM₀⟩ :=
    (A.contact.compensationVelocity_contDiff lam).continuous
      |>.bounded_above_of_compact_support hcompCompact
  let M := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMbound : ∀ y, |A.contact.compensationVelocity lam y| ≤ M := by
    intro y
    rw [← Real.norm_eq_abs]
    exact (hM₀ y).trans (le_max_right _ _)
  obtain ⟨εc, hεc, hc⟩ := exists_uniform_shift
    (A.contact.compensationVelocity lam)
    A.compensationTube.radius_pos hM hMbound
  let ε := min εm (min εp εc)
  have hε : 0 < ε := lt_min hεm (lt_min hεp hεc)
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have htm : |t| < εm := ht.trans_le (min_le_left _ _)
  have htp : |t| < εp :=
    ht.trans_le ((min_le_right εm (min εp εc)).trans (min_le_left _ _))
  have htc : |t| < εc :=
    ht.trans_le ((min_le_right εm (min εp εc)).trans (min_le_right _ _))
  have hshiftMinus :
      ∀ y ∈ Ioo A.contact.minus.a A.contact.minus.b,
        |t * A.contact.minusVelocity y| < A.minusTube.radius :=
    fun y _ => hm t htm y
  have hshiftPlus :
      ∀ y ∈ Ioo A.contact.plus.a A.contact.plus.b,
        |t * A.contact.plusVelocity y| < A.plusTube.radius :=
    fun y _ => hp t htp y
  have hshiftComp :
      ∀ y ∈ Ioo A.contact.compensation.a A.contact.compensation.b,
        |t * A.contact.compensationVelocity lam y| <
          A.compensationTube.radius :=
    fun y _ => hc t htc y
  have hvalidMinus :=
    A.contact.minus.validAt_of_pointwise_mul_lt
      A.minusTube hshiftMinus
  have hvalidPlus :=
    A.contact.plus.validAt_of_pointwise_mul_lt
      A.plusTube hshiftPlus
  have hvalidComp :=
    A.contact.compensation.validAt_of_pointwise_mul_lt
      A.compensationTube hshiftComp
  have hdiff :=
    A.contact.variedRibbons_symmDiff_subset_supportTubes lam
      A.minusTube A.plusTube A.compensationTube
      hshiftMinus hshiftPlus hshiftComp
  refine ⟨hvalidMinus, hvalidPlus, hvalidComp,
    A.weightedArea_variedCarrier hlam
      hvalidMinus hvalidPlus hvalidComp hdiff,
    hdiff, ?_, A.contact.variedGraphs_meet t, ?_, ?_,
    A.contact.abs_compensationCoefficient_le_lam_add_one_mul_rho hlam⟩
  · intro p hpOutside
    exact A.mem_variedCarrier_iff_of_not_mem_supportTubes
      lam hdiff hpOutside
  · intro y hy
    exact A.contact.minus_variedGraph_eq_on_outer t hy
  · intro y hy
    exact A.contact.plus_variedGraph_eq_on_outer t hy

end ActualContactData


namespace HorizontalGraphPatch

lemma carrier_bounded (P : HorizontalGraphPatch) :
    Bornology.IsBounded P.carrier := by
  let v : ℝ → ℝ := fun _ => 0
  have hsubset :
      P.variedCarrier v 0 ⊆
        Icc P.lowerBound P.upperBound ×ˢ Icc P.a P.b := by
    intro p hp
    have hbox := P.variedCarrier_subset_box (P.validAt_zero v) hp
    exact ⟨⟨hbox.1.1.le, hbox.1.2.le⟩,
      ⟨hbox.2.1.le, hbox.2.2.le⟩⟩
  rw [P.variedCarrier_zero v] at hsubset
  exact ((Metric.isBounded_Icc P.lowerBound P.upperBound).prod
    (Metric.isBounded_Icc P.a P.b)).subset hsubset

end HorizontalGraphPatch

/-- Tangential momentum of `x = graph(y)` in the common increasing-`y`
orientation. -/
def contactMomentum (P : HorizontalGraphPatch) (y : ℝ) : ℝ :=
  deriv P.graph y / Real.sqrt (1 + (deriv P.graph y) ^ 2)

/-- Signed transmission defect across the density interface, with both graph
traces oriented by increasing `y`. -/
def transmissionDefect (lam : ℝ) (D : ContactData) : ℝ :=
  D.minus.zone.weight lam * contactMomentum D.minus D.interfaceY -
    D.plus.zone.weight lam * contactMomentum D.plus D.interfaceY

/-! ## Independent bounded `lambda = 2` exercise -/

namespace Examples

/-- Interior affine germ approaching the upper interface from below. -/
def minusPatch : HorizontalGraphPatch where
  a := 3 / 4
  b := 1
  base := -2
  graph := fun _ => 0
  lowerBound := -2
  upperBound := 1 / 2
  zone := .interior
  side := .below
  a_lt_b := by norm_num
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := le_rfl
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change |p.2| ≤ 1
    rw [abs_of_nonneg (by linarith [hp.1.1])]
    exact hp.1.2.le

/-- Exterior affine germ leaving the upper interface with nonzero slope. -/
def plusPatch : HorizontalGraphPatch where
  a := 1
  b := 5 / 4
  base := -2
  graph := fun y => y - 1
  lowerBound := -2
  upperBound := 1 / 2
  zone := .exterior
  side := .below
  a_lt_b := by norm_num
  graph_contDiff := by fun_prop
  base_order_graph := by
    intro y hy
    norm_num only
    linarith [hy.1]
  lowerBound_le_base := le_rfl
  base_le_upperBound := by norm_num
  graph_bounds := by
    intro y hy
    rcases hy with ⟨hyLower, hyUpper⟩
    constructor <;> norm_num at hyLower hyUpper ⊢ <;> linarith
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change 1 < |p.2|
    rw [abs_of_pos (by linarith [hp.1.1])]
    exact hp.1.1

/-- Remote density-one compensation patch. -/
def compensationPatch : HorizontalGraphPatch where
  a := -1 / 2
  b := -1 / 4
  base := 1
  graph := fun _ => 2
  lowerBound := 1
  upperBound := 5 / 2
  zone := .interior
  side := .below
  a_lt_b := by norm_num
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := le_rfl
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change |p.2| ≤ 1
    rw [abs_of_nonpos (by linarith [hp.1.2])]
    linarith [hp.1.1]

/-- A literal upper-interface contact with distinct density zones and a
disjoint remote patch. -/
def contact : ContactData where
  interfaceY := 1
  rho := 1 / 4
  rho_pos := by norm_num
  interface_eq := Or.inl rfl
  minus := minusPatch
  plus := plusPatch
  compensation := compensationPatch
  minus_a := by norm_num [minusPatch]
  minus_b := rfl
  plus_a := rfl
  plus_b := by norm_num [plusPatch]
  common_side := rfl
  different_zones := by decide
  graphs_meet := by norm_num [minusPatch, plusPatch]
  compensation_vertical_disjoint := by
    rw [Set.disjoint_left]
    intro y hyComp hyContact
    norm_num [compensationPatch] at hyComp hyContact
    linarith

def minusTube : minusPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [minusPatch]
  graph_lower_clearance := by intros; norm_num [minusPatch]
  graph_upper_clearance := by intros; norm_num [minusPatch]
  tube_in_zone := by
    intro y hy _x _hx
    change |y| ≤ 1
    norm_num [minusPatch] at hy
    rw [abs_of_nonneg (by linarith)]
    exact hy.2.le

def plusTube : plusPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by
    intro y hy
    norm_num [plusPatch] at hy ⊢
    linarith
  graph_lower_clearance := by
    intro y hy
    norm_num [plusPatch] at hy ⊢
    linarith
  graph_upper_clearance := by
    intro y hy
    norm_num [plusPatch] at hy ⊢
    linarith
  tube_in_zone := by
    intro y hy _x _hx
    change 1 < |y|
    norm_num [plusPatch] at hy
    rw [abs_of_pos (by linarith)]
    exact hy.1

def compensationTube : compensationPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [compensationPatch]
  graph_lower_clearance := by intros; norm_num [compensationPatch]
  graph_upper_clearance := by intros; norm_num [compensationPatch]
  tube_in_zone := by
    intro y hy _x _hx
    change |y| ≤ 1
    norm_num [compensationPatch] at hy
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The independently defined carrier is exactly the three bounded literal
graph ribbons; no source admissibility or minimality is asserted. -/
def actual : ActualContactData where
  contact := contact
  minusTube := by simpa [contact] using minusTube
  plusTube := by simpa [contact] using plusTube
  compensationTube := by simpa [contact] using compensationTube
  actualCarrier := contact.baselineRibbons
  fixedCarrier := ∅
  actualCarrier_eq_fixed_union := by simp
  measurableSet_actualCarrier := by
    simpa [ContactData.baselineRibbons, contact] using
      (minusPatch.measurableSet_carrier.union
        plusPatch.measurableSet_carrier).union
          compensationPatch.measurableSet_carrier
  measurableSet_fixedCarrier := MeasurableSet.empty
  actualCarrier_bounded := by
    simpa [ContactData.baselineRibbons, contact] using
      (minusPatch.carrier_bounded.union plusPatch.carrier_bounded).union
        compensationPatch.carrier_bounded
  fixed_disjoint_baseline := Set.empty_disjoint _
  fixed_disjoint_supportTubes := Set.empty_disjoint _

/-- The example is a genuinely bounded actual carrier. -/
theorem actualCarrier_bounded :
    Bornology.IsBounded actual.actualCarrier :=
  actual.actualCarrier_bounded

/-- The two affine slopes violate the `lambda = 2` tangential-momentum law. -/
theorem transmissionDefect_ne_zero :
    transmissionDefect 2 contact ≠ 0 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp [transmissionDefect, contactMomentum, contact, minusPatch, plusPatch,
    DensityZone.weight]

/-- Nonvacuous exact-area family on the independent nonstationary specimen. -/
theorem exact_area_family :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      actual.contact.minus.ValidAt actual.contact.minusVelocity t ∧
      actual.contact.plus.ValidAt actual.contact.plusVelocity t ∧
      actual.contact.compensation.ValidAt
        (actual.contact.compensationVelocity 2) t ∧
      WeightedArea 2 (actual.variedCarrier 2 t) =
        WeightedArea 2 actual.actualCarrier ∧
      actual.contact.variedRibbons 2 t ∆ actual.contact.baselineRibbons ⊆
        actual.contact.supportTubes
          actual.minusTube actual.plusTube actual.compensationTube ∧
      (∀ p ∉ actual.contact.supportTubes
          actual.minusTube actual.plusTube actual.compensationTube,
        (p ∈ actual.variedCarrier 2 t ↔ p ∈ actual.actualCarrier)) ∧
      actual.contact.minus.variedGraph actual.contact.minusVelocity
          t actual.contact.interfaceY =
        actual.contact.plus.variedGraph actual.contact.plusVelocity
          t actual.contact.interfaceY ∧
      (∀ y ≤ actual.contact.interfaceY - actual.contact.rho / 2,
        actual.contact.minus.variedGraph actual.contact.minusVelocity t y =
          actual.contact.minus.graph y) ∧
      (∀ y, actual.contact.interfaceY + actual.contact.rho / 2 ≤ y →
        actual.contact.plus.variedGraph actual.contact.plusVelocity t y =
          actual.contact.plus.graph y) ∧
      |actual.contact.compensationCoefficient 2| ≤
        (2 + 1) * actual.contact.rho :=
  actual.transverse_contact_exact_area_checkpoint (by norm_num)

end Examples

end CMVTransverseContactVariation
