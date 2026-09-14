/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVGeometry
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Two-patch graph variations in the CMV strip density

This module treats two horizontally disjoint graph regions.  The moving
boundary is varied vertically on the first patch and compensated by a
normalized smooth bump constructed on the second patch.  Area is always the
literal planar `WeightedArea`; boundary cost is recorded only as the literal
weighted Euclidean graph-length integral, not as a relaxed perimeter.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval symmDiff

noncomputable section

namespace CMVTwoPatchGraphVariation

/-- The two constant branches of `StripDensity`. -/
inductive DensityZone where
  | interior
  | exterior
  deriving DecidableEq

namespace DensityZone

/-- Constant value of the strip density on a zone. -/
def weight (zone : DensityZone) (lam : ℝ) : ℝ :=
  match zone with
  | .interior => 1
  | .exterior => lam

/-- Pointwise membership in a constant-density branch. -/
def Contains (zone : DensityZone) (p : PlanePoint) : Prop :=
  match zone with
  | .interior => |p.2| ≤ 1
  | .exterior => 1 < |p.2|

lemma stripDensity_eq_weight {zone : DensityZone} {lam : ℝ} {p : PlanePoint}
    (hp : zone.Contains p) : StripDensity lam p = zone.weight lam := by
  cases zone with
  | interior =>
      change |p.2| ≤ 1 at hp
      simp [weight, StripDensity, hp]
  | exterior =>
      change 1 < |p.2| at hp
      simp [weight, StripDensity, not_le.mpr hp]

lemma weight_pos {zone : DensityZone} {lam : ℝ} (hlam : 1 < lam) :
    0 < zone.weight lam := by
  cases zone <;> simp [weight, lt_trans zero_lt_one hlam]

lemma weight_ne_zero {zone : DensityZone} {lam : ℝ} (hlam : 1 < lam) :
    zone.weight lam ≠ 0 := ne_of_gt (weight_pos hlam)

end DensityZone

/-- Which side of a boundary graph is occupied by the carrier. -/
inductive OccupiedSide where
  | below
  | above
  deriving DecidableEq

namespace OccupiedSide

/-- Signed area response to an upward graph displacement. -/
def areaSign : OccupiedSide → ℝ
  | .below => 1
  | .above => -1

@[simp] lemma areaSign_below : OccupiedSide.below.areaSign = (1 : ℝ) := rfl

@[simp] lemma areaSign_above : OccupiedSide.above.areaSign = (-1 : ℝ) := rfl

lemma areaSign_ne_zero (side : OccupiedSide) : side.areaSign ≠ 0 := by
  cases side <;> norm_num

lemma areaSign_mul_self (side : OccupiedSide) :
    side.areaSign * side.areaSign = 1 := by
  cases side <;> norm_num

end OccupiedSide

/-- A bounded oriented graph region over `(a,b]`.  `side` records whether the
actual occupied region lies below or above the moving graph.  Its literal
carrier, rather than an assumed area formula, is required to remain in one
constant-density branch. -/
structure GraphPatch where
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
  base_order_graph : ∀ x ∈ Ioc a b,
    match side with
    | .below => base < graph x
    | .above => graph x < base
  lowerBound_le_base : lowerBound ≤ base
  base_le_upperBound : base ≤ upperBound
  graph_bounds : ∀ x ∈ Ioc a b, lowerBound ≤ graph x ∧ graph x ≤ upperBound
  carrier_in_zone :
    ∀ p ∈ match side with
      | .below => regionBetween (fun _ : ℝ => base) graph (Ioc a b)
      | .above => regionBetween graph (fun _ : ℝ => base) (Ioc a b),
      zone.Contains p

namespace GraphPatch

/-- Literal region on the declared occupied side of the graph. -/
def carrier (P : GraphPatch) : Set PlanePoint :=
  match P.side with
  | .below => regionBetween (fun _ : ℝ => P.base) P.graph (Ioc P.a P.b)
  | .above => regionBetween P.graph (fun _ : ℝ => P.base) (Ioc P.a P.b)

/-- Vertical perturbation of the graph. -/
def variedGraph (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) (x : ℝ) : ℝ :=
  P.graph x + t * v x

/-- Literal planar region associated with a vertical graph perturbation, on
the same occupied side as the original patch. -/
def variedCarrier (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) : Set PlanePoint :=
  match P.side with
  | .below =>
      regionBetween (fun _ : ℝ => P.base) (P.variedGraph v t) (Ioc P.a P.b)
  | .above =>
      regionBetween (P.variedGraph v t) (fun _ : ℝ => P.base) (Ioc P.a P.b)

/-- Nonnegative vertical thickness when the varied graph remains ordered. -/
def verticalThickness (P : GraphPatch) (v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  P.side.areaSign * (P.variedGraph v t x - P.base)

@[simp] lemma variedGraph_zero (P : GraphPatch) (v : ℝ → ℝ) :
    P.variedGraph v 0 = P.graph := by
  funext x
  simp [variedGraph]

@[simp] lemma variedCarrier_zero (P : GraphPatch) (v : ℝ → ℝ) :
    P.variedCarrier v 0 = P.carrier := by
  cases P.side <;> simp [variedCarrier, carrier]

lemma measurableSet_carrier (P : GraphPatch) : MeasurableSet P.carrier := by
  cases hside : P.side with
  | below =>
      simpa only [carrier, hside] using
        (measurableSet_regionBetween measurable_const
          P.graph_contDiff.continuous.measurable measurableSet_Ioc)
  | above =>
      simpa only [carrier, hside] using
        (measurableSet_regionBetween P.graph_contDiff.continuous.measurable
          measurable_const measurableSet_Ioc)

lemma measurableSet_variedCarrier (P : GraphPatch) {v : ℝ → ℝ}
    (hv : Measurable v) (t : ℝ) : MeasurableSet (P.variedCarrier v t) := by
  have hgraph : Measurable (P.variedGraph v t) :=
    P.graph_contDiff.continuous.measurable.add (measurable_const.mul hv)
  cases hside : P.side with
  | below =>
      simpa only [variedCarrier, hside] using
        (measurableSet_regionBetween measurable_const hgraph measurableSet_Ioc)
  | above =>
      simpa only [variedCarrier, hside] using
        (measurableSet_regionBetween hgraph measurable_const measurableSet_Ioc)

/-- Side-dependent ordering of an actual boundary graph and its fixed local
baseline. -/
def OrderedAt (P : GraphPatch) (g : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioc P.a P.b,
    match P.side with
    | .below => P.base < g x
    | .above => g x < P.base

/-- Validity means that the varied region is nondegenerate, stays in the same
constant-density branch, and stays in one fixed finite vertical box. -/
def ValidAt (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) : Prop :=
  P.OrderedAt (P.variedGraph v t) ∧
  (∀ p ∈ P.variedCarrier v t, P.zone.Contains p) ∧
  (∀ x ∈ Ioc P.a P.b,
    P.lowerBound ≤ P.variedGraph v t x ∧
      P.variedGraph v t x ≤ P.upperBound)

lemma validAt_zero (P : GraphPatch) (v : ℝ → ℝ) : P.ValidAt v 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [OrderedAt, variedGraph] using P.base_order_graph
  · rw [variedCarrier_zero]
    simpa only [carrier] using P.carrier_in_zone
  · intro x hx
    simpa [variedGraph] using P.graph_bounds x hx

/-- A geometric tube whose closed vertical fibers stay in one constant-density
branch.  The closed containment makes density locality stable under every
strictly smaller displacement. -/
structure Tube (P : GraphPatch) where
  radius : ℝ
  radius_pos : 0 < radius
  order_clearance : ∀ x ∈ Ioc P.a P.b,
    match P.side with
    | .below => P.base + radius < P.graph x
    | .above => P.graph x + radius < P.base
  graph_lower_clearance :
    ∀ x ∈ Ioc P.a P.b, P.lowerBound ≤ P.graph x - radius
  graph_upper_clearance :
    ∀ x ∈ Ioc P.a P.b, P.graph x + radius ≤ P.upperBound
  closed_tube_in_zone : ∀ x ∈ Icc P.a P.b, ∀ y : ℝ,
    |y - P.graph x| ≤ radius → P.zone.Contains (x, y)

/-- The half-open localization tube used by the graph-region representation. -/
def graphTube (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.1 ∈ Ioc P.a P.b ∧ |p.2 - P.graph p.1| < T.radius}

/-- A closed tube containing every changed point and remaining in the same
density branch. -/
def closedGraphTube (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.1 ∈ Icc P.a P.b ∧ |p.2 - P.graph p.1| ≤ T.radius}

lemma graphTube_subset_closedGraphTube (P : GraphPatch) (T : P.Tube) :
    P.graphTube T ⊆ P.closedGraphTube T := by
  rintro p ⟨hx, hy⟩
  exact ⟨⟨hx.1.le, hx.2⟩, hy.le⟩

lemma closedGraphTube_in_zone (P : GraphPatch) (T : P.Tube) :
    P.closedGraphTube T ⊆ {p | P.zone.Contains p} := by
  rintro p ⟨hx, hy⟩
  exact T.closed_tube_in_zone p.1 hx p.2 hy

lemma validAt_of_pointwise_mul_lt (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ} (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius) :
    P.ValidAt v t := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hclear := T.order_clearance x hx
    have hbounds := abs_lt.mp (hshift x hx)
    cases hside : P.side <;>
      simp only [hside] at hclear ⊢ <;>
      simp only [variedGraph] <;>
      linarith
  · intro p hp
    cases hside : P.side with
    | below =>
        simp only [variedCarrier, hside] at hp
        have hxClosed : p.1 ∈ Icc P.a P.b := ⟨hp.1.1.le, hp.1.2⟩
        by_cases hold : p.2 < P.graph p.1
        · apply P.carrier_in_zone
          simpa only [carrier, hside] using ⟨hp.1, hp.2.1, hold⟩
        · apply T.closed_tube_in_zone p.1 hxClosed p.2
          have hnonneg : 0 ≤ p.2 - P.graph p.1 :=
            sub_nonneg.mpr (le_of_not_gt hold)
          rw [abs_of_nonneg hnonneg]
          have hupper := hp.2.2
          dsimp [variedGraph] at hupper
          have habs := (abs_lt.mp (hshift p.1 hp.1)).2
          linarith
    | above =>
        simp only [variedCarrier, hside] at hp
        have hxClosed : p.1 ∈ Icc P.a P.b := ⟨hp.1.1.le, hp.1.2⟩
        by_cases hold : P.graph p.1 < p.2
        · apply P.carrier_in_zone
          simpa only [carrier, hside] using ⟨hp.1, hold, hp.2.2⟩
        · apply T.closed_tube_in_zone p.1 hxClosed p.2
          have hnonpos : p.2 - P.graph p.1 ≤ 0 :=
            sub_nonpos.mpr (le_of_not_gt hold)
          rw [abs_of_nonpos hnonpos]
          have hlower := hp.2.1
          dsimp [variedGraph] at hlower
          have habs := (abs_lt.mp (hshift p.1 hp.1)).1
          linarith
  · intro x hx
    have hbounds := abs_lt.mp (hshift x hx)
    have hlower := T.graph_lower_clearance x hx
    have hupper := T.graph_upper_clearance x hx
    dsimp only [variedGraph]
    constructor <;> linarith

/-- A point on the moving graph stays in the certified constant-density tube. -/
lemma variedGraph_in_zone_of_pointwise_mul_lt (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius) :
    ∀ x ∈ Ioc P.a P.b, P.zone.Contains (x, P.variedGraph v t x) := by
  intro x hx
  apply T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩
    (P.variedGraph v t x)
  simp only [variedGraph, add_sub_cancel_left]
  exact (hshift x hx).le

/-- The changed planar set is contained in the prescribed graph tube. -/
lemma variedCarrier_symmDiff_subset_graphTube (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ} (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius) :
    P.variedCarrier v t ∆ P.carrier ⊆ P.graphTube T := by
  intro p hp
  cases hside : P.side with
  | below =>
      simp only [Set.mem_symmDiff, variedCarrier, carrier, hside, regionBetween,
        mem_ofPred_eq, mem_Ioo] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨⟨hx, hbase, hnew⟩, hold⟩
        refine ⟨hx, ?_⟩
        have hnotold : ¬ p.2 < P.graph p.1 := fun h => hold ⟨hx, hbase, h⟩
        have hnonneg : 0 ≤ p.2 - P.graph p.1 :=
          sub_nonneg.mpr (le_of_not_gt hnotold)
        rw [abs_of_nonneg hnonneg]
        dsimp [variedGraph] at hnew
        have hupper := (abs_lt.mp (hshift p.1 hx)).2
        linarith
      · rcases hp with ⟨⟨hx, hbase, hold⟩, hnew⟩
        refine ⟨hx, ?_⟩
        have hnotnew : ¬ p.2 < P.variedGraph v t p.1 :=
          fun h => hnew ⟨hx, hbase, h⟩
        have hneg : p.2 - P.graph p.1 < 0 := sub_neg.mpr hold
        rw [abs_of_neg hneg]
        dsimp [variedGraph] at hnotnew
        have hnewle := le_of_not_gt hnotnew
        have hlower := (abs_lt.mp (hshift p.1 hx)).1
        linarith
  | above =>
      simp only [Set.mem_symmDiff, variedCarrier, carrier, hside, regionBetween,
        mem_ofPred_eq, mem_Ioo] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨⟨hx, hnew, hbase⟩, hold⟩
        refine ⟨hx, ?_⟩
        have hnotold : ¬ P.graph p.1 < p.2 := fun h => hold ⟨hx, h, hbase⟩
        have hnonpos : p.2 - P.graph p.1 ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hnotold)
        rw [abs_of_nonpos hnonpos]
        dsimp [variedGraph] at hnew
        have hlower := (abs_lt.mp (hshift p.1 hx)).1
        linarith
      · rcases hp with ⟨⟨hx, hold, hbase⟩, hnew⟩
        refine ⟨hx, ?_⟩
        have hnotnew : ¬ P.variedGraph v t p.1 < p.2 :=
          fun h => hnew ⟨hx, h, hbase⟩
        have hpos : 0 < p.2 - P.graph p.1 := sub_pos.mpr hold
        rw [abs_of_pos hpos]
        dsimp [variedGraph] at hnotnew
        have hnewle := le_of_not_gt hnotnew
        have hupper := (abs_lt.mp (hshift p.1 hx)).2
        linarith

lemma variedCarrier_symmDiff_subset_closedGraphTube (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ} (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius) :
    P.variedCarrier v t ∆ P.carrier ⊆ P.closedGraphTube T :=
  (P.variedCarrier_symmDiff_subset_graphTube T hshift).trans
    (P.graphTube_subset_closedGraphTube T)

lemma variedCarrier_subset_box (P : GraphPatch) {v : ℝ → ℝ} {t : ℝ}
    (hvalid : P.ValidAt v t) :
    P.variedCarrier v t ⊆ Ioc P.a P.b ×ˢ Ioo P.lowerBound P.upperBound := by
  intro p hp
  cases hside : P.side with
  | below =>
      simp only [variedCarrier, hside] at hp
      exact ⟨hp.1, lt_of_le_of_lt P.lowerBound_le_base hp.2.1,
        lt_of_lt_of_le hp.2.2 (hvalid.2.2 p.1 hp.1).2⟩
  | above =>
      simp only [variedCarrier, hside] at hp
      exact ⟨hp.1, lt_of_le_of_lt (hvalid.2.2 p.1 hp.1).1 hp.2.1,
        lt_of_lt_of_le hp.2.2 P.base_le_upperBound⟩

lemma volume_variedCarrier_ne_top (P : GraphPatch) {v : ℝ → ℝ} {t : ℝ}
    (hvalid : P.ValidAt v t) : volume (P.variedCarrier v t) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (P.variedCarrier_subset_box hvalid))
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioo_lt_top.ne

lemma integrableOn_stripDensity_variedCarrier (P : GraphPatch) {lam t : ℝ}
    {v : ℝ → ℝ} (hvalid : P.ValidAt v t) :
    IntegrableOn (StripDensity lam) (P.variedCarrier v t) :=
  stripDensity_integrableOn_of_volume_ne_top lam (P.volume_variedCarrier_ne_top hvalid)

/-- Exact weighted area of a valid oriented graph region.  This is derived from
the literal planar `WeightedArea` definition and
`volume_regionBetween_eq_lintegral'`; the occupied-side sign is not supplied as
an area identity. -/
theorem weightedArea_variedCarrier (P : GraphPatch) {lam t : ℝ} {v : ℝ → ℝ}
    (hv : Continuous v) (hvalid : P.ValidAt v t) :
    WeightedArea lam (P.variedCarrier v t) =
      P.zone.weight lam * ∫ x in P.a..P.b, P.verticalThickness v t x := by
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
        ∫ x in P.a..P.b, P.verticalThickness v t x := by
      congr 1
      have hgraphMeas : Measurable (P.variedGraph v t) :=
        P.graph_contDiff.continuous.measurable.add
          (measurable_const.mul hv.measurable)
      cases hside : P.side with
      | below =>
          have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc P.a P.b)]
              fun x => P.variedGraph v t x - P.base := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            have hord := hvalid.1 x hx
            simp only [hside] at hord
            exact sub_nonneg.mpr hord.le
          have hmeas : AEStronglyMeasurable
              (fun x => P.variedGraph v t x - P.base)
              (volume.restrict (Ioc P.a P.b)) :=
            ((P.graph_contDiff.continuous.add (continuous_const.mul hv)).sub
              continuous_const).aestronglyMeasurable.restrict
          have hintegral :
              ∫ x in Ioc P.a P.b, (P.variedGraph v t x - P.base) =
                (∫⁻ x in Ioc P.a P.b,
                  ENNReal.ofReal (P.variedGraph v t x - P.base)).toReal :=
            integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
          rw [measureReal_def, Measure.volume_eq_prod]
          simp only [variedCarrier, hside]
          have hvol := volume_regionBetween_eq_lintegral'
            (μ := volume) (f := fun _ : ℝ => P.base) (g := P.variedGraph v t)
            (s := Ioc P.a P.b) measurable_const hgraphMeas measurableSet_Ioc
          rw [hvol]
          simp only [Pi.sub_apply]
          rw [← hintegral, intervalIntegral.integral_of_le P.a_lt_b.le]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro x _hx
          simp [verticalThickness, hside]
      | above =>
          have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc P.a P.b)]
              fun x => P.base - P.variedGraph v t x := by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
            have hord := hvalid.1 x hx
            simp only [hside] at hord
            exact sub_nonneg.mpr hord.le
          have hmeas : AEStronglyMeasurable
              (fun x => P.base - P.variedGraph v t x)
              (volume.restrict (Ioc P.a P.b)) :=
            (continuous_const.sub
              (P.graph_contDiff.continuous.add
                (continuous_const.mul hv))).aestronglyMeasurable.restrict
          have hintegral :
              ∫ x in Ioc P.a P.b, (P.base - P.variedGraph v t x) =
                (∫⁻ x in Ioc P.a P.b,
                  ENNReal.ofReal (P.base - P.variedGraph v t x)).toReal :=
            integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
          rw [measureReal_def, Measure.volume_eq_prod]
          simp only [variedCarrier, hside]
          have hvol := volume_regionBetween_eq_lintegral'
            (μ := volume) (f := P.variedGraph v t) (g := fun _ : ℝ => P.base)
            (s := Ioc P.a P.b) hgraphMeas measurable_const measurableSet_Ioc
          rw [hvol]
          simp only [Pi.sub_apply]
          rw [← hintegral, intervalIntegral.integral_of_le P.a_lt_b.le]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro x _hx
          simp only [verticalThickness, hside, OccupiedSide.areaSign_above]
          ring

/-- The exact oriented planar thickness varies linearly with signed vertical
velocity. -/
lemma intervalIntegral_verticalThickness (P : GraphPatch) {v : ℝ → ℝ}
    (hv : Continuous v) (t : ℝ) :
    (∫ x in P.a..P.b, P.verticalThickness v t x) =
      (∫ x in P.a..P.b, P.verticalThickness v 0 x) +
        t * P.side.areaSign * ∫ x in P.a..P.b, v x := by
  have hbaseCont : Continuous (P.verticalThickness v 0) := by
    unfold verticalThickness variedGraph
    exact continuous_const.mul
      ((P.graph_contDiff.continuous.add (continuous_const.mul hv)).sub
        continuous_const)
  have hbase : IntervalIntegrable (P.verticalThickness v 0)
      volume P.a P.b := hbaseCont.intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun x => (t * P.side.areaSign) * v x) volume P.a P.b :=
    (continuous_const.mul hv).intervalIntegrable _ _
  rw [show (fun x => P.verticalThickness v t x) =
      fun x => P.verticalThickness v 0 x + (t * P.side.areaSign) * v x by
        funext x
        unfold verticalThickness variedGraph
        ring,
    intervalIntegral.integral_add hbase hvar,
    intervalIntegral.integral_const_mul]

end GraphPatch

/-- Smooth compactly supported primary vertical variation. -/
structure PrimaryVariation (P : GraphPatch) where
  toFun : ℝ → ℝ
  contDiff : ContDiff ℝ 2 toFun
  tsupport_subset : tsupport toFun ⊆ Ioo P.a P.b

instance (P : GraphPatch) : CoeFun (PrimaryVariation P) (fun _ => ℝ → ℝ) :=
  ⟨PrimaryVariation.toFun⟩

namespace PrimaryVariation

lemma continuous {P : GraphPatch} (V : PrimaryVariation P) : Continuous V :=
  V.contDiff.continuous

lemma intervalIntegrable {P : GraphPatch} (V : PrimaryVariation P) :
    IntervalIntegrable V volume P.a P.b := V.continuous.intervalIntegrable _ _

/-- The primary graph is literally unchanged outside the declared compact
horizontal support. -/
lemma variedGraph_eq_of_not_mem_interval {P : GraphPatch}
    (V : PrimaryVariation P) (t : ℝ) {x : ℝ} (hx : x ∉ Ioo P.a P.b) :
    P.variedGraph V t x = P.graph x := by
  have hv : V x = 0 := by
    by_contra hne
    exact hx (V.tsupport_subset (subset_tsupport V hne))
  simp [GraphPatch.variedGraph, hv]

end PrimaryVariation

namespace GraphPatch

/-- Canonical bump centered in the second patch, with closed support strictly
inside its horizontal interval. -/
def compensationKernel (P : GraphPatch) : ContDiffBump ((P.a + P.b) / 2) where
  rIn := (P.b - P.a) / 8
  rOut := (P.b - P.a) / 4
  rIn_pos := by linarith [P.a_lt_b]
  rIn_lt_rOut := by linarith [P.a_lt_b]

/-- Internally normalized compensation bump; its whole-line integral is one. -/
def compensationBump (P : GraphPatch) : ℝ → ℝ :=
  (P.compensationKernel).normed volume

lemma compensationBump_contDiff (P : GraphPatch) :
    ContDiff ℝ ∞ P.compensationBump :=
  P.compensationKernel.contDiff_normed

lemma compensationBump_nonneg (P : GraphPatch) (x : ℝ) :
    0 ≤ P.compensationBump x :=
  P.compensationKernel.nonneg_normed x

lemma tsupport_compensationBump_subset (P : GraphPatch) :
    tsupport P.compensationBump ⊆ Ioo P.a P.b := by
  rw [compensationBump, P.compensationKernel.tsupport_normed_eq]
  intro x hx
  rw [mem_closedBall, Real.dist_eq] at hx
  dsimp [compensationKernel] at hx
  rw [abs_le] at hx
  constructor <;> linarith [P.a_lt_b]

lemma support_compensationBump_subset_Ioc (P : GraphPatch) :
    support P.compensationBump ⊆ Ioc P.a P.b :=
  (subset_tsupport _).trans <|
    P.tsupport_compensationBump_subset.trans Ioo_subset_Ioc_self

lemma integral_compensationBump (P : GraphPatch) :
    ∫ x, P.compensationBump x = 1 :=
  P.compensationKernel.integral_normed

lemma intervalIntegral_compensationBump (P : GraphPatch) :
    ∫ x in P.a..P.b, P.compensationBump x = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    P.support_compensationBump_subset_Ioc]
  exact P.integral_compensationBump

end GraphPatch

/-- The internally forced coefficient of the normalized bump on patch 2.  Both
occupied-side signs and both positive density weights enter the exact area
constraint. -/
def compensationCoefficient (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) : ℝ :=
  -((P₁.side.areaSign * P₁.zone.weight lam) /
      (P₂.side.areaSign * P₂.zone.weight lam)) *
    ∫ x in P₁.a..P₁.b, V x

/-- The two velocity fields: the supplied primary variation and the normalized
compensation bump with its forced coefficient. -/
def velocityOne {P₁ : GraphPatch} (V : PrimaryVariation P₁) : ℝ → ℝ := V

def velocityTwo (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) : ℝ → ℝ :=
  fun x => compensationCoefficient lam P₁ P₂ V * P₂.compensationBump x

lemma velocityTwo_contDiff (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) : ContDiff ℝ 2 (velocityTwo lam P₁ P₂ V) := by
  change ContDiff ℝ 2 (fun x =>
    compensationCoefficient lam P₁ P₂ V * P₂.compensationBump x)
  have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    apply WithTop.coe_le_coe.mpr
    exact le_top
  exact contDiff_const.mul (P₂.compensationBump_contDiff.of_le hle)

lemma tsupport_velocityTwo_subset (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) :
    tsupport (velocityTwo lam P₁ P₂ V) ⊆ Ioo P₂.a P₂.b := by
  exact tsupport_mul_subset_right.trans P₂.tsupport_compensationBump_subset

/-- The normalized compensation graph is literally unchanged outside the
second patch's compact horizontal support. -/
lemma variedGraph_velocityTwo_eq_of_not_mem_interval
    (lam : ℝ) (P₁ P₂ : GraphPatch) (V : PrimaryVariation P₁) (t : ℝ)
    {x : ℝ} (hx : x ∉ Ioo P₂.a P₂.b) :
    P₂.variedGraph (velocityTwo lam P₁ P₂ V) t x = P₂.graph x := by
  have hv : velocityTwo lam P₁ P₂ V x = 0 := by
    by_contra hne
    exact hx (tsupport_velocityTwo_subset lam P₁ P₂ V
      (subset_tsupport (velocityTwo lam P₁ P₂ V) hne))
  simp [GraphPatch.variedGraph, hv]

lemma intervalIntegral_velocityTwo (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) :
    ∫ x in P₂.a..P₂.b, velocityTwo lam P₁ P₂ V x =
      compensationCoefficient lam P₁ P₂ V := by
  change (∫ x in P₂.a..P₂.b,
    compensationCoefficient lam P₁ P₂ V * P₂.compensationBump x) = _
  rw [intervalIntegral.integral_const_mul,
    P₂.intervalIntegral_compensationBump, mul_one]

lemma weighted_velocity_integrals_cancel {lam : ℝ} (hlam : 1 < lam)
    (P₁ P₂ : GraphPatch) (V : PrimaryVariation P₁) :
    P₁.side.areaSign * P₁.zone.weight lam *
        (∫ x in P₁.a..P₁.b, V x) +
      P₂.side.areaSign * P₂.zone.weight lam *
        (∫ x in P₂.a..P₂.b, velocityTwo lam P₁ P₂ V x) = 0 := by
  rw [intervalIntegral_velocityTwo, compensationCoefficient]
  field_simp [OccupiedSide.areaSign_ne_zero, DensityZone.weight_ne_zero hlam]
  ring

/-- Two graph patches with disjoint closed horizontal windows.  The stronger
closed-window condition makes every pair of certified closed graph tubes
disjoint, not merely their half-open ribbon carriers. -/
structure TwoPatchData where
  first : GraphPatch
  second : GraphPatch
  horizontal_disjoint : Disjoint (Icc first.a first.b) (Icc second.a second.b)

namespace TwoPatchData

/-- Literal union of the two perturbed planar graph regions. -/
def variedCarrier (D : TwoPatchData) (v₁ v₂ : ℝ → ℝ) (t : ℝ) : Set PlanePoint :=
  D.first.variedCarrier v₁ t ∪ D.second.variedCarrier v₂ t

lemma variedCarrier_fst_mem (P : GraphPatch) {v : ℝ → ℝ} {t : ℝ}
    {p : PlanePoint} (hp : p ∈ P.variedCarrier v t) :
    p.1 ∈ Ioc P.a P.b := by
  cases hside : P.side <;>
    simp only [GraphPatch.variedCarrier, hside] at hp <;>
    exact hp.1

lemma variedCarriers_disjoint (D : TwoPatchData) (v₁ v₂ : ℝ → ℝ) (t : ℝ) :
    Disjoint (D.first.variedCarrier v₁ t) (D.second.variedCarrier v₂ t) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  exact Set.disjoint_left.1 D.horizontal_disjoint
    ⟨(variedCarrier_fst_mem D.first hp₁).1.le,
      (variedCarrier_fst_mem D.first hp₁).2⟩
    ⟨(variedCarrier_fst_mem D.second hp₂).1.le,
      (variedCarrier_fst_mem D.second hp₂).2⟩

/-- Certified closed graph neighborhoods of the two patches are disjoint. -/
lemma closedGraphTubes_disjoint (D : TwoPatchData)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube) :
    Disjoint (D.first.closedGraphTube T₁) (D.second.closedGraphTube T₂) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  exact Set.disjoint_left.1 D.horizontal_disjoint hp₁.1 hp₂.1

lemma measurableSet_variedCarrier (D : TwoPatchData) {v₁ v₂ : ℝ → ℝ}
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂) (t : ℝ) :
    MeasurableSet (D.variedCarrier v₁ v₂ t) :=
  (D.first.measurableSet_variedCarrier hv₁ t).union
    (D.second.measurableSet_variedCarrier hv₂ t)

/-- The compensated two-patch family. -/
def compensatedCarrier (D : TwoPatchData) (lam : ℝ)
    (V : PrimaryVariation D.first) (t : ℝ) : Set PlanePoint :=
  D.variedCarrier V (velocityTwo lam D.first D.second V) t
@[simp] lemma compensatedCarrier_zero (D : TwoPatchData) (lam : ℝ)
    (V : PrimaryVariation D.first) :
    D.compensatedCarrier lam V 0 = D.first.carrier ∪ D.second.carrier := by
  simp [compensatedCarrier, variedCarrier]

/-- Both graph changes are confined to the two certified closed patch tubes. -/
lemma compensatedCarrier_symmDiff_subset_closedGraphTubes
    (D : TwoPatchData) (lam : ℝ) (V : PrimaryVariation D.first)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube) {t : ℝ}
    (hshift₁ : ∀ x ∈ Ioc D.first.a D.first.b, |t * V x| < T₁.radius)
    (hshift₂ : ∀ x ∈ Ioc D.second.a D.second.b,
      |t * velocityTwo lam D.first D.second V x| < T₂.radius) :
    D.compensatedCarrier lam V t ∆ D.compensatedCarrier lam V 0 ⊆
      D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂ := by
  unfold compensatedCarrier variedCarrier
  refine Set.union_symmDiff_union_subset.trans ?_
  apply union_subset_union
  · simpa only [GraphPatch.variedCarrier_zero] using
      D.first.variedCarrier_symmDiff_subset_closedGraphTube T₁ hshift₁
  · simpa only [GraphPatch.variedCarrier_zero] using
      D.second.variedCarrier_symmDiff_subset_closedGraphTube T₂ hshift₂

/-- Membership in the literal two-patch carrier is unchanged away from both
closed patch tubes. -/
lemma mem_compensatedCarrier_iff_of_not_mem_closedGraphTubes
    (D : TwoPatchData) (lam : ℝ) (V : PrimaryVariation D.first)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube) {t : ℝ} {p : PlanePoint}
    (hshift₁ : ∀ x ∈ Ioc D.first.a D.first.b, |t * V x| < T₁.radius)
    (hshift₂ : ∀ x ∈ Ioc D.second.a D.second.b,
      |t * velocityTwo lam D.first D.second V x| < T₂.radius)
    (hp : p ∉ D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂) :
    p ∈ D.compensatedCarrier lam V t ↔
      p ∈ D.compensatedCarrier lam V 0 := by
  have hnot : p ∉ D.compensatedCarrier lam V t ∆
      D.compensatedCarrier lam V 0 := fun hmem =>
    hp (D.compensatedCarrier_symmDiff_subset_closedGraphTubes
      lam V T₁ T₂ hshift₁ hshift₂ hmem)
  simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hnot
  exact ⟨hnot.1, hnot.2⟩

/-- Exact preservation of the literal planar `WeightedArea`. -/
theorem weightedArea_compensatedCarrier {lam : ℝ} (hlam : 1 < lam)
    (D : TwoPatchData) (V : PrimaryVariation D.first) {t : ℝ}
    (hvalid₁ : D.first.ValidAt V t)
    (hvalid₂ : D.second.ValidAt (velocityTwo lam D.first D.second V) t) :
    WeightedArea lam (D.compensatedCarrier lam V t) =
      WeightedArea lam (D.compensatedCarrier lam V 0) := by
  let v₂ := velocityTwo lam D.first D.second V
  have hv₂ : Continuous v₂ :=
    (velocityTwo_contDiff lam D.first D.second V).continuous
  have hvalid₁zero := D.first.validAt_zero V
  have hvalid₂zero := D.second.validAt_zero v₂
  unfold compensatedCarrier variedCarrier
  rw [WeightedArea,
    setIntegral_union₀ (D.variedCarriers_disjoint V v₂ t).aedisjoint
      (D.second.measurableSet_variedCarrier hv₂.measurable t).nullMeasurableSet
      (D.first.integrableOn_stripDensity_variedCarrier hvalid₁)
      (D.second.integrableOn_stripDensity_variedCarrier hvalid₂)]
  rw [WeightedArea,
    setIntegral_union₀ (D.variedCarriers_disjoint V v₂ 0).aedisjoint
      (D.second.measurableSet_variedCarrier hv₂.measurable 0).nullMeasurableSet
      (D.first.integrableOn_stripDensity_variedCarrier hvalid₁zero)
      (D.second.integrableOn_stripDensity_variedCarrier hvalid₂zero)]
  rw [show (∫ p in D.first.variedCarrier V t, StripDensity lam p) =
      D.first.zone.weight lam * ∫ x in D.first.a..D.first.b,
        D.first.verticalThickness V t x by
      simpa [WeightedArea] using D.first.weightedArea_variedCarrier V.continuous hvalid₁,
    show (∫ p in D.second.variedCarrier v₂ t, StripDensity lam p) =
      D.second.zone.weight lam * ∫ x in D.second.a..D.second.b,
        D.second.verticalThickness v₂ t x by
      simpa [WeightedArea] using D.second.weightedArea_variedCarrier hv₂ hvalid₂,
    show (∫ p in D.first.variedCarrier V 0, StripDensity lam p) =
      D.first.zone.weight lam * ∫ x in D.first.a..D.first.b,
        D.first.verticalThickness V 0 x by
      simpa [WeightedArea] using D.first.weightedArea_variedCarrier V.continuous hvalid₁zero,
    show (∫ p in D.second.variedCarrier v₂ 0, StripDensity lam p) =
      D.second.zone.weight lam * ∫ x in D.second.a..D.second.b,
        D.second.verticalThickness v₂ 0 x by
      simpa [WeightedArea] using D.second.weightedArea_variedCarrier hv₂ hvalid₂zero]
  rw [D.first.intervalIntegral_verticalThickness V.continuous t,
    D.second.intervalIntegral_verticalThickness hv₂ t]
  have hcancel := weighted_velocity_integrals_cancel hlam D.first D.second V
  linear_combination t * hcancel

/-- Density-one/interior specialization of exact planar area preservation. -/
theorem weightedArea_compensatedCarrier_interior {lam : ℝ} (hlam : 1 < lam)
    (D : TwoPatchData) (hfirst : D.first.zone = .interior)
    (hsecond : D.second.zone = .interior)
    (V : PrimaryVariation D.first) {t : ℝ}
    (hvalid₁ : D.first.ValidAt V t)
    (hvalid₂ : D.second.ValidAt (velocityTwo lam D.first D.second V) t) :
    WeightedArea lam (D.compensatedCarrier lam V t) =
      WeightedArea lam (D.compensatedCarrier lam V 0) := by
  have _ := hfirst
  have _ := hsecond
  exact D.weightedArea_compensatedCarrier hlam V hvalid₁ hvalid₂

/-- Arbitrary `lam > 1` exterior/exterior specialization of exact planar area
preservation. -/
theorem weightedArea_compensatedCarrier_exterior {lam : ℝ} (hlam : 1 < lam)
    (D : TwoPatchData) (hfirst : D.first.zone = .exterior)
    (hsecond : D.second.zone = .exterior)
    (V : PrimaryVariation D.first) {t : ℝ}
    (hvalid₁ : D.first.ValidAt V t)
    (hvalid₂ : D.second.ValidAt (velocityTwo lam D.first D.second V) t) :
    WeightedArea lam (D.compensatedCarrier lam V t) =
      WeightedArea lam (D.compensatedCarrier lam V 0) := by
  have _ := hfirst
  have _ := hsecond
  exact D.weightedArea_compensatedCarrier hlam V hvalid₁ hvalid₂

end TwoPatchData

/-! ## Replacement inside an actual ambient carrier -/

/-- Two local graph ribbons cut out of one actual bounded carrier.

`actualCarrier_eq_fixed_union` is a set-level local representation, not an area
formula: the fixed part and both occupied-side ribbons reconstruct the literal
carrier.  `fixed_disjoint_closedGraphTubes` says that the actual fixed geometry
does not re-enter either replacement neighborhood.  The two graph traces are
explicitly required to be pieces of the actual topological frontier. -/
structure ActualTwoPatchData where
  patches : TwoPatchData
  firstTube : patches.first.Tube
  secondTube : patches.second.Tube
  actualCarrier : Set PlanePoint
  fixedCarrier : Set PlanePoint
  actualCarrier_eq_fixed_union :
    actualCarrier =
      fixedCarrier ∪ (patches.first.carrier ∪ patches.second.carrier)
  measurableSet_actualCarrier : MeasurableSet actualCarrier
  measurableSet_fixedCarrier : MeasurableSet fixedCarrier
  actualCarrier_bounded : Bornology.IsBounded actualCarrier
  fixed_disjoint_patchCarriers :
    Disjoint fixedCarrier
      (patches.first.carrier ∪ patches.second.carrier)
  fixed_disjoint_closedGraphTubes :
    Disjoint fixedCarrier
      (patches.first.closedGraphTube firstTube ∪
        patches.second.closedGraphTube secondTube)
  first_graph_frontier :
    ∀ x ∈ Ioo patches.first.a patches.first.b,
      (x, patches.first.graph x) ∈ frontier actualCarrier
  second_graph_frontier :
    ∀ x ∈ Ioo patches.second.a patches.second.b,
      (x, patches.second.graph x) ∈ frontier actualCarrier

namespace ActualTwoPatchData

/-- Replace only the two actual graph ribbons, retaining the carrier's fixed
part literally. -/
def variedCarrier (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) : Set PlanePoint :=
  A.fixedCarrier ∪ A.patches.compensatedCarrier lam V t

@[simp] theorem variedCarrier_zero (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) :
    A.variedCarrier lam V 0 = A.actualCarrier := by
  rw [variedCarrier, A.patches.compensatedCarrier_zero]
  exact A.actualCarrier_eq_fixed_union.symm

lemma fixedCarrier_subset_actualCarrier (A : ActualTwoPatchData) :
    A.fixedCarrier ⊆ A.actualCarrier := by
  intro p hp
  rw [A.actualCarrier_eq_fixed_union]
  exact Or.inl hp

lemma fixedCarrier_bounded (A : ActualTwoPatchData) :
    Bornology.IsBounded A.fixedCarrier :=
  A.actualCarrier_bounded.subset A.fixedCarrier_subset_actualCarrier

lemma integrableOn_fixedCarrier (A : ActualTwoPatchData) (lam : ℝ) :
    IntegrableOn (StripDensity lam) A.fixedCarrier :=
  stripDensity_integrableOn_of_volume_ne_top lam
    A.fixedCarrier_bounded.measure_lt_top.ne

/-- The actual fixed remainder is disjoint from every localized varied ribbon,
not only from the original ribbons. -/
lemma fixedCarrier_disjoint_compensatedCarrier
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) :
    Disjoint A.fixedCarrier
      (A.patches.compensatedCarrier lam V t) := by
  rw [Set.disjoint_left]
  intro p hpFixed hpVaried
  by_cases hpOriginal :
      p ∈ A.patches.compensatedCarrier lam V 0
  · apply Set.disjoint_left.1 A.fixed_disjoint_patchCarriers hpFixed
    simpa only [A.patches.compensatedCarrier_zero] using hpOriginal
  · have hpDiff :
        p ∈ A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 := by
      simp only [Set.mem_symmDiff]
      exact Or.inl ⟨hpVaried, hpOriginal⟩
    exact Set.disjoint_left.1 A.fixed_disjoint_closedGraphTubes hpFixed
      (hdiff hpDiff)

lemma measurableSet_variedCarrier (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) :
    MeasurableSet (A.variedCarrier lam V t) :=
  A.measurableSet_fixedCarrier.union
    (A.patches.measurableSet_variedCarrier V.continuous.measurable
      (velocityTwo_contDiff lam A.patches.first A.patches.second V).continuous.measurable t)

lemma integrableOn_variedCarrier
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hcomp :
      IntegrableOn (StripDensity lam)
        (A.patches.compensatedCarrier lam V t)) :
    IntegrableOn (StripDensity lam) (A.variedCarrier lam V t) :=
  (A.integrableOn_fixedCarrier lam).union hcomp

/-- Additivity of literal weighted area for the actual fixed remainder and the
localized moving ribbons. -/
theorem weightedArea_variedCarrier_eq_add
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hcomp :
      IntegrableOn (StripDensity lam)
        (A.patches.compensatedCarrier lam V t))
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) :
    WeightedArea lam (A.variedCarrier lam V t) =
      WeightedArea lam A.fixedCarrier +
        WeightedArea lam (A.patches.compensatedCarrier lam V t) := by
  simpa only [WeightedArea, variedCarrier] using
    setIntegral_union₀
      (A.fixedCarrier_disjoint_compensatedCarrier lam V hdiff).aedisjoint
      (A.patches.measurableSet_variedCarrier V.continuous.measurable
        (velocityTwo_contDiff lam A.patches.first A.patches.second V).continuous.measurable
        t).nullMeasurableSet
      (A.integrableOn_fixedCarrier lam) hcomp

/-- Exact weighted-area preservation for the literal actual carrier, derived
from the set replacement and the internally normalized compensation bump. -/
theorem weightedArea_variedCarrier
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hvalid₁ : A.patches.first.ValidAt V t)
    (hvalid₂ : A.patches.second.ValidAt
      (velocityTwo lam A.patches.first A.patches.second V) t)
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) :
    WeightedArea lam (A.variedCarrier lam V t) =
      WeightedArea lam A.actualCarrier := by
  have hcomp :
      IntegrableOn (StripDensity lam)
        (A.patches.compensatedCarrier lam V t) :=
    (A.patches.first.integrableOn_stripDensity_variedCarrier hvalid₁).union
      (A.patches.second.integrableOn_stripDensity_variedCarrier hvalid₂)
  have hvalid₁zero := A.patches.first.validAt_zero V
  have hvalid₂zero := A.patches.second.validAt_zero
    (velocityTwo lam A.patches.first A.patches.second V)
  have hcompZero :
      IntegrableOn (StripDensity lam)
        (A.patches.compensatedCarrier lam V 0) :=
    (A.patches.first.integrableOn_stripDensity_variedCarrier hvalid₁zero).union
      (A.patches.second.integrableOn_stripDensity_variedCarrier hvalid₂zero)
  have hdiffZero :
      A.patches.compensatedCarrier lam V 0 ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube := by
    simp
  calc
    WeightedArea lam (A.variedCarrier lam V t) =
        WeightedArea lam A.fixedCarrier +
          WeightedArea lam (A.patches.compensatedCarrier lam V t) :=
      A.weightedArea_variedCarrier_eq_add lam V hcomp hdiff
    _ = WeightedArea lam A.fixedCarrier +
          WeightedArea lam (A.patches.compensatedCarrier lam V 0) := by
      rw [A.patches.weightedArea_compensatedCarrier
        hlam V hvalid₁ hvalid₂]
    _ = WeightedArea lam (A.variedCarrier lam V 0) :=
      (A.weightedArea_variedCarrier_eq_add lam V hcompZero hdiffZero).symm
    _ = WeightedArea lam A.actualCarrier := by
      rw [A.variedCarrier_zero]

/-- The actual ambient carrier changes only inside the two certified closed
constant-density graph neighborhoods. -/
lemma variedCarrier_symmDiff_subset_closedGraphTubes
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) :
    A.variedCarrier lam V t ∆ A.actualCarrier ⊆
      A.patches.first.closedGraphTube A.firstTube ∪
        A.patches.second.closedGraphTube A.secondTube := by
  rw [← A.variedCarrier_zero lam V]
  intro p hp
  apply hdiff
  simpa using (Set.union_symmDiff_union_subset hp)

/-- Literal membership of the actual carrier is unchanged outside both graph
neighborhoods. -/
lemma mem_variedCarrier_iff_of_not_mem_closedGraphTubes
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) {t : ℝ} {p : PlanePoint}
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube)
    (hp : p ∉ A.patches.first.closedGraphTube A.firstTube ∪
      A.patches.second.closedGraphTube A.secondTube) :
    p ∈ A.variedCarrier lam V t ↔ p ∈ A.actualCarrier := by
  have hnot : p ∉ A.variedCarrier lam V t ∆ A.actualCarrier :=
    fun hmem => hp (A.variedCarrier_symmDiff_subset_closedGraphTubes
      lam V hdiff hmem)
  simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hnot
  exact ⟨hnot.1, hnot.2⟩

end ActualTwoPatchData

/-! ## Literal weighted Euclidean graph-length differentiation -/

private def arcF (p q : ℝ → ℝ) (t x : ℝ) : ℝ :=
  Real.sqrt (1 + (p x + t * q x) ^ 2)

private def arcF' (p q : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (p x + t * q x) * q x / Real.sqrt (1 + (p x + t * q x) ^ 2)

private theorem arcF_hasDerivAt (p q : ℝ → ℝ) (t x : ℝ) :
    HasDerivAt (fun s => arcF p q s x) (arcF' p q t x) t := by
  unfold arcF arcF'
  have hlin : DifferentiableAt ℝ (fun s : ℝ => p x + s * q x) t := by fun_prop
  have hinner : DifferentiableAt ℝ
      (fun s : ℝ => 1 + (p x + s * q x) ^ 2) t := by fun_prop
  have hsq : DifferentiableAt ℝ
      (fun s : ℝ => Real.sqrt (1 + (p x + s * q x) ^ 2)) t :=
    hinner.sqrt (by positivity)
  apply hsq.hasDerivAt.congr_deriv
  rw [deriv_sqrt hinner (by positivity)]
  have hlin_deriv : deriv (fun s : ℝ => p x + s * q x) t = q x := by
    rw [deriv_const_add]
    simp
  have hpow_deriv : deriv (fun s : ℝ => (p x + s * q x) ^ 2) t =
      2 * (p x + t * q x) * q x := by
    change deriv ((fun s : ℝ => p x + s * q x) ^ 2) t = _
    rw [deriv_pow hlin 2, hlin_deriv]
    ring
  rw [deriv_const_add, hpow_deriv]
  have hroot : Real.sqrt (1 + (p x + t * q x) ^ 2) ≠ 0 := by positivity
  field_simp

private theorem arcF'_norm_le (p q : ℝ → ℝ) (t x : ℝ) :
    ‖arcF' p q t x‖ ≤ |q x| := by
  let z := p x + t * q x
  have hroot : 0 < Real.sqrt (1 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hzle : |z| ≤ Real.sqrt (1 + z ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg z) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    linarith [sq_nonneg z]
  rw [arcF', Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hroot]
  calc
    |p x + t * q x| * |q x| / Real.sqrt (1 + (p x + t * q x) ^ 2) =
        (|z| / Real.sqrt (1 + z ^ 2)) * |q x| := by simp [z]; ring
    _ ≤ 1 * |q x| :=
      mul_le_mul_of_nonneg_right ((div_le_one hroot).2 hzle) (abs_nonneg _)
    _ = |q x| := one_mul _

private theorem graphLengthVariation_hasDerivAt {a b : ℝ} {p q : ℝ → ℝ}
    (hp : Continuous p) (hq : Continuous q) :
    HasDerivAt
      (fun t => ∫ x in a..b, Real.sqrt (1 + (p x + t * q x) ^ 2))
      (∫ x in a..b, p x * q x / Real.sqrt (1 + (p x) ^ 2)) 0 := by
  have hFcont (t : ℝ) : Continuous (arcF p q t) := by unfold arcF; fun_prop
  have hF'cont (t : ℝ) : Continuous (arcF' p q t) := by
    unfold arcF'
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      positivity
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b)
    (F := arcF p q) (F' := arcF' p q) (bound := fun x => |q x|)
    (s := univ) (x₀ := 0) univ_mem
    (by filter_upwards with t; exact (hFcont t).aestronglyMeasurable.restrict)
    ((hFcont 0).intervalIntegrable a b)
    ((hF'cont 0).aestronglyMeasurable.restrict)
    (by filter_upwards with x; intro _ t _; exact arcF'_norm_le p q t x)
    (hq.abs.intervalIntegrable a b)
    (by filter_upwards with x; intro _ t _; exact arcF_hasDerivAt p q t x)
  simpa only [arcF, arcF', zero_mul, add_zero] using h.2

/-- Differentiation under the integral for a Euclidean graph-speed family.
This public scalar lemma is shared by vertical and horizontal graph charts. -/
theorem graphLengthIntegral_hasDerivAt {a b : ℝ} {p q : ℝ → ℝ}
    (hp : Continuous p) (hq : Continuous q) :
    HasDerivAt
      (fun t => ∫ x in a..b, Real.sqrt (1 + (p x + t * q x) ^ 2))
      (∫ x in a..b, p x * q x / Real.sqrt (1 + (p x) ^ 2)) 0 :=
  graphLengthVariation_hasDerivAt hp hq

lemma deriv_variedGraph (P : GraphPatch) {v : ℝ → ℝ}
    (hv : Differentiable ℝ v) (t x : ℝ) :
    deriv (P.variedGraph v t) x = deriv P.graph x + t * deriv v x := by
  change deriv (P.graph + fun y => t * v y) x = _
  simpa only [deriv_const_mul_field] using
    deriv_add (P.graph_contDiff.differentiable (by norm_num) x) ((hv x).const_mul t)

/-- Literal weighted Euclidean graph length on a constant-density patch. -/
def weightedGraphLength (lam : ℝ) (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in P.a..P.b,
    StripDensity lam (x, P.variedGraph v t x) *
      Real.sqrt (1 + (deriv (P.variedGraph v t) x) ^ 2)

/-- On a valid constant-density graph patch, the literal density remains the
zone weight along the moving graph. -/
lemma weightedGraphLength_eq_weight (lam : ℝ) (P : GraphPatch) {v : ℝ → ℝ} {t : ℝ}
    (hgraphZone : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph v t x)) :
    weightedGraphLength lam P v t = P.zone.weight lam *
      ∫ x in P.a..P.b, Real.sqrt (1 + (deriv (P.variedGraph v t) x) ^ 2) := by
  rw [weightedGraphLength, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le P.a_lt_b.le,
    intervalIntegral.integral_of_le P.a_lt_b.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only
  rw [DensityZone.stripDensity_eq_weight (hgraphZone x hx)]

/-- Derivative at zero of the literal weighted graph-length integral, under a
local constant-density hypothesis.  The conclusion contains `StripDensity`
itself rather than an assumed perimeter formula. -/
theorem weightedGraphLength_hasDerivAt (lam : ℝ) (P : GraphPatch) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v)
    (hzone : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph v t x)) :
    HasDerivAt (weightedGraphLength lam P v)
      (P.zone.weight lam * ∫ x in P.a..P.b,
        deriv P.graph x * deriv v x /
          Real.sqrt (1 + (deriv P.graph x) ^ 2)) 0 := by
  have hbase := graphLengthVariation_hasDerivAt
    (a := P.a) (b := P.b) (p := deriv P.graph) (q := deriv v)
    (P.graph_contDiff.continuous_deriv (by norm_num))
    (hv.continuous_deriv (by norm_num))
  have hscaled := hbase.const_mul (P.zone.weight lam)
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [hzone] with t ht
  rw [weightedGraphLength_eq_weight lam P ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  simp only
  rw [deriv_variedGraph P (hv.differentiable (by norm_num))]

/-- Literal total graph length of the two compensated moving boundaries. -/
def totalWeightedGraphLength (lam : ℝ) (D : TwoPatchData)
    (V : PrimaryVariation D.first) (t : ℝ) : ℝ :=
  weightedGraphLength lam D.first V t +
    weightedGraphLength lam D.second (velocityTwo lam D.first D.second V) t

/-- First variation of the literal sum of the two weighted Euclidean graph
length integrals. -/
theorem totalWeightedGraphLength_hasDerivAt {lam : ℝ} (D : TwoPatchData)
    (V : PrimaryVariation D.first)
    (hzone₁ : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ Ioc D.first.a D.first.b,
      D.first.zone.Contains (x, D.first.variedGraph V t x))
    (hzone₂ : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ Ioc D.second.a D.second.b,
      D.second.zone.Contains
        (x, D.second.variedGraph (velocityTwo lam D.first D.second V) t x)) :
    HasDerivAt (totalWeightedGraphLength lam D V)
      ((D.first.zone.weight lam * ∫ x in D.first.a..D.first.b,
          deriv D.first.graph x * deriv V x /
            Real.sqrt (1 + (deriv D.first.graph x) ^ 2)) +
        (D.second.zone.weight lam * ∫ x in D.second.a..D.second.b,
          deriv D.second.graph x *
              deriv (velocityTwo lam D.first D.second V) x /
            Real.sqrt (1 + (deriv D.second.graph x) ^ 2))) 0 := by
  change HasDerivAt
    (fun t => weightedGraphLength lam D.first V t +
      weightedGraphLength lam D.second
        (velocityTwo lam D.first D.second V) t) _ 0
  exact (weightedGraphLength_hasDerivAt lam D.first V.contDiff hzone₁).add
    (weightedGraphLength_hasDerivAt lam D.second
      (velocityTwo_contDiff lam D.first D.second V) hzone₂)

/-- The checkpoint packages sufficiently-small oriented validity, closed-tube
locality, unchanged geometry away from both patches, integrability, and exact
literal weighted area preservation. -/
theorem twoPatch_checkpoint {lam : ℝ} (hlam : 1 < lam) (D : TwoPatchData)
    (V : PrimaryVariation D.first) (T₁ : D.first.Tube) (T₂ : D.second.Tube) :
    ∃ ε > 0, ∀ t, |t| < ε →
      D.first.ValidAt V t ∧
      D.second.ValidAt (velocityTwo lam D.first D.second V) t ∧
      (∀ x ∈ Ioc D.first.a D.first.b,
        D.first.zone.Contains (x, D.first.variedGraph V t x)) ∧
      (∀ x ∈ Ioc D.second.a D.second.b,
        D.second.zone.Contains
          (x, D.second.variedGraph (velocityTwo lam D.first D.second V) t x)) ∧
      D.first.variedCarrier V t ∆ D.first.carrier ⊆
        D.first.closedGraphTube T₁ ∧
      D.second.variedCarrier (velocityTwo lam D.first D.second V) t ∆
          D.second.carrier ⊆ D.second.closedGraphTube T₂ ∧
      D.compensatedCarrier lam V t ∆ D.compensatedCarrier lam V 0 ⊆
        D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂ ∧
      (∀ p ∉ D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂,
        (p ∈ D.compensatedCarrier lam V t ↔
          p ∈ D.compensatedCarrier lam V 0)) ∧
      IntegrableOn (StripDensity lam) (D.compensatedCarrier lam V t) ∧
      WeightedArea lam (D.compensatedCarrier lam V t) =
        WeightedArea lam (D.compensatedCarrier lam V 0) := by
  have hVcompact : HasCompactSupport V := by
    rw [HasCompactSupport]
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (V.tsupport_subset.trans Ioo_subset_Icc_self)
  obtain ⟨M₁, hM₁⟩ :=
    V.continuous.bounded_above_of_compact_support hVcompact
  let v₂ := velocityTwo lam D.first D.second V
  have hv₂cont : Continuous v₂ :=
    (velocityTwo_contDiff lam D.first D.second V).continuous
  have hv₂compact : HasCompactSupport v₂ := by
    change HasCompactSupport (fun x =>
      compensationCoefficient lam D.first D.second V *
        D.second.compensationBump x)
    exact D.second.compensationKernel.hasCompactSupport_normed.mul_left
  obtain ⟨M₂, hM₂⟩ := hv₂cont.bounded_above_of_compact_support hv₂compact
  let M := max 1 (max M₁ M₂)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨min (T₁.radius / M) (T₂.radius / M),
    lt_min (div_pos T₁.radius_pos hMpos) (div_pos T₂.radius_pos hMpos), ?_⟩
  intro t ht
  have hM₁le : M₁ ≤ M :=
    le_trans (le_max_left M₁ M₂) (le_max_right 1 (max M₁ M₂))
  have hM₂le : M₂ ≤ M :=
    le_trans (le_max_right M₁ M₂) (le_max_right 1 (max M₁ M₂))
  have ht₁ : |t| * M₁ < T₁.radius := by
    have htM : |t| * M < T₁.radius := by
      apply (lt_div_iff₀ hMpos).mp
      exact lt_of_lt_of_le ht (min_le_left _ _)
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hM₁le (abs_nonneg t)) htM
  have ht₂ : |t| * M₂ < T₂.radius := by
    have htM : |t| * M < T₂.radius := by
      apply (lt_div_iff₀ hMpos).mp
      exact lt_of_lt_of_le ht (min_le_right _ _)
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hM₂le (abs_nonneg t)) htM
  have hshift₁ : ∀ x ∈ Ioc D.first.a D.first.b, |t * V x| < T₁.radius := by
    intro x _hx
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hM₁ x) (abs_nonneg t)) ht₁
  have hshift₂ : ∀ x ∈ Ioc D.second.a D.second.b, |t * v₂ x| < T₂.radius := by
    intro x _hx
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hM₂ x) (abs_nonneg t)) ht₂
  have hvalid₁ := D.first.validAt_of_pointwise_mul_lt T₁ hshift₁
  have hvalid₂ := D.second.validAt_of_pointwise_mul_lt T₂ hshift₂
  refine ⟨hvalid₁, hvalid₂,
    D.first.variedGraph_in_zone_of_pointwise_mul_lt T₁ hshift₁,
    D.second.variedGraph_in_zone_of_pointwise_mul_lt T₂ hshift₂,
    D.first.variedCarrier_symmDiff_subset_closedGraphTube T₁ hshift₁,
    D.second.variedCarrier_symmDiff_subset_closedGraphTube T₂ hshift₂,
    D.compensatedCarrier_symmDiff_subset_closedGraphTubes
      lam V T₁ T₂ hshift₁ hshift₂,
    fun _p hp => D.mem_compensatedCarrier_iff_of_not_mem_closedGraphTubes
      lam V T₁ T₂ hshift₁ hshift₂ hp, ?_,
    D.weightedArea_compensatedCarrier hlam V hvalid₁ hvalid₂⟩
  apply IntegrableOn.union
  · exact D.first.integrableOn_stripDensity_variedCarrier hvalid₁
  · exact D.second.integrableOn_stripDensity_variedCarrier hvalid₂

/-- Full first checkpoint: the exact oriented small compensated family and the
derivative of its literal two graph-length integrals are proved together. -/
theorem twoPatch_checkpoint_with_firstVariation {lam : ℝ} (hlam : 1 < lam)
    (D : TwoPatchData) (V : PrimaryVariation D.first)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube) :
    (∃ ε > 0, ∀ t, |t| < ε →
      D.first.ValidAt V t ∧
      D.second.ValidAt (velocityTwo lam D.first D.second V) t ∧
      (∀ x ∈ Ioc D.first.a D.first.b,
        D.first.zone.Contains (x, D.first.variedGraph V t x)) ∧
      (∀ x ∈ Ioc D.second.a D.second.b,
        D.second.zone.Contains
          (x, D.second.variedGraph (velocityTwo lam D.first D.second V) t x)) ∧
      D.first.variedCarrier V t ∆ D.first.carrier ⊆
        D.first.closedGraphTube T₁ ∧
      D.second.variedCarrier (velocityTwo lam D.first D.second V) t ∆
          D.second.carrier ⊆ D.second.closedGraphTube T₂ ∧
      D.compensatedCarrier lam V t ∆ D.compensatedCarrier lam V 0 ⊆
        D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂ ∧
      (∀ p ∉ D.first.closedGraphTube T₁ ∪ D.second.closedGraphTube T₂,
        (p ∈ D.compensatedCarrier lam V t ↔
          p ∈ D.compensatedCarrier lam V 0)) ∧
      IntegrableOn (StripDensity lam) (D.compensatedCarrier lam V t) ∧
      WeightedArea lam (D.compensatedCarrier lam V t) =
        WeightedArea lam (D.compensatedCarrier lam V 0)) ∧
    HasDerivAt (totalWeightedGraphLength lam D V)
      ((D.first.zone.weight lam * ∫ x in D.first.a..D.first.b,
          deriv D.first.graph x * deriv V x /
            Real.sqrt (1 + (deriv D.first.graph x) ^ 2)) +
        (D.second.zone.weight lam * ∫ x in D.second.a..D.second.b,
          deriv D.second.graph x *
              deriv (velocityTwo lam D.first D.second V) x /
            Real.sqrt (1 + (deriv D.second.graph x) ^ 2))) 0 := by
  rcases twoPatch_checkpoint hlam D V T₁ T₂ with ⟨ε, hε, hlocal⟩
  refine ⟨⟨ε, hε, hlocal⟩,
    totalWeightedGraphLength_hasDerivAt D V ?_ ?_⟩
  · filter_upwards [ball_mem_nhds (0 : ℝ) hε] with t ht
    have habs : |t| < ε := by simpa [Real.dist_eq] using ht
    exact (hlocal t habs).2.2.1
  · filter_upwards [ball_mem_nhds (0 : ℝ) hε] with t ht
    have habs : |t| < ε := by simpa [Real.dist_eq] using ht
    exact (hlocal t habs).2.2.2.1

/-- Actual-carrier first checkpoint.  The two local graphs are certified pieces
of one literal ambient frontier; their disjoint closed neighborhoods remain in
their declared constant-density zones.  For all sufficiently small parameters,
the actual carrier is measurable and integrable, changes nowhere else, keeps
its literal weighted area exactly, and its two moving Euclidean graph lengths
have the displayed first derivative. -/
theorem actualTwoPatch_checkpoint_with_firstVariation
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (V : PrimaryVariation A.patches.first) :
    (∃ ε > 0, ∀ t, |t| < ε →
      A.patches.first.ValidAt V t ∧
      A.patches.second.ValidAt
        (velocityTwo lam A.patches.first A.patches.second V) t ∧
      Disjoint
        (A.patches.first.closedGraphTube A.firstTube)
        (A.patches.second.closedGraphTube A.secondTube) ∧
      A.patches.first.closedGraphTube A.firstTube ⊆
        {p | A.patches.first.zone.Contains p} ∧
      A.patches.second.closedGraphTube A.secondTube ⊆
        {p | A.patches.second.zone.Contains p} ∧
      (∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
        (x, A.patches.first.graph x) ∈ frontier A.actualCarrier) ∧
      (∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        (x, A.patches.second.graph x) ∈ frontier A.actualCarrier) ∧
      MeasurableSet (A.variedCarrier lam V t) ∧
      IntegrableOn (StripDensity lam) (A.variedCarrier lam V t) ∧
      WeightedArea lam (A.variedCarrier lam V t) =
        WeightedArea lam A.actualCarrier ∧
      A.variedCarrier lam V t ∆ A.actualCarrier ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube ∧
      (∀ p ∉ A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube,
        (p ∈ A.variedCarrier lam V t ↔ p ∈ A.actualCarrier)) ∧
      (∀ x ∉ Ioo A.patches.first.a A.patches.first.b,
        A.patches.first.variedGraph V t x = A.patches.first.graph x) ∧
      (∀ x ∉ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.variedGraph
          (velocityTwo lam A.patches.first A.patches.second V) t x =
            A.patches.second.graph x)) ∧
    HasDerivAt (totalWeightedGraphLength lam A.patches V)
      ((A.patches.first.zone.weight lam *
          ∫ x in A.patches.first.a..A.patches.first.b,
            deriv A.patches.first.graph x * deriv V x /
              Real.sqrt (1 + (deriv A.patches.first.graph x) ^ 2)) +
        (A.patches.second.zone.weight lam *
          ∫ x in A.patches.second.a..A.patches.second.b,
            deriv A.patches.second.graph x *
                deriv (velocityTwo lam A.patches.first A.patches.second V) x /
              Real.sqrt (1 + (deriv A.patches.second.graph x) ^ 2))) 0 := by
  rcases twoPatch_checkpoint_with_firstVariation hlam A.patches V
    A.firstTube A.secondTube with ⟨⟨ε, hε, hlocal⟩, hderiv⟩
  refine ⟨⟨ε, hε, ?_⟩, hderiv⟩
  intro t ht
  rcases hlocal t ht with
    ⟨hvalid₁, hvalid₂, _hzone₁, _hzone₂, _hdiff₁, _hdiff₂,
      hdiff, _houtside, hcomp, _hribbonArea⟩
  refine ⟨hvalid₁, hvalid₂,
    A.patches.closedGraphTubes_disjoint A.firstTube A.secondTube,
    A.patches.first.closedGraphTube_in_zone A.firstTube,
    A.patches.second.closedGraphTube_in_zone A.secondTube,
    A.first_graph_frontier, A.second_graph_frontier,
    A.measurableSet_variedCarrier lam V t,
    A.integrableOn_variedCarrier lam V hcomp,
    A.weightedArea_variedCarrier hlam V hvalid₁ hvalid₂ hdiff,
    A.variedCarrier_symmDiff_subset_closedGraphTubes lam V hdiff,
    fun _p hp => A.mem_variedCarrier_iff_of_not_mem_closedGraphTubes
      lam V hdiff hp,
    fun _x hx => V.variedGraph_eq_of_not_mem_interval t hx,
    fun _x hx => variedGraph_velocityTwo_eq_of_not_mem_interval
      lam A.patches.first A.patches.second V t hx⟩

/-! ## Concrete interior and exterior applications -/

namespace Examples

/-- A nonvacuous flat density-one patch occupied below its graph. -/
def interiorPatch (a b : ℝ) (hab : a < b) : GraphPatch where
  a := a
  b := b
  base := -(1 / 2 : ℝ)
  graph := fun _ => 0
  lowerBound := -1
  upperBound := 1
  zone := .interior
  side := .below
  a_lt_b := hab
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    rintro p ⟨_hx, hyLower, hyUpper⟩
    change |p.2| ≤ 1
    rw [abs_le]
    constructor <;> linarith

/-- A radius-`1/4` closed-density tube for the flat interior patch. -/
def interiorTube (a b : ℝ) (hab : a < b) :
    (interiorPatch a b hab).Tube where
  radius := 1 / 4
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [interiorPatch]
  graph_lower_clearance := by intros; norm_num [interiorPatch]
  graph_upper_clearance := by intros; norm_num [interiorPatch]
  closed_tube_in_zone := by
    intro x _hx y hy
    change |y| ≤ 1
    change |y - 0| ≤ 1 / 4 at hy
    simpa only [sub_zero] using
      le_trans hy (by norm_num : (1 / 4 : ℝ) ≤ 1)

/-- A nonvacuous flat density-one patch occupied above its graph. -/
def interiorAbovePatch (a b : ℝ) (hab : a < b) : GraphPatch where
  a := a
  b := b
  base := 1 / 2
  graph := fun _ => 0
  lowerBound := -1
  upperBound := 1
  zone := .interior
  side := .above
  a_lt_b := hab
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    rintro p ⟨_hx, hyLower, hyUpper⟩
    change |p.2| ≤ 1
    rw [abs_le]
    constructor <;> linarith

def interiorAboveTube (a b : ℝ) (hab : a < b) :
    (interiorAbovePatch a b hab).Tube where
  radius := 1 / 4
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [interiorAbovePatch]
  graph_lower_clearance := by intros; norm_num [interiorAbovePatch]
  graph_upper_clearance := by intros; norm_num [interiorAbovePatch]
  closed_tube_in_zone := by
    intro x _hx y hy
    change |y| ≤ 1
    change |y - 0| ≤ 1 / 4 at hy
    simpa only [sub_zero] using
      le_trans hy (by norm_num : (1 / 4 : ℝ) ≤ 1)

/-- A flat upper-exterior patch occupied below its graph. -/
def exteriorPatch (a b : ℝ) (hab : a < b) : GraphPatch where
  a := a
  b := b
  base := 2
  graph := fun _ => 3
  lowerBound := 2
  upperBound := 4
  zone := .exterior
  side := .below
  a_lt_b := hab
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := le_rfl
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    rintro p ⟨_hx, hyLower, _hyUpper⟩
    change 1 < |p.2|
    rw [abs_of_pos (by linarith)]
    linarith

/-- A radius-`1/4` closed-density tube for the upper-exterior patch. -/
def exteriorTube (a b : ℝ) (hab : a < b) :
    (exteriorPatch a b hab).Tube where
  radius := 1 / 4
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [exteriorPatch]
  graph_lower_clearance := by intros; norm_num [exteriorPatch]
  graph_upper_clearance := by intros; norm_num [exteriorPatch]
  closed_tube_in_zone := by
    intro x _hx y hy
    change 1 < |y|
    change |y - 3| ≤ 1 / 4 at hy
    have hyLower : 1 < y := by
      have := (abs_le.mp hy).1
      linarith
    rw [abs_of_pos (lt_trans zero_lt_one hyLower)]
    exact hyLower

/-- A flat lower-exterior patch occupied above its graph. -/
def lowerExteriorPatch (a b : ℝ) (hab : a < b) : GraphPatch where
  a := a
  b := b
  base := -2
  graph := fun _ => -3
  lowerBound := -4
  upperBound := -2
  zone := .exterior
  side := .above
  a_lt_b := hab
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := le_rfl
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    rintro p ⟨_hx, _hyLower, hyUpper⟩
    change 1 < |p.2|
    rw [abs_of_neg (by linarith)]
    linarith

def lowerExteriorTube (a b : ℝ) (hab : a < b) :
    (lowerExteriorPatch a b hab).Tube where
  radius := 1 / 4
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [lowerExteriorPatch]
  graph_lower_clearance := by intros; norm_num [lowerExteriorPatch]
  graph_upper_clearance := by intros; norm_num [lowerExteriorPatch]
  closed_tube_in_zone := by
    intro x _hx y hy
    change 1 < |y|
    change |y - (-3)| ≤ 1 / 4 at hy
    have hyUpper : y < -1 := by
      have := (abs_le.mp hy).2
      linarith
    rw [abs_of_neg (lt_trans hyUpper (by norm_num))]
    linarith

/-- Two separated interior patches with opposite occupied sides. -/
def interiorData : TwoPatchData where
  first := interiorPatch (-2) (-1) (by norm_num)
  second := interiorAbovePatch 1 2 (by norm_num)
  horizontal_disjoint := by
    rw [Set.disjoint_left]
    rintro x hx hy
    rcases hx with ⟨_hxLower, hxUpper⟩
    rcases hy with ⟨hyLower, _hyUpper⟩
    norm_num [interiorPatch, interiorAbovePatch] at hxUpper hyLower
    linarith

/-- Two separated exterior patches with opposite occupied sides. -/
def exteriorData : TwoPatchData where
  first := exteriorPatch (-2) (-1) (by norm_num)
  second := lowerExteriorPatch 1 2 (by norm_num)
  horizontal_disjoint := by
    rw [Set.disjoint_left]
    rintro x hx hy
    rcases hx with ⟨_hxLower, hxUpper⟩
    rcases hy with ⟨hyLower, _hyUpper⟩
    norm_num [exteriorPatch, lowerExteriorPatch] at hxUpper hyLower
    linarith

/-- The normalized bump itself gives a concrete compactly supported primary
vertical variation on any patch. -/
def normalizedPrimary (P : GraphPatch) : PrimaryVariation P where
  toFun := P.compensationBump
  contDiff := P.compensationBump_contDiff.of_le (by
    apply WithTop.coe_le_coe.mpr
    exact le_top)
  tsupport_subset := P.tsupport_compensationBump_subset

/-- Fully instantiated opposite-side density-one first checkpoint. -/
noncomputable def interiorApplication (lam : ℝ) (hlam : 1 < lam) :=
  twoPatch_checkpoint_with_firstVariation hlam interiorData
    (normalizedPrimary interiorData.first)
    (interiorTube (-2) (-1) (by norm_num))
    (interiorAboveTube 1 2 (by norm_num))

/-- Fully instantiated opposite-side exterior checkpoint for every `lam > 1`. -/
noncomputable def exteriorApplication (lam : ℝ) (hlam : 1 < lam) :=
  twoPatch_checkpoint_with_firstVariation hlam exteriorData
    (normalizedPrimary exteriorData.first)
    (exteriorTube (-2) (-1) (by norm_num))
    (lowerExteriorTube 1 2 (by norm_num))

end Examples

end CMVTwoPatchGraphVariation
