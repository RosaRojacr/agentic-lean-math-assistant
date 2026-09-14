import CMVFiniteBandCostAssembly
import CMVLocalGraphSurgery

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement
namespace HeightGraphProjection

/-- Which endpoint boundary is modeled: a left endpoint occupies its closed
supergraph, while a right endpoint occupies its closed subgraph. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

/-- The three open height zones on which the strip density is constant. -/
inductive Zone where
  | belowStrip
  | insideStrip
  | aboveStrip
  deriving DecidableEq

namespace Zone

/-- Exact strip-density weight of an open height zone. -/
def weight (zone : Zone) (lam : ℝ) : ℝ :=
  match zone with
  | .belowStrip => lam
  | .insideStrip => 1
  | .aboveStrip => lam

/-- Membership of a height in one open constant-density zone. -/
def Contains (zone : Zone) (y : ℝ) : Prop :=
  match zone with
  | .belowStrip => y < -1
  | .insideStrip => -1 < y ∧ y < 1
  | .aboveStrip => 1 < y

lemma stripDensity_eq_weight {zone : Zone} {lam y x : ℝ}
    (hy : zone.Contains y) :
    StripDensity lam (x, y) = zone.weight lam := by
  cases zone with
  | belowStrip =>
      change y < -1 at hy
      have hyneg : y < 0 := lt_trans hy (by norm_num)
      have habs : 1 < |y| := by
        rw [abs_of_neg hyneg]
        linarith
      simp [weight, StripDensity, not_le.mpr habs]
  | insideStrip =>
      change -1 < y ∧ y < 1 at hy
      have habs : |y| ≤ 1 := by rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
      simp [weight, StripDensity, habs]
  | aboveStrip =>
      change 1 < y at hy
      have habs : 1 < |y| := by
        rw [abs_of_pos (lt_trans zero_lt_one hy)]
        exact hy
      simp [weight, StripDensity, not_le.mpr habs]

lemma weight_pos {zone : Zone} {lam : ℝ} (hlam : 1 < lam) :
    0 < zone.weight lam := by
  cases zone <;> simp [weight, lt_trans zero_lt_one hlam]

end Zone

/-- A compact `C¹` height-graph restriction together with its exact closed
one-sided carrier model in a protected horizontal tube.  The model deliberately
uses non-strict inequalities because `Region.carrier` is closed. -/
structure Patch (lam : ℝ) (E : Set PlanePoint) where
  a : ℝ
  b : ℝ
  graph : ℝ → ℝ
  side : Side
  zone : Zone
  a_lt_b : a < b
  graph_contDiff : ContDiff ℝ 1 graph
  radius : ℝ
  radius_pos : 0 < radius
  carrier_model : ∀ q : PlanePoint,
    q.2 ∈ Ioo a b → |q.1 - graph q.2| < radius →
      (q ∈ E ↔ match side with
        | .left => graph q.2 ≤ q.1
        | .right => q.1 ≤ graph q.2)
  height_in_zone : ∀ y ∈ Ioo a b, zone.Contains y


namespace Region

/-- Endpoint graphs are continuous for every finite endpoint index. -/
lemma continuous_indexedGraphValue (R : Region) (q : GraphIndex R) :
    Continuous (R.indexedGraphValue q) := by
  rcases q with ⟨i, j, side⟩
  cases side with
  | false => simpa only [Region.indexedGraphValue_left] using R.left_continuous i j
  | true => simpa only [Region.indexedGraphValue_right] using R.right_continuous i j

/-- On a compact subinterval of an open band, one endpoint graph has a
uniform positive horizontal separation from every other endpoint graph. -/
lemma exists_uniform_indexedGraphValue_clearance
    (R : Region) (i : Fin R.bandCount)
    (q : Fin (R.componentCount i) × Bool) {a b : ℝ}
    (hsub : Icc a b ⊆ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ y ∈ Icc a b, ∀ r : Fin (R.componentCount i) × Bool, r ≠ q →
        rho ≤ |R.indexedGraphValue ⟨i, r⟩ y -
          R.indexedGraphValue ⟨i, q⟩ y| := by
  classical
  let S : Finset (Fin (R.componentCount i) × Bool) := Finset.univ.erase q
  have hS : S.Nonempty := by
    cases hside : q.2 with
    | false =>
        refine ⟨(q.1, true), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
        intro h
        have hsnd := congrArg Prod.snd h
        rw [hside] at hsnd
        exact Bool.noConfusion hsnd
    | true =>
        refine ⟨(q.1, false), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
        intro h
        have hsnd := congrArg Prod.snd h
        rw [hside] at hsnd
        exact Bool.noConfusion hsnd
  let d : ℝ → ℝ := fun y =>
    S.inf' hS (fun r => |R.indexedGraphValue ⟨i, r⟩ y -
      R.indexedGraphValue ⟨i, q⟩ y|)
  have hdcont : Continuous d := by
    dsimp only [d]
    apply Continuous.finset_inf'_apply hS
    intro r _
    exact ((continuous_indexedGraphValue R ⟨i, r⟩).sub
      (continuous_indexedGraphValue R ⟨i, q⟩)).abs
  have hdpos : ∀ y ∈ Icc a b, 0 < d y := by
    intro y hy
    dsimp only [d]
    rw [Finset.lt_inf'_iff]
    intro r hr
    apply abs_pos.mpr
    exact sub_ne_zero.mpr
      ((R.indexedGraphValue_injective i (hsub hy)).ne
        (Finset.ne_of_mem_erase hr))
  obtain ⟨rho, hrho, hbound⟩ :=
    isCompact_Icc.exists_forall_le' hdcont.continuousOn hdpos
  refine ⟨rho, hrho, ?_⟩
  intro y hy r hrq
  exact (hbound y hy).trans
    (Finset.inf'_le _ (show r ∈ S by simp [S, hrq]))


/-- A compact piece of a left endpoint has a uniform horizontal tube in which
the literal region is exactly the closed supergraph. -/
lemma exists_leftGraph_horizontalTube
    (R : Region) (i : Fin R.bandCount) (j : Fin (R.componentCount i))
    {a b : ℝ}
    (hsub : Icc a b ⊆ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ y ∈ Icc a b, ∀ x : ℝ,
      |x - R.left i j y| < rho →
        ((x, y) ∈ R.carrier ↔ R.left i j y ≤ x) := by
  obtain ⟨rho, hrho, hclear⟩ :=
    exists_uniform_indexedGraphValue_clearance R i (j, false) hsub
  refine ⟨rho, hrho, ?_⟩
  intro y hy x hx
  have hyOpen := hsub hy
  change x ∈ horizontalSection R.carrier y ↔ R.left i j y ≤ x
  rw [R.horizontalSection_carrier_of_mem_Ioo i hyOpen]
  constructor
  · intro hxf
    rw [Region.fiber, mem_iUnion] at hxf
    rcases hxf with ⟨k, hxk⟩
    by_cases hkj : k = j
    · simpa only [hkj] using hxk.1
    · rcases lt_or_gt_of_ne hkj with hkj' | hjk'
      · have hgap := R.components_strict i hkj' y hyOpen
        have hc := hclear y hy (k, true) (by
          intro heq
          exact hkj (congrArg Prod.fst heq))
        change rho ≤ |R.right i k y - R.left i j y| at hc
        rw [abs_of_neg (sub_neg.mpr hgap)] at hc
        rcases abs_lt.mp hx with ⟨hxL, _hxR⟩
        linarith [hxk.2]
      · have hgap := R.components_strict i hjk' y hyOpen
        have hw := R.width_pos i j y hyOpen
        linarith [hxk.1]
  · intro hxleft
    rw [Region.fiber, mem_iUnion]
    refine ⟨j, hxleft, ?_⟩
    have hw := R.width_pos i j y hyOpen
    have hc := hclear y hy (j, true) (by simp)
    change rho ≤ |R.right i j y - R.left i j y| at hc
    rw [abs_of_pos (sub_pos.mpr hw)] at hc
    rcases abs_lt.mp hx with ⟨_hxL, hxR⟩
    linarith

/-- A compact piece of a right endpoint has a uniform horizontal tube in which
the literal region is exactly the closed subgraph. -/
lemma exists_rightGraph_horizontalTube
    (R : Region) (i : Fin R.bandCount) (j : Fin (R.componentCount i))
    {a b : ℝ}
    (hsub : Icc a b ⊆ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ y ∈ Icc a b, ∀ x : ℝ,
      |x - R.right i j y| < rho →
        ((x, y) ∈ R.carrier ↔ x ≤ R.right i j y) := by
  obtain ⟨rho, hrho, hclear⟩ :=
    exists_uniform_indexedGraphValue_clearance R i (j, true) hsub
  refine ⟨rho, hrho, ?_⟩
  intro y hy x hx
  have hyOpen := hsub hy
  change x ∈ horizontalSection R.carrier y ↔ x ≤ R.right i j y
  rw [R.horizontalSection_carrier_of_mem_Ioo i hyOpen]
  constructor
  · intro hxf
    rw [Region.fiber, mem_iUnion] at hxf
    rcases hxf with ⟨k, hxk⟩
    by_cases hkj : k = j
    · simpa only [hkj] using hxk.2
    · rcases lt_or_gt_of_ne hkj with hkj' | hjk'
      · have hgap := R.components_strict i hkj' y hyOpen
        have hw := R.width_pos i j y hyOpen
        linarith [hxk.2]
      · have hgap := R.components_strict i hjk' y hyOpen
        have hc := hclear y hy (k, false) (by
          intro heq
          exact hkj (congrArg Prod.fst heq))
        change rho ≤ |R.left i k y - R.right i j y| at hc
        rw [abs_of_pos (sub_pos.mpr hgap)] at hc
        rcases abs_lt.mp hx with ⟨_hxL, hxR⟩
        linarith [hxk.1]
  · intro hxright
    rw [Region.fiber, mem_iUnion]
    refine ⟨j, ?_, hxright⟩
    have hw := R.width_pos i j y hyOpen
    have hc := hclear y hy (j, false) (by simp)
    change rho ≤ |R.left i j y - R.right i j y| at hc
    rw [abs_of_neg (sub_neg.mpr hw)] at hc
    rcases abs_lt.mp hx with ⟨hxL, _hxR⟩
    linarith


/-- The selected endpoint is `C¹` on its open height band. -/
lemma contDiffOn_indexedGraphValue (R : Region) (q : GraphIndex R) :
    ContDiffOn ℝ 1 (R.indexedGraphValue q)
      (Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ)) := by
  rcases q with ⟨i, j, side⟩
  cases side with
  | false => simpa only [Region.indexedGraphValue_left] using R.left_contDiffOn i j
  | true => simpa only [Region.indexedGraphValue_right] using R.right_contDiffOn i j

/-- Every compact restriction of an actual finite-band endpoint graph admits a
global `C¹` representative and an exact one-sided model of the literal closed
carrier.  This is the bridge from `Region` to tangent projection patches. -/
theorem exists_heightGraphPatch
    (R : Region) (lam : ℝ) (q : GraphIndex R) {a b : ℝ}
    (hab : a < b)
    (hsub : Icc a b ⊆
      Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ))
    (zone : Zone)
    (hzone : ∀ y ∈ Ioo a b, zone.Contains y) :
    ∃ P : Patch lam R.carrier,
      P.a = a ∧ P.b = b ∧
      P.side = (if q.2.2 then .right else .left) ∧
      P.zone = zone ∧
      Set.EqOn P.graph (R.indexedGraphValue q) (Icc a b) := by
  rcases q with ⟨i, j, side⟩
  cases side with
  | false =>
      have hnhd :
          Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∈ 𝓝ˢ (Icc a b) :=
        isOpen_Ioo.mem_nhdsSet.2 hsub
      obtain ⟨g, hgC1, _happrox, hgeq, _hsupport⟩ :=
        (R.left_continuous i j).exists_contDiff_approx_and_eqOn
          1 continuous_const (fun _ => zero_lt_one) isClosed_Icc hnhd
          (R.left_contDiffOn i j)
      obtain ⟨rho, hrho, htube⟩ :=
        exists_leftGraph_horizontalTube R i j hsub
      let P : Patch lam R.carrier := {
        a := a
        b := b
        graph := g
        side := Side.left
        zone := zone
        a_lt_b := hab
        graph_contDiff := hgC1
        radius := rho
        radius_pos := hrho
        carrier_model := by
          intro p hpheight hpnear
          have hy : p.2 ∈ Icc a b := ⟨hpheight.1.le, hpheight.2.le⟩
          have heq : g p.2 = R.left i j p.2 := hgeq hy
          have hmodel := htube p.2 hy p.1 (by simpa only [heq] using hpnear)
          simpa only [heq] using hmodel
        height_in_zone := hzone }
      refine ⟨P, rfl, rfl, ?_, rfl, ?_⟩
      · simp [P]
      · intro y hy
        exact hgeq hy
  | true =>
      have hnhd :
          Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∈ 𝓝ˢ (Icc a b) :=
        isOpen_Ioo.mem_nhdsSet.2 hsub
      obtain ⟨g, hgC1, _happrox, hgeq, _hsupport⟩ :=
        (R.right_continuous i j).exists_contDiff_approx_and_eqOn
          1 continuous_const (fun _ => zero_lt_one) isClosed_Icc hnhd
          (R.right_contDiffOn i j)
      obtain ⟨rho, hrho, htube⟩ :=
        exists_rightGraph_horizontalTube R i j hsub
      let P : Patch lam R.carrier := {
        a := a
        b := b
        graph := g
        side := Side.right
        zone := zone
        a_lt_b := hab
        graph_contDiff := hgC1
        radius := rho
        radius_pos := hrho
        carrier_model := by
          intro p hpheight hpnear
          have hy : p.2 ∈ Icc a b := ⟨hpheight.1.le, hpheight.2.le⟩
          have heq : g p.2 = R.right i j p.2 := hgeq hy
          have hmodel := htube p.2 hy p.1 (by simpa only [heq] using hpnear)
          simpa only [heq] using hmodel
        height_in_zone := hzone }
      refine ⟨P, rfl, rfl, ?_, rfl, ?_⟩
      · simp [P]
      · intro y hy
        exact hgeq hy

end Region

namespace Patch

variable {lam : ℝ} {E : Set PlanePoint}

/-- The protected open tube around the actual height graph. -/
def tube (P : Patch lam E) : Set PlanePoint :=
  {q | q.2 ∈ Ioo P.a P.b ∧ |q.1 - P.graph q.2| < P.radius}

/-- Restrict a protected tube without changing its graph, side, or density
zone. -/
def withRadius (P : Patch lam E) (r : ℝ) (hr : 0 < r)
    (hrle : r ≤ P.radius) : Patch lam E where
  a := P.a
  b := P.b
  graph := P.graph
  side := P.side
  zone := P.zone
  a_lt_b := P.a_lt_b
  graph_contDiff := P.graph_contDiff
  radius := r
  radius_pos := hr
  carrier_model := by
    intro q hq hnear
    exact P.carrier_model q hq (hnear.trans_le hrle)
  height_in_zone := P.height_in_zone

@[simp] theorem withRadius_tube
    (P : Patch lam E) (r : ℝ) (hr : 0 < r) (hrle : r ≤ P.radius) :
    (P.withRadius r hr hrle).tube =
      {q | q.2 ∈ Ioo P.a P.b ∧ |q.1 - P.graph q.2| < r} := rfl
/-- Tangent frame before exchanging graph and source coordinates. -/
def rawFrame (P : Patch lam E) (y₀ : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  match P.side with
  | .right => graphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀)
  | .left => supergraphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀)


/-- Tangent coordinates, followed by coordinate exchange back to the original
CMV plane.  Negative local normal points into the declared occupied side. -/
def frame (P : Patch lam E) (y₀ : ℝ) : EuclideanPlane ≃ᵢ EuclideanPlane :=
  (P.rawFrame y₀).trans euclideanGraphCoordinateSwap

@[simp] theorem euclideanRigidMap_coordinateSwap (q : PlanePoint) :
    euclideanRigidMap euclideanGraphCoordinateSwap q = (q.2, q.1) := by
  rfl

@[simp] theorem euclideanRigidMap_frame_right
    (P : Patch lam E) (hside : P.side = .right) (y₀ : ℝ) (q : PlanePoint) :
    euclideanRigidMap (P.frame y₀) q =
      let z := euclideanRigidMap
        (graphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀)) q
      (z.2, z.1) := by
  rw [frame, rawFrame, hside]
  rfl

@[simp] theorem euclideanRigidMap_frame_left
    (P : Patch lam E) (hside : P.side = .left) (y₀ : ℝ) (q : PlanePoint) :
    euclideanRigidMap (P.frame y₀) q =
      let z := euclideanRigidMap
        (supergraphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀)) q
      (z.2, z.1) := by
  rw [frame, rawFrame, hside]
  rfl


/-- `C¹` regularity already gives uniform tangent cones on compact intervals;
no second derivative or curvature bound is needed. -/
theorem exists_uniform_tangent_remainder_on_Icc_C1
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {a b ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₀ ∈ Icc a b, ∀ x ∈ Icc a b,
      |x - x₀| < δ →
        |f x - f x₀ - deriv f x₀ * (x - x₀)| ≤ ε * |x - x₀| := by
  have hf' : ContDiff ℝ (0 + 1) f := by simpa using hf
  have hderiv : Continuous (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 0)).mp hf').2.2.continuous
  have huc : UniformContinuousOn (deriv f) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hderiv.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hdist
  apply abs_sub_tangent_le_of_deriv_close
    (hf.differentiable (by norm_num))
    (a := min x₀ x) (b := max x₀ x)
    (by simp) (by simp)
  intro y hy
  have hyI : y ∈ Icc a b :=
    ordConnected_Icc.uIcc_subset hx₀ hx hy
  have hydist : |y - x₀| < δ := by
    rw [← Real.dist_eq, dist_comm]
    exact (Real.dist_left_le_of_mem_uIcc hy).trans_lt
      (by simpa only [Real.dist_eq, abs_sub_comm] using hdist)
  have hc : |deriv f y - deriv f x₀| < ε := by
    simpa only [Real.dist_eq] using
      (hclose y hyI x₀ hx₀ (by simpa only [Real.dist_eq] using hydist))
  exact hc.le

/-- The source-height displacement of either oriented tangent frame. -/
theorem abs_rawFrame_fst_sub_le_div_speed
    (P : Patch lam E) (y₀ : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (P.rawFrame y₀) p).1 - y₀| ≤
      |p.1| / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + |p.2| := by
  cases hside : P.side with
  | left =>
      simpa only [rawFrame, hside] using
        abs_supergraphTangentFrame_fst_sub_le_div_speed
          y₀ (P.graph y₀) (deriv P.graph y₀) p
  | right =>
      simpa only [rawFrame, hside] using
        abs_graphTangentFrame_fst_sub_le_div_speed
          y₀ (P.graph y₀) (deriv P.graph y₀) p

/-- Absolute normal displacement in either occupied-side orientation. -/
theorem abs_rawFrame_normal_displacement
    (P : Patch lam E) (y₀ : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (P.rawFrame y₀) p).2 - P.graph y₀ -
        deriv P.graph y₀ *
          ((euclideanRigidMap (P.rawFrame y₀) p).1 - y₀)| =
      |p.2| * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by
  cases hside : P.side with
  | left =>
      rw [rawFrame, hside, supergraphTangentFrame_normal_displacement,
        abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
  | right =>
      rw [rawFrame, hside, graphTangentFrame_normal_displacement,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- A graph-speed-scaled tangent box remains in the protected original-coordinate
tube. -/
theorem tangentProjectionBox_subset_tube_div_speed
    (P : Patch lam E) (y₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ y,
      |y - y₀| ≤ h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho →
      |P.graph y - P.graph y₀ -
          deriv P.graph y₀ * (y - y₀)| ≤ ε * |y - y₀|)
    (hsmall : ε *
      (h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho) < rho)
    (hleft : h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho <
      y₀ - P.a)
    (hright : h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho <
      P.b - y₀)
    (htube : 3 * rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) <
      P.radius) :
    rigidProjectionBox (P.frame y₀) (-h) h 0 rho ⊆ P.tube := by
  rintro _ ⟨p, hp, rfl⟩
  change p.1 ∈ Icc (-h) h ∧
    p.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hp
  have hp₁ : |p.1| ≤ h := abs_le.mpr hp.1
  have hp₂ : |p.2| ≤ 2 * rho := by
    rw [abs_le]
    constructor <;> nlinarith [hp.2.1, hp.2.2]
  let z := euclideanRigidMap (P.rawFrame y₀) p
  have hspeed : 0 < Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by positivity
  have hdy : |z.1 - y₀| ≤
      h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho :=
    (P.abs_rawFrame_fst_sub_le_div_speed y₀ p).trans
      (add_le_add (div_le_div_of_nonneg_right hp₁ hspeed.le) hp₂)
  have hzframe :
      euclideanRigidMap (P.frame y₀) p = (z.2, z.1) := by
    change euclideanRigidMap ((P.rawFrame y₀).trans
      euclideanGraphCoordinateSwap) p = (z.2, z.1)
    rfl
  rw [hzframe]
  refine ⟨?_, ?_⟩
  · rw [mem_Ioo]
    rcases abs_le.mp hdy with ⟨hdyL, hdyR⟩
    constructor <;> linarith
  · have hres0 := htangent z.1 hdy
    have hres :
        |P.graph z.1 - P.graph y₀ -
            deriv P.graph y₀ * (z.1 - y₀)| < rho := by
      exact hres0.trans_lt
        ((mul_le_mul_of_nonneg_left hdy hε).trans_lt hsmall)
    let normal := z.2 - P.graph y₀ - deriv P.graph y₀ * (z.1 - y₀)
    let residual :=
      P.graph z.1 - P.graph y₀ - deriv P.graph y₀ * (z.1 - y₀)
    have hnormal :
        |normal| = |p.2| * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by
      simpa only [normal, z] using P.abs_rawFrame_normal_displacement y₀ p
    have hres' :
        |residual| < rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) :=
      hres.trans_le (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show 1 ≤ Real.sqrt (1 + (deriv P.graph y₀) ^ 2) by
            nlinarith [Real.sq_sqrt
              (show 0 ≤ 1 + (deriv P.graph y₀) ^ 2 by positivity),
              Real.sqrt_nonneg (1 + (deriv P.graph y₀) ^ 2)])
          hrho.le)
    have hdecomp : z.2 - P.graph z.1 = normal - residual := by
      dsimp only [normal, residual]
      ring
    rw [hdecomp]
    calc
      |normal - residual| ≤ |normal| + |residual| := abs_sub _ _
      _ = |p.2| * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) +
          |residual| := by rw [hnormal]
      _ < 2 * rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) +
          rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) :=
        add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right hp₂ hspeed.le) hres'
      _ = 3 * rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by ring
      _ < P.radius := htube

/-- The same tangent box is localized in a prescribed source-height cell. -/
theorem tangentProjectionBox_subset_snd_Ioo
    (P : Patch lam E) (y₀ l r h rho : ℝ)
    (hfit : h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho <
      min (y₀ - l) (r - y₀)) :
    rigidProjectionBox (P.frame y₀) (-h) h 0 rho ⊆
      {q : PlanePoint | q.2 ∈ Ioo l r} := by
  rintro _ ⟨p, hp, rfl⟩
  change p.1 ∈ Icc (-h) h ∧
    p.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hp
  have hp₁ : |p.1| ≤ h := abs_le.mpr hp.1
  have hp₂ : |p.2| ≤ 2 * rho := by
    rw [abs_le]
    constructor <;> nlinarith [hp.2.1, hp.2.2]
  let z := euclideanRigidMap (P.rawFrame y₀) p
  have hspeed : 0 < Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by positivity
  have hdy : |z.1 - y₀| ≤
      h / Real.sqrt (1 + (deriv P.graph y₀) ^ 2) + 2 * rho :=
    (P.abs_rawFrame_fst_sub_le_div_speed y₀ p).trans
      (add_le_add (div_le_div_of_nonneg_right hp₁ hspeed.le) hp₂)
  have hzframe :
      euclideanRigidMap (P.frame y₀) p = (z.2, z.1) := by
    change euclideanRigidMap ((P.rawFrame y₀).trans
      euclideanGraphCoordinateSwap) p = (z.2, z.1)
    rfl
  rw [hzframe]
  change z.1 ∈ Ioo l r
  rw [lt_min_iff] at hfit
  rcases abs_le.mp hdy with ⟨hdyL, hdyR⟩
  constructor <;> linarith
/-- A tangent box satisfying the residual estimate becomes a projection patch
on the literal closed carrier.  Strict collar inequalities are converted to
the non-strict local carrier model only after the geometry is proved. -/
noncomputable def tangentPatch
    (P : Patch lam E) (y₀ h rho : ℝ) (hrho : 0 < rho)
    (hresidual : ∀ p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
      |P.graph (euclideanRigidMap (P.rawFrame y₀) p).1 - P.graph y₀ -
          deriv P.graph y₀ *
            ((euclideanRigidMap (P.rawFrame y₀) p).1 - y₀)| <
        rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2))
    (hwindow : rigidProjectionBox (P.frame y₀) (-h) h 0 rho ⊆ P.tube) :
    RigidProjectionPatch lam E where
  frame := P.frame y₀
  a := -h
  b := h
  y₀ := 0
  rho := rho
  weight := P.zone.weight lam
  rho_pos := hrho
  lower_collar := by
    rintro _ ⟨p, hp, rfl⟩
    change p.1 ∈ Icc (-h) h ∧
      p.2 ∈ Icc (0 - 2 * rho) (0 - rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    have hpbox :
        euclideanRigidMap (P.frame y₀) p ∈
          rigidProjectionBox (P.frame y₀) (-h) h 0 rho := by
      exact ⟨p, ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩, rfl⟩
    have htube := hwindow hpbox
    let z := euclideanRigidMap (P.rawFrame y₀) p
    have hq :
        euclideanRigidMap (P.frame y₀) p = (z.2, z.1) := by
      change euclideanRigidMap ((P.rawFrame y₀).trans
        euclideanGraphCoordinateSwap) p = (z.2, z.1)
      rfl
    rw [hq] at htube ⊢
    have hres := hresidual p hpfull
    have hspeed : 0 < Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by positivity
    cases hside : P.side with
    | left =>
        have hnormal := supergraphTangentFrame_normal_displacement
          y₀ (P.graph y₀) (deriv P.graph y₀) p
        have hzraw :
            P.rawFrame y₀ =
              supergraphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀) := by
          simp [rawFrame, hside]
        rw [hzraw] at hres
        have hpnormal :
            rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) ≤
              -p.2 * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hspeed.le
          linarith [hp.2.2]
        have hin : P.graph z.1 < z.2 := by
          dsimp only [z]
          rw [hzraw]
          linarith [le_abs_self
            (P.graph
                (euclideanRigidMap
                  (supergraphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 -
              P.graph y₀ -
              deriv P.graph y₀ *
                ((euclideanRigidMap
                  (supergraphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 - y₀))]
        exact (P.carrier_model (z.2, z.1) htube.1 htube.2).2
          (by simpa only [hside] using hin.le)
    | right =>
        have hnormal := graphTangentFrame_normal_displacement
          y₀ (P.graph y₀) (deriv P.graph y₀) p
        have hzraw :
            P.rawFrame y₀ =
              graphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀) := by
          simp [rawFrame, hside]
        rw [hzraw] at hres
        have hpnormal :
            p.2 * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) ≤
              -rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) :=
          mul_le_mul_of_nonneg_right hp.2.2 hspeed.le
        have hin : z.2 < P.graph z.1 := by
          dsimp only [z]
          rw [hzraw]
          linarith [neg_abs_le
            (P.graph
                (euclideanRigidMap
                  (graphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 -
              P.graph y₀ -
              deriv P.graph y₀ *
                ((euclideanRigidMap
                  (graphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 - y₀))]
        exact (P.carrier_model (z.2, z.1) htube.1 htube.2).2
          (by simpa only [hside] using hin.le)
  upper_collar := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hcarrier
    change p.1 ∈ Icc (-h) h ∧
      p.2 ∈ Icc (0 + rho) (0 + 2 * rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
    have hpbox :
        euclideanRigidMap (P.frame y₀) p ∈
          rigidProjectionBox (P.frame y₀) (-h) h 0 rho := by
      exact ⟨p, ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩, rfl⟩
    have htube := hwindow hpbox
    let z := euclideanRigidMap (P.rawFrame y₀) p
    have hq :
        euclideanRigidMap (P.frame y₀) p = (z.2, z.1) := by
      change euclideanRigidMap ((P.rawFrame y₀).trans
        euclideanGraphCoordinateSwap) p = (z.2, z.1)
      rfl
    rw [hq] at htube hcarrier
    have hres := hresidual p hpfull
    have hspeed : 0 < Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by positivity
    cases hside : P.side with
    | left =>
        have hnormal := supergraphTangentFrame_normal_displacement
          y₀ (P.graph y₀) (deriv P.graph y₀) p
        have hzraw :
            P.rawFrame y₀ =
              supergraphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀) := by
          simp [rawFrame, hside]
        rw [hzraw] at hres
        have hpnormal :
            -p.2 * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) ≤
              -rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hspeed.le
          linarith [hp.2.1]
        have hout : z.2 < P.graph z.1 := by
          dsimp only [z]
          rw [hzraw]
          linarith [neg_abs_le
            (P.graph
                (euclideanRigidMap
                  (supergraphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 -
              P.graph y₀ -
              deriv P.graph y₀ *
                ((euclideanRigidMap
                  (supergraphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 - y₀))]
        have hin :=
          (P.carrier_model (z.2, z.1) htube.1 htube.2).1 hcarrier
        simp only [hside] at hin
        linarith
    | right =>
        have hnormal := graphTangentFrame_normal_displacement
          y₀ (P.graph y₀) (deriv P.graph y₀) p
        have hzraw :
            P.rawFrame y₀ =
              graphTangentFrame y₀ (P.graph y₀) (deriv P.graph y₀) := by
          simp [rawFrame, hside]
        rw [hzraw] at hres
        have hpnormal :
            rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) ≤
              p.2 * Real.sqrt (1 + (deriv P.graph y₀) ^ 2) :=
          mul_le_mul_of_nonneg_right hp.2.1 hspeed.le
        have hout : P.graph z.1 < z.2 := by
          dsimp only [z]
          rw [hzraw]
          linarith [le_abs_self
            (P.graph
                (euclideanRigidMap
                  (graphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 -
              P.graph y₀ -
              deriv P.graph y₀ *
                ((euclideanRigidMap
                  (graphTangentFrame y₀ (P.graph y₀)
                    (deriv P.graph y₀)) p).1 - y₀))]
        have hin :=
          (P.carrier_model (z.2, z.1) htube.1 htube.2).1 hcarrier
        simp only [hside] at hin
        linarith
  density_lower := by
    intro q hq
    have htube := hwindow hq
    rw [P.zone.stripDensity_eq_weight (P.height_in_zone q.2 htube.1)]

@[simp] theorem tangentPatch_window
    (P : Patch lam E) (y₀ h rho : ℝ) (hrho : 0 < rho)
    (hresidual : ∀ p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
      |P.graph (euclideanRigidMap (P.rawFrame y₀) p).1 - P.graph y₀ -
          deriv P.graph y₀ *
            ((euclideanRigidMap (P.rawFrame y₀) p).1 - y₀)| <
        rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2))
    (hwindow : rigidProjectionBox (P.frame y₀) (-h) h 0 rho ⊆ P.tube) :
    (P.tangentPatch y₀ h rho hrho hresidual hwindow).window =
      rigidProjectionBox (P.frame y₀) (-h) h 0 rho := rfl

@[simp] theorem tangentPatch_payoff
    (P : Patch lam E) (y₀ h rho : ℝ) (hrho : 0 < rho)
    (hresidual : ∀ p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
      |P.graph (euclideanRigidMap (P.rawFrame y₀) p).1 - P.graph y₀ -
          deriv P.graph y₀ *
            ((euclideanRigidMap (P.rawFrame y₀) p).1 - y₀)| <
        rho * Real.sqrt (1 + (deriv P.graph y₀) ^ 2))
    (hwindow : rigidProjectionBox (P.frame y₀) (-h) h 0 rho ⊆ P.tube) :
    (P.tangentPatch y₀ h rho hrho hresidual hwindow).payoff =
      ENNReal.ofReal (P.zone.weight lam) * ENNReal.ofReal (h - (-h)) := rfl

/-- Exact weighted speed integral of the compact height-graph restriction. -/
def weightedLength (P : Patch lam E) : ℝ :=
  P.zone.weight lam *
    ∫ y in P.a..P.b, Real.sqrt (1 + deriv P.graph y ^ 2)

set_option maxHeartbeats 800000 in
-- The quantitative mesh algebra needs more than Lean's default heartbeat cap.
/-- A finite equal-height mesh of complete tangent windows exhausts every
compact `C¹` height graph from below.  Windows are disjoint in actual source
height, remain in the literal carrier's protected tube, and have finite total
projection-defect coefficient. -/
theorem exists_pairwiseDisjoint_tangentPatches_payoff_ge
    (P : Patch lam E) (hlam : 1 < lam) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (Q : Fin N → RigidProjectionPatch lam E),
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      (∀ i, (Q i).window ⊆ P.tube) ∧
      (∑ i, (Q i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal (P.weightedLength - η) ≤ ∑ i, (Q i).payoff := by
  let F : ℝ → ℝ := fun y =>
    Real.sqrt (1 + (deriv P.graph y) ^ 2)
  let w := P.zone.weight lam
  have hderiv : Continuous (deriv P.graph) := by
    have hP : ContDiff ℝ (0 + 1) P.graph := by
      simpa using P.graph_contDiff
    exact ((contDiff_succ_iff_deriv (n := 0)).mp hP).2.2.continuous
  have hF : Continuous F :=
    (continuous_const.add (hderiv.pow 2)).sqrt
  have hw : 0 < w := P.zone.weight_pos hlam
  obtain ⟨M₀, hM₀⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hF.continuousOn)
  let M := max 1 M₀
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hFM : ∀ y ∈ Icc P.a P.b, F y ≤ M := by
    intro y hy
    exact (hM₀ _ (mem_image_of_mem _ hy)).trans (le_max_right _ _)
  let κ := min (1 / 2 : ℝ)
    (η / (4 * w * M * (P.b - P.a)))
  have hκ : 0 < κ := by
    dsimp [κ]
    exact lt_min (by norm_num)
      (div_pos hη (mul_pos (mul_pos (by positivity) hM)
        (sub_pos.mpr P.a_lt_b)))
  have hκhalf : κ ≤ 1 / 2 := min_le_left _ _
  have hκ1 : κ < 1 := hκhalf.trans_lt (by norm_num)
  let ε := κ / (256 * M ^ 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨δ, hδ, hrem⟩ :=
    exists_uniform_tangent_remainder_on_Icc_C1
      (a := P.a - 1) (b := P.b + 1) P.graph P.graph_contDiff hε
  let err := η / (4 * w)
  have herr : 0 < err := by
    dsimp [err]
    positivity
  let σ := min (δ / M) (min (1 / M) P.radius)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact lt_min (div_pos hδ hM)
      (lt_min (div_pos zero_lt_one hM) P.radius_pos)
  obtain ⟨N, hN, hdσ, hRiemann⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral hF P.a_lt_b herr hσ
  let d := (P.b - P.a) / (N : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (sub_pos.mpr P.a_lt_b) (by exact_mod_cast hN)
  have hdδ : d < δ / M := hdσ.trans_le (min_le_left _ _)
  have hd1 : d < 1 / M :=
    hdσ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdT : d < P.radius :=
    hdσ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hMdδ : M * d < δ := by
    apply (lt_div_iff₀' hM).mp
    simpa only [mul_comm] using hdδ
  have hMd1 : M * d < 1 := by
    apply (lt_div_iff₀' hM).mp
    simpa only [mul_comm] using hd1
  let edge : ℕ → ℝ := fun k => P.a + (k : ℝ) * d
  let y₀ : Fin N → ℝ := fun i => edge i + d / 2
  let speed : Fin N → ℝ := fun i => F (y₀ i)
  let h : Fin N → ℝ := fun i => (1 - κ) * speed i * d / 2
  let rho : ℝ := κ * d / (64 * M)
  have hNd : (N : ℝ) * d = P.b - P.a := by
    dsimp [d]
    field_simp
  have hedgeN : edge N = P.b := by
    dsimp [edge]
    rw [hNd]
    ring
  have hy₀_mem (i : Fin N) : y₀ i ∈ Ioo P.a P.b := by
    have hi : (i : ℕ) + 1 ≤ N := i.isLt
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
    have hiN : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hi
    dsimp [y₀, edge]
    constructor
    · nlinarith
    · rw [← hedgeN]
      dsimp [edge]
      nlinarith
  have hspeed_pos (i : Fin N) : 0 < speed i := by
    dsimp [speed, F]
    positivity
  have hspeed_le (i : Fin N) : speed i ≤ M :=
    hFM _ ⟨(hy₀_mem i).1.le, (hy₀_mem i).2.le⟩
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hh (i : Fin N) : 0 < h i := by
    dsimp [h]
    positivity
  have hsharp (i : Fin N) :
      h i / speed i + 2 * rho < d / 2 := by
    have hquot : h i / speed i = (1 - κ) * d / 2 := by
      dsimp [h]
      field_simp [ne_of_gt (hspeed_pos i)]
    have hcoef : 1 / (32 * M) < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ (by positivity : 0 < 32 * M)]
      nlinarith
    have hkrho : 2 * rho < κ * d / 2 := by
      calc
        2 * rho = (κ * d) * (1 / (32 * M)) := by
          dsimp [rho]
          field_simp
          ring
        _ < (κ * d) * (1 / 2) :=
          mul_lt_mul_of_pos_left hcoef (mul_pos hκ hd)
        _ = κ * d / 2 := by ring
    rw [hquot]
    nlinarith
  have hcoarse (i : Fin N) : h i + 2 * rho < M * d := by
    have hrewrite : speed i * (h i / speed i) = h i := by
      field_simp [ne_of_gt (hspeed_pos i)]
    calc
      h i + 2 * rho =
          speed i * (h i / speed i) + 2 * rho := by rw [hrewrite]
      _ ≤ M * (h i / speed i) + M * (2 * rho) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hspeed_le i)
            (div_nonneg (hh i).le (hspeed_pos i).le)
        · exact le_mul_of_one_le_left
            (mul_nonneg (by norm_num) hrho.le) hM1
      _ = M * (h i / speed i + 2 * rho) := by ring
      _ < M * (d / 2) := mul_lt_mul_of_pos_left (hsharp i) hM
      _ < M * d := by nlinarith
  have hspeed_one (i : Fin N) : 1 ≤ speed i := by
    dsimp [speed, F]
    nlinarith [Real.sq_sqrt
      (show 0 ≤ 1 + (deriv P.graph (y₀ i)) ^ 2 by positivity),
      Real.sqrt_nonneg (1 + (deriv P.graph (y₀ i)) ^ 2)]
  have hsharp_le_coarse (i : Fin N) :
      h i / speed i + 2 * rho ≤ h i + 2 * rho := by
    gcongr
    exact div_le_self (hh i).le (hspeed_one i)
  have htangent (i : Fin N) : ∀ y,
      |y - y₀ i| ≤ h i + 2 * rho →
      |P.graph y - P.graph (y₀ i) -
          deriv P.graph (y₀ i) * (y - y₀ i)| ≤
        ε * |y - y₀ i| := by
    intro y hy
    apply hrem (y₀ i)
    · exact ⟨by nlinarith [(hy₀_mem i).1], by nlinarith [(hy₀_mem i).2]⟩
    · rw [abs_le] at hy
      constructor <;>
        nlinarith [hcoarse i, hMd1, (hy₀_mem i).1, (hy₀_mem i).2]
    · exact hy.trans_lt ((hcoarse i).trans hMdδ)
  have hsmall (i : Fin N) : ε * (h i + 2 * rho) < rho := by
    calc
      ε * (h i + 2 * rho) < ε * (M * d) :=
        mul_lt_mul_of_pos_left (hcoarse i) hε
      _ < rho := by
        have heq : rho = 4 * (ε * (M * d)) := by
          dsimp [ε, rho]
          field_simp
          ring
        rw [heq]
        nlinarith [mul_pos hε (mul_pos hM hd)]
  have hwindow (i : Fin N) :
      rigidProjectionBox (P.frame (y₀ i))
          (-(h i)) (h i) 0 rho ⊆ P.tube := by
    apply P.tangentProjectionBox_subset_tube_div_speed
      (y₀ i) (h i) rho ε hrho hε.le
    · intro y hy
      exact htangent i y ((hsharp_le_coarse i).trans' hy)
    · exact (mul_le_mul_of_nonneg_left
        (hsharp_le_coarse i) hε.le).trans_lt (hsmall i)
    · dsimp [y₀, edge]
      have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
      nlinarith [hsharp i]
    · have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by
        exact_mod_cast i.isLt
      dsimp [y₀, edge]
      nlinarith [hsharp i, hNd]
    · calc
        3 * rho * speed i ≤ 3 * rho * M := by
          exact mul_le_mul_of_nonneg_left (hspeed_le i)
            (mul_nonneg (by norm_num) hrho.le)
        _ = 3 * κ * d / 64 := by
          dsimp [rho]
          field_simp
        _ < d := by nlinarith [hκhalf, hd]
        _ < P.radius := hdT
  have hresidual (i : Fin N) :
      ∀ p ∈ Icc (-(h i)) (h i) ×ˢ Icc (-2 * rho) (2 * rho),
        |P.graph (euclideanRigidMap (P.rawFrame (y₀ i)) p).1 -
            P.graph (y₀ i) -
            deriv P.graph (y₀ i) *
              ((euclideanRigidMap (P.rawFrame (y₀ i)) p).1 - y₀ i)| <
          rho * Real.sqrt (1 + (deriv P.graph (y₀ i)) ^ 2) := by
    apply tangentBox_residual_lt_of_bound_div_speed
      P.graph (y₀ i) (deriv P.graph (y₀ i)) (h i) rho ε
      hrho hε.le (euclideanRigidMap (P.rawFrame (y₀ i)))
      (P.abs_rawFrame_fst_sub_le_div_speed (y₀ i))
    · intro y hy
      exact htangent i y ((hsharp_le_coarse i).trans' hy)
    · exact (mul_le_mul_of_nonneg_left
        (hsharp_le_coarse i) hε.le).trans_lt (hsmall i)
  let Q : Fin N → RigidProjectionPatch lam E := fun i =>
    P.tangentPatch (y₀ i) (h i) rho hrho (hresidual i) (hwindow i)
  have hcell (i : Fin N) : (Q i).window ⊆
      {q : PlanePoint | q.2 ∈ Ioo (edge i) (edge ((i : ℕ) + 1))} := by
    dsimp [Q]
    apply P.tangentProjectionBox_subset_snd_Ioo
    rw [lt_min_iff]
    dsimp [y₀, edge]
    norm_num only [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [hsharp i]
  have hpair : Set.Pairwise (Set.univ : Set (Fin N))
      (Function.onFun Disjoint fun i => (Q i).window) := by
    intro i _ j _ hij
    change Disjoint (Q i).window (Q j).window
    rw [Set.disjoint_left]
    intro q hqi hqj
    have hi := hcell i hqi
    have hj := hcell j hqj
    change q.2 ∈ Ioo (edge i) (edge ((i : ℕ) + 1)) at hi
    change q.2 ∈ Ioo (edge j) (edge ((j : ℕ) + 1)) at hj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
    · have hijle : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_iff.mpr hij'
      have hijleR : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ (j : ℕ) := by
        exact_mod_cast hijle
      have hedge : edge ((i : ℕ) + 1) ≤ edge j := by
        dsimp [edge]
        simpa only [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_right hijleR hd.le) P.a
      linarith [hi.2, hj.1, hedge]
    · have hjile : (j : ℕ) + 1 ≤ (i : ℕ) := Nat.succ_le_iff.mpr hji'
      have hjileR : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (i : ℕ) := by
        exact_mod_cast hjile
      have hedge : edge ((j : ℕ) + 1) ≤ edge i := by
        dsimp [edge]
        simpa only [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_right hjileR hd.le) P.a
      linarith [hj.2, hi.1, hedge]
  let S := ∑ i : Fin N, speed i * d
  have hRiemann' :
      ∫ y in P.a..P.b, F y ≤ S + err := by
    calc
      ∫ y in P.a..P.b, F y ≤
          (∑ i : Fin N,
            F (P.a + ((i : ℝ) + 1 / 2) * d) * d) + err := by
        simpa only [d] using hRiemann
      _ = S + err := by
        congr 1
        dsimp [S, speed, y₀, edge]
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        ring
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hspeed_pos i).le hd.le
  have hSle : S ≤ M * (P.b - P.a) := by
    calc
      S ≤ ∑ _i : Fin N, M * d := by
        dsimp [S]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hspeed_le i) hd.le
      _ = (N : ℝ) * (M * d) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = M * (P.b - P.a) := by
        rw [← hNd]
        ring
  have hκbound : κ ≤ η / (4 * w * M * (P.b - P.a)) :=
    min_le_right _ _
  have hden : 0 < 4 * w * M * (P.b - P.a) :=
    mul_pos (mul_pos (by positivity) hM) (sub_pos.mpr P.a_lt_b)
  have hκden : κ * (4 * w * M * (P.b - P.a)) ≤ η :=
    (le_div_iff₀ hden).mp hκbound
  have hκloss : w * κ * S ≤ η / 4 := by
    calc
      w * κ * S ≤ w * κ * (M * (P.b - P.a)) :=
        mul_le_mul_of_nonneg_left hSle (mul_nonneg hw.le hκ.le)
      _ = (κ * (4 * w * M * (P.b - P.a))) / 4 := by ring
      _ ≤ η / 4 := div_le_div_of_nonneg_right hκden (by norm_num)
  have hwerr : w * err = η / 4 := by
    dsimp [err]
    field_simp
  have hreal :
      w * (∫ y in P.a..P.b, F y) - η ≤
        w * (1 - κ) * S := by
    have hwR := mul_le_mul_of_nonneg_left hRiemann' hw.le
    rw [mul_add, hwerr] at hwR
    have hrewrite : w * (1 - κ) * S = w * S - w * κ * S := by ring
    rw [hrewrite]
    nlinarith
  have hpay :
      (∑ i : Fin N, (Q i).payoff) =
        ENNReal.ofReal (w * (1 - κ) * S) := by
    calc
      (∑ i : Fin N, (Q i).payoff) =
          ∑ i : Fin N,
            ENNReal.ofReal (w * (1 - κ) * (speed i * d)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [Q]
        rw [← ENNReal.ofReal_mul hw.le]
        congr 1
        dsimp [h]
        ring
      _ = ENNReal.ofReal
          (∑ i : Fin N, w * (1 - κ) * (speed i * d)) := by
        symm
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        positivity
      _ = ENNReal.ofReal (w * (1 - κ) * S) := by
        congr 1
        dsimp [S]
        rw [Finset.mul_sum]
  refine ⟨N, Q, hN, hpair, ?_, ?_, ?_⟩
  · intro i
    dsimp [Q]
    exact hwindow i
  · apply ENNReal.sum_ne_top.2
    intro i _hi
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 hrho).ne'
  · rw [hpay]
    apply ENNReal.ofReal_le_ofReal
    change w * (∫ y in P.a..P.b, F y) - η ≤ _
    exact hreal

set_option maxHeartbeats 900000 in
-- Compact-thickening localization replays the quantitative mesh construction.
/-- The tangent exhaustion can be placed inside any prescribed open
neighborhood of the compact graph restriction. -/
theorem exists_pairwiseDisjoint_tangentPatches_payoff_ge_in_open
    (P : Patch lam E) (hlam : 1 < lam)
    {W : Set PlanePoint} (hW : IsOpen W)
    (hgraphW :
      (fun y : ℝ => (P.graph y, y)) '' Icc P.a P.b ⊆ W)
    {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (Q : Fin N → RigidProjectionPatch lam E),
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      (∀ i, (Q i).window ⊆ P.tube ∩ W) ∧
      (∑ i, (Q i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal (P.weightedLength - η) ≤ ∑ i, (Q i).payoff := by
  let K : Set PlanePoint :=
    (fun y : ℝ => (P.graph y, y)) '' Icc P.a P.b
  have hK : IsCompact K := by
    apply isCompact_Icc.image
    exact P.graph_contDiff.continuous.prodMk continuous_id
  obtain ⟨δ, hδ, hthick⟩ :=
    hK.exists_cthickening_subset_open hW hgraphW
  let r := min (P.radius / 2) (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos P.radius_pos) (half_pos hδ)
  have hrle : r ≤ P.radius := by
    exact (min_le_left _ _).trans (half_le_self P.radius_pos.le)
  have hrδ : r ≤ δ := by
    exact (min_le_right _ _).trans (half_le_self hδ.le)
  let P' := P.withRadius r hr hrle
  have htube : P'.tube ⊆ P.tube ∩ W := by
    intro p hp
    rw [withRadius_tube] at hp
    refine ⟨⟨hp.1, hp.2.trans_le hrle⟩, hthick ?_⟩
    apply Metric.mem_cthickening_of_dist_le p (P.graph p.2, p.2) δ K
    · exact ⟨p.2, ⟨hp.1.1.le, hp.1.2.le⟩, rfl⟩
    · simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero]
      rw [max_eq_left (abs_nonneg _)]
      exact hp.2.le.trans hrδ
  obtain ⟨N, Q, hN, hpair, hlocal, hfinite, hpay⟩ :=
    P'.exists_pairwiseDisjoint_tangentPatches_payoff_ge hlam hη
  refine ⟨N, Q, hN, hpair, ?_, hfinite, ?_⟩
  · intro i
    exact (hlocal i).trans htube
  · simpa [P', withRadius, weightedLength] using hpay

end Patch

namespace Region

set_option maxHeartbeats 900000 in
-- This wrapper elaborates both the finite-band adapter and the full mesh proof.
/-- Tangent projection windows on an actual finite-band endpoint graph recover
its density-weighted compact graph-speed integral from below. -/
theorem exists_pairwiseDisjoint_heightGraphPatches_payoff_ge
    (R : Region) (lam : ℝ) (hlam : 1 < lam)
    (q : GraphIndex R) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆
      Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ))
    (zone : Zone) (hzone : ∀ y ∈ Ioo a b, zone.Contains y)
    {η : ℝ} (hη : 0 < η) :
    ∃ (P : Patch lam R.carrier) (N : ℕ)
        (Q : Fin N → RigidProjectionPatch lam R.carrier),
      P.a = a ∧
      P.b = b ∧
      P.side = (if q.2.2 then .right else .left) ∧
      P.zone = zone ∧
      Set.EqOn P.graph (R.indexedGraphValue q) (Icc a b) ∧
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      (∀ i, (Q i).window ⊆ P.tube) ∧
      (∑ i, (Q i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (zone.weight lam *
            (∫ y in a..b,
              Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2)) - η) ≤
        ∑ i, (Q i).payoff := by
  obtain ⟨P, ha, hb, hside, hPzone, hEq⟩ :=
    exists_heightGraphPatch R lam q hab hsub zone hzone
  obtain ⟨N, Q, hN, hpair, hlocal, hfinite, hpay⟩ :=
    P.exists_pairwiseDisjoint_tangentPatches_payoff_ge hlam hη
  have hlength :
      P.weightedLength =
        zone.weight lam *
          (∫ y in a..b,
            Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2)) := by
    rw [Patch.weightedLength, ha, hb, hPzone]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro y hy
    dsimp
    rw [(hEq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hy]
  refine ⟨P, N, Q, ha, hb, hside, hPzone, hEq, hN, hpair,
    hlocal, hfinite, ?_⟩
  rw [← hlength]
  exact hpay

set_option maxHeartbeats 950000 in
-- The composed result elaborates the adapter, thickening, and quantitative mesh.
/-- Actual finite-band endpoint windows may additionally be confined to any
prescribed open neighborhood of the compact endpoint trace. -/
theorem exists_pairwiseDisjoint_heightGraphPatches_payoff_ge_in_open
    (R : Region) (lam : ℝ) (hlam : 1 < lam)
    (q : GraphIndex R) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆
      Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ))
    (zone : Zone) (hzone : ∀ y ∈ Ioo a b, zone.Contains y)
    {W : Set PlanePoint} (hW : IsOpen W)
    (hgraphW :
      (fun y : ℝ => (R.indexedGraphValue q y, y)) '' Icc a b ⊆ W)
    {η : ℝ} (hη : 0 < η) :
    ∃ (P : Patch lam R.carrier) (N : ℕ)
        (Q : Fin N → RigidProjectionPatch lam R.carrier),
      P.a = a ∧
      P.b = b ∧
      P.side = (if q.2.2 then .right else .left) ∧
      P.zone = zone ∧
      Set.EqOn P.graph (R.indexedGraphValue q) (Icc a b) ∧
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      (∀ i, (Q i).window ⊆ P.tube ∩ W) ∧
      (∑ i, (Q i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (zone.weight lam *
            (∫ y in a..b,
              Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2)) - η) ≤
        ∑ i, (Q i).payoff := by
  obtain ⟨P, ha, hb, hside, hPzone, hEq⟩ :=
    exists_heightGraphPatch R lam q hab hsub zone hzone
  have hPgraphW :
      (fun y : ℝ => (P.graph y, y)) '' Icc P.a P.b ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Icc a b := by simpa only [ha, hb] using hy
    simpa only [hEq hy'] using hgraphW ⟨y, hy', rfl⟩
  obtain ⟨N, Q, hN, hpair, hlocal, hfinite, hpay⟩ :=
    P.exists_pairwiseDisjoint_tangentPatches_payoff_ge_in_open
      hlam hW hPgraphW hη
  have hlength :
      P.weightedLength =
        zone.weight lam *
          (∫ y in a..b,
            Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2)) := by
    rw [Patch.weightedLength, ha, hb, hPzone]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro y hy
    dsimp
    rw [(hEq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hy]
  refine ⟨P, N, Q, ha, hb, hside, hPzone, hEq, hN, hpair,
    hlocal, hfinite, ?_⟩
  rw [← hlength]
  exact hpay

end Region
end HeightGraphProjection
end FiniteBandRearrangement
end CMVRelaxation
