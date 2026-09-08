/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxation
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Euclidean projection defects for the CMV relaxation

A vertical target collar forces each approximating open domain either to cross
its frontier or to spend a fixed amount of symmetric-difference volume.  The
frontier term below is the one-dimensional Hausdorff measure in
`EuclideanPlane`, not Hausdorff measure for the coordinate product metric.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff

noncomputable section

namespace CMVRelaxation

/-- The closed coordinate box used by one vertical projection estimate. -/
def projectionBox (a b y₀ rho : ℝ) : Set PlanePoint :=
  Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ + 2 * rho)

/-- Horizontal coordinates whose complete vertical box segment meets the
frontier of `U`. -/
def crossingFibers (U : Set PlanePoint) (a b y₀ rho : ℝ) : Set ℝ :=
  Prod.fst '' (frontier U ∩ projectionBox a b y₀ rho)

/-- First coordinate after transporting the coordinate plane to its Euclidean
`L²` realization. -/
def euclideanFirst (z : EuclideanPlane) : ℝ :=
  (WithLp.ofLp z).1

lemma lipschitzWith_euclideanFirst : LipschitzWith 1 euclideanFirst := by
  change LipschitzWith 1
    (Prod.fst ∘ (WithLp.ofLp : EuclideanPlane → ℝ × ℝ))
  simpa only [one_mul] using LipschitzWith.prod_fst.comp
    (WithLp.prod_lipschitzWith_ofLp (2 : ℝ≥0∞) ℝ ℝ)

lemma euclideanFirst_planeEuclideanHomeomorph (p : PlanePoint) :
    euclideanFirst (planeEuclideanHomeomorph p) = p.1 := by
  rfl

lemma isCompact_projectionBox (a b y₀ rho : ℝ) :
    IsCompact (projectionBox a b y₀ rho) := by
  exact isCompact_Icc.prod isCompact_Icc

lemma isCompact_crossingFibers (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    IsCompact (crossingFibers U a b y₀ rho) := by
  exact ((isCompact_projectionBox a b y₀ rho).inter_left
    isClosed_frontier).image continuous_fst

lemma measurableSet_crossingFibers (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    MeasurableSet (crossingFibers U a b y₀ rho) :=
  (isCompact_crossingFibers U a b y₀ rho).measurableSet

lemma crossingFibers_eq_euclideanFirst_image (U : Set PlanePoint)
    (a b y₀ rho : ℝ) :
    crossingFibers U a b y₀ rho =
      euclideanFirst ''
        (planeEuclideanHomeomorph ''
          (frontier U ∩ projectionBox a b y₀ rho)) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨planeEuclideanHomeomorph p, ⟨p, hp, rfl⟩,
      euclideanFirst_planeEuclideanHomeomorph p⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, euclideanFirst_planeEuclideanHomeomorph p⟩

/-- The crossing-fiber width is controlled by the correct Euclidean `H¹`
measure of the frontier portion inside the coordinate box. -/
theorem volume_crossingFibers_le_euclidean_frontier
    (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    volume (crossingFibers U a b y₀ rho) ≤
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          (frontier U ∩ projectionBox a b y₀ rho)) := by
  rw [crossingFibers_eq_euclideanFirst_image, ← hausdorffMeasure_real]
  simpa using lipschitzWith_euclideanFirst.hausdorffMeasure_image_le
    (d := (1 : ℝ)) (by norm_num)
    (planeEuclideanHomeomorph ''
      (frontier U ∩ projectionBox a b y₀ rho))

/-- Evaluating `FrontierMeasure` on a measurable coordinate set is exactly
Euclidean `H¹` on the corresponding complete-frontier portion. -/
theorem frontierMeasure_apply_eq_euclidean
    (U Q : Set PlanePoint) (hQ : MeasurableSet Q) :
    FrontierMeasure U Q =
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (frontier U ∩ Q)) := by
  rw [FrontierMeasure, Measure.map_apply
    planeEuclideanHomeomorph.symm.measurable hQ, Measure.restrict_apply]
  · rw [planeEuclideanHomeomorph.preimage_symm,
      ← planeEuclideanHomeomorph.image_frontier,
      ← Set.image_inter planeEuclideanHomeomorph.injective]
    congr 2
    exact inter_comm _ _
  · exact planeEuclideanHomeomorph.symm.measurable hQ

/-- If one vertical box fiber misses the frontier of an open set, its complete
vertical segment is wholly inside or wholly outside that set. -/
lemma verticalSegment_subset_or_subset_compl
    {U : Set PlanePoint} {a b y₀ rho x : ℝ}
    (hx : x ∈ Icc a b \ crossingFibers U a b y₀ rho) :
    (fun y : ℝ => (x, y)) ''
        Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ U ∨
      (fun y : ℝ => (x, y)) ''
        Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ Uᶜ := by
  let f : ℝ → PlanePoint := fun y => (x, y)
  have hfrontier : Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆
      f ⁻¹' (frontier U)ᶜ := by
    intro y hy
    change (x, y) ∉ frontier U
    intro hboundary
    exact hx.2 ⟨(x, y), ⟨hboundary, ⟨hx.1, hy⟩⟩, rfl⟩
  have hcover : Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆
      f ⁻¹' interior U ∪ f ⁻¹' interior Uᶜ := by
    simpa only [preimage_union, compl_frontier_eq_union_interior] using hfrontier
  have hopenU : IsOpen (f ⁻¹' interior U) :=
    isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  have hopenC : IsOpen (f ⁻¹' interior Uᶜ) :=
    isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  have hdisjoint : Disjoint (f ⁻¹' interior U) (f ⁻¹' interior Uᶜ) := by
    apply Set.disjoint_left.2
    intro y hyU hyC
    exact (show f y ∉ U from interior_subset hyC) (interior_subset hyU)
  rcases isPreconnected_Icc.subset_or_subset hopenU hopenC hdisjoint
      hcover with hin | hout
  · left
    rintro p ⟨y, hy, rfl⟩
    exact interior_subset (hin hy)
  · right
    rintro p ⟨y, hy, rfl⟩
    exact interior_subset (hout hy)

/-- A fixed vertical collar contributes at least its height to a fiber of the
symmetric difference whenever the entire box fiber stays on one side of `U`. -/
lemma collar_length_le_fiber_symmDiff
    {E U : Set PlanePoint} {a b y₀ rho x : ℝ}
    (hrho : 0 < rho)
    (hlower :
      Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho) ⊆ E)
    (hupper :
      Disjoint (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho)) E)
    (hx : x ∈ Icc a b)
    (hfiber :
      (fun y : ℝ => (x, y)) ''
          Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ U ∨
      (fun y : ℝ => (x, y)) ''
          Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ Uᶜ) :
    ENNReal.ofReal rho ≤
      volume (Prod.mk x ⁻¹' (U ∆ E)) := by
  rcases hfiber with hin | hout
  · have hsubset : Icc (y₀ + rho) (y₀ + 2 * rho) ⊆
        Prod.mk x ⁻¹' (U ∆ E) := by
      intro y hy
      have hseg : y ∈ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) := by
        constructor <;> linarith [hy.1, hy.2]
      have hyU : (x, y) ∈ U := hin ⟨y, hseg, rfl⟩
      have hyNotE : (x, y) ∉ E := by
        intro hyE
        exact Set.disjoint_left.1 hupper ⟨hx, hy⟩ hyE
      simp only [Set.mem_preimage, Set.mem_symmDiff]
      exact Or.inl ⟨hyU, hyNotE⟩
    calc
      ENNReal.ofReal rho =
          volume (Icc (y₀ + rho) (y₀ + 2 * rho)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      _ ≤ volume (Prod.mk x ⁻¹' (U ∆ E)) := measure_mono hsubset
  · have hsubset : Icc (y₀ - 2 * rho) (y₀ - rho) ⊆
        Prod.mk x ⁻¹' (U ∆ E) := by
      intro y hy
      have hseg : y ∈ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) := by
        constructor <;> linarith [hy.1, hy.2]
      have hyNotU : (x, y) ∉ U := hout ⟨y, hseg, rfl⟩
      have hyE : (x, y) ∈ E := hlower ⟨hx, hy⟩
      simp only [Set.mem_preimage, Set.mem_symmDiff]
      exact Or.inr ⟨hyE, hyNotU⟩
    calc
      ENNReal.ofReal rho =
          volume (Icc (y₀ - 2 * rho) (y₀ - rho)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      _ ≤ volume (Prod.mk x ⁻¹' (U ∆ E)) := measure_mono hsubset

/-- The axis-aligned projection-defect estimate.  It quantifies over every
open approximant and measures its frontier only after transport to the
Euclidean `L²` plane. -/
theorem projection_defect
    {E U : Set PlanePoint} {a b y₀ rho : ℝ}
    (hE : MeasurableSet E) (hU : IsOpen U)
    (hrho : 0 < rho)
    (hlower :
      Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho) ⊆ E)
    (hupper :
      Disjoint (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho)) E) :
    ENNReal.ofReal (b - a) ≤
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (frontier U ∩ projectionBox a b y₀ rho)) +
        characteristicDistance U E / ENNReal.ofReal rho := by
  let N : Set ℝ := Icc a b \ crossingFibers U a b y₀ rho
  have hN : MeasurableSet N :=
    measurableSet_Icc.diff (measurableSet_crossingFibers U a b y₀ rho)
  have hdiff : MeasurableSet (U ∆ E) :=
    hU.measurableSet.symmDiff hE
  have hNdefect :
      ENNReal.ofReal rho * volume N ≤ volume (U ∆ E) := by
    calc
      ENNReal.ofReal rho * volume N =
          ∫⁻ _ in N, ENNReal.ofReal rho ∂volume := by
            rw [setLIntegral_const]
      _ ≤ ∫⁻ x in N, volume (Prod.mk x ⁻¹' (U ∆ E)) ∂volume := by
        apply setLIntegral_mono' hN
        intro x hx
        exact collar_length_le_fiber_symmDiff hrho hlower hupper hx.1
          (verticalSegment_subset_or_subset_compl hx)
      _ ≤ ∫⁻ x, volume (Prod.mk x ⁻¹' (U ∆ E)) ∂volume :=
        setLIntegral_le_lintegral N _
      _ = volume (U ∆ E) := by
        rw [Measure.volume_eq_prod, Measure.prod_apply hdiff]
  have hNdiv :
      volume N ≤ volume (U ∆ E) / ENNReal.ofReal rho := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.2 hrho).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2
    simpa only [mul_comm] using hNdefect
  have hwidth :
      volume (Icc a b) ≤
        volume (crossingFibers U a b y₀ rho) + volume N := by
    apply (measure_mono (show Icc a b ⊆
        crossingFibers U a b y₀ rho ∪ N by
      intro x hx
      by_cases hcross : x ∈ crossingFibers U a b y₀ rho
      · exact Or.inl hcross
      · exact Or.inr ⟨hx, hcross⟩)).trans
    exact measure_union_le _ _
  rw [Real.volume_Icc] at hwidth
  simpa only [characteristicDistance] using hwidth.trans (add_le_add
    (volume_crossingFibers_le_euclidean_frontier U a b y₀ rho) hNdiv)

/-- A pointwise density lower bound converts local frontier measure into the
corresponding local contribution to the smooth cost. -/
theorem ofReal_mul_frontierMeasure_le_setLIntegral
    {U Q : Set PlanePoint} (hQ : MeasurableSet Q) (lam w : ℝ)
    (hwindow : ∀ p ∈ Q, w ≤ StripDensity lam p) :
    ENNReal.ofReal w * FrontierMeasure U Q ≤
      ∫⁻ p in Q, ENNReal.ofReal (StripDensity lam p)
        ∂FrontierMeasure U := by
  calc
    ENNReal.ofReal w * FrontierMeasure U Q =
        ∫⁻ _ in Q, ENNReal.ofReal w ∂FrontierMeasure U := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ p in Q, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U := by
      apply setLIntegral_mono' hQ
      intro p hp
      exact ENNReal.ofReal_le_ofReal (hwindow p hp)

/-- A pointwise density lower bound on a measurable window converts its
frontier measure into a lower bound for the full smooth cost. -/
theorem ofReal_mul_frontierMeasure_le_smoothCost
    {U Q : Set PlanePoint} (hQ : MeasurableSet Q) (lam w : ℝ)
    (hwindow : ∀ p ∈ Q, w ≤ StripDensity lam p) :
    ENNReal.ofReal w * FrontierMeasure U Q ≤ smoothCost lam U := by
  calc
    ENNReal.ofReal w * FrontierMeasure U Q ≤
        ∫⁻ p in Q, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U :=
      ofReal_mul_frontierMeasure_le_setLIntegral hQ lam w hwindow
    _ ≤ ∫⁻ p, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U :=
      setLIntegral_le_lintegral Q _
    _ = smoothCost lam U := rfl

/-- Weighted projection-defect inequality.  A uniform density lower bound on
the box pays for crossing fibers through `smoothCost`; noncrossing fibers pay
through characteristic-function error. -/
theorem projection_defect_smoothCost
    {E U : Set PlanePoint} {a b y₀ rho : ℝ}
    (hE : MeasurableSet E) (hU : IsOpen U)
    (hrho : 0 < rho)
    (hlower :
      Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho) ⊆ E)
    (hupper :
      Disjoint (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho)) E)
    (lam w : ℝ)
    (hwindow : ∀ p ∈ projectionBox a b y₀ rho,
      w ≤ StripDensity lam p) :
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
      smoothCost lam U +
        (ENNReal.ofReal w / ENNReal.ofReal rho) *
          characteristicDistance U E := by
  have hproj := projection_defect hE hU hrho hlower hupper
  have hcost :
      ENNReal.ofReal w *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              (frontier U ∩ projectionBox a b y₀ rho)) ≤
        smoothCost lam U := by
    rw [← frontierMeasure_apply_eq_euclidean U
      (projectionBox a b y₀ rho)
      (isCompact_projectionBox a b y₀ rho).measurableSet]
    exact ofReal_mul_frontierMeasure_le_smoothCost
      (isCompact_projectionBox a b y₀ rho).measurableSet lam w hwindow
  calc
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
        ENNReal.ofReal w *
          ((μH[1] : Measure EuclideanPlane)
              (planeEuclideanHomeomorph ''
                (frontier U ∩ projectionBox a b y₀ rho)) +
            characteristicDistance U E / ENNReal.ofReal rho) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_left hproj (ENNReal.ofReal w)
    _ = ENNReal.ofReal w *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              (frontier U ∩ projectionBox a b y₀ rho)) +
        (ENNReal.ofReal w / ENNReal.ofReal rho) *
          characteristicDistance U E := by
      rw [mul_add]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ smoothCost lam U +
          (ENNReal.ofReal w / ENNReal.ofReal rho) *
            characteristicDistance U E :=
      add_le_add hcost le_rfl

/-- Pointwise lower bounds with a vanishing characteristic-function error pass
to the actual extended liminf cost of every smooth sequence. A fixed additive
allowance is retained after taking the liminf. -/
theorem SmoothSequence.cost_add_ge_of_pointwise_add_distance
    {lam : ℝ} (A : SmoothSequence) (E : Set PlanePoint)
    (target errorCoefficient allowance : ℝ≥0∞)
    (hconv : A.ConvergesTo E)
    (herrorCoefficient : errorCoefficient ≠ ⊤)
    (hpoint : ∀ n,
      target ≤ smoothCost lam (A.carrier n) +
        errorCoefficient * characteristicDistance (A.carrier n) E +
        allowance) :
    target ≤ A.cost lam + allowance := by
  unfold SmoothSequence.ConvergesTo at hconv
  unfold SmoothSequence.cost
  have herr : Tendsto
      (fun n => errorCoefficient *
        characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv
      (Or.inr herrorCoefficient)
  rw [← ENNReal.liminf_add_of_right_tendsto_zero herr]
  change target ≤
    liminf (fun n => smoothCost lam (A.carrier n) +
      errorCoefficient * characteristicDistance (A.carrier n) E) atTop +
      allowance
  rw [← liminf_add_const atTop
    (fun n => smoothCost lam (A.carrier n) +
      errorCoefficient * characteristicDistance (A.carrier n) E)
    allowance (by isBoundedDefault) (by isBoundedDefault)]
  exact le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall hpoint)

namespace FrozenCanonicalCap

/-- The compulsory `lambda = 2`, `h = 1/2` source profile. -/
def profile : CanonicalTypeIVProfile (2 : ℝ) where
  h := 1 / 2
  density_jump := by norm_num
  h_pos := by norm_num
  h_lt_one := by norm_num

def lowerCollar : Set PlanePoint :=
  Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (9 / 4 : ℝ) (19 / 8)

def upperCollar : Set PlanePoint :=
  Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (21 / 8 : ℝ) (11 / 4)

def box : Set PlanePoint :=
  Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (9 / 4 : ℝ) (11 / 4)

private lemma radius_eq : profile.radius = 2 := by
  norm_num [profile, CanonicalTypeIVProfile.radius]

private lemma upperCenter_eq : profile.upperCenter = (0, 1 / 2) := by
  rw [CanonicalTypeIVProfile.upperCenter]
  simp only [CanonicalTypeIVProfile.radius, CanonicalTypeIVProfile.alpha, profile]
  rw [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ (1 / 2) / 2)
    (by norm_num : (1 / 2 : ℝ) / 2 ≤ 1)]
  norm_num

private lemma carrier_height_le {p : PlanePoint} (hp : p ∈ profile.carrier) :
    p.2 ≤ 5 / 2 := by
  simp only [CanonicalTypeIVProfile.carrier,
    CanonicalTypeIVProfile.rectangleCarrier,
    CanonicalTypeIVProfile.leftSegmentCarrier,
    CanonicalTypeIVProfile.rightSegmentCarrier,
    CanonicalTypeIVProfile.upperCapCarrier,
    CanonicalTypeIVProfile.lowerCapCarrier,
    Set.mem_union, Set.mem_ofPred_eq] at hp
  rcases hp with (((hrect | hleft) | hright) | hupper) | hlower
  · exact le_trans (abs_le.mp hrect.2.2).2 (by norm_num)
  · exact le_trans (abs_le.mp hleft.2.2).2 (by norm_num)
  · exact le_trans (abs_le.mp hright.2.2).2 (by norm_num)
  · rw [upperCenter_eq, radius_eq] at hupper
    norm_num at hupper ⊢
    nlinarith [sq_nonneg p.1]
  · linarith [hlower.2]

/-- The frozen cap supplies the exact two target collars and the density-two
box required by the projection gate. -/
theorem collar_certificate :
    lowerCollar ⊆ profile.carrier ∧
    Disjoint upperCollar profile.carrier ∧
    ∀ p ∈ box, StripDensity 2 p = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [CanonicalTypeIVProfile.carrier, Set.mem_union]
    left
    right
    change (x - profile.upperCenter.1) ^ 2 +
        (y - profile.upperCenter.2) ^ 2 ≤ profile.radius ^ 2 ∧ 1 ≤ y
    rw [upperCenter_eq, radius_eq]
    norm_num at hx hy ⊢
    constructor
    · nlinarith [sq_nonneg x, sq_nonneg (y - 1 / 2)]
    · linarith
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ hcarrier
    norm_num at hy
    linarith [carrier_height_le hcarrier]
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [StripDensity, if_neg]
    intro habs
    rw [abs_of_pos] at habs
    · norm_num at hy
      linarith
    · norm_num at hy
      linarith

/-- Every smooth open competitor satisfies the frozen cap projection gate. -/
theorem smoothCost_add_distance_ge_one
    (U : Set PlanePoint) (hU : IsOpen U) :
    (1 : ℝ≥0∞) ≤ smoothCost 2 U +
      16 * characteristicDistance U profile.carrier := by
  have hE : MeasurableSet profile.carrier := by
    rw [profile.carrier_eq_candidate_assembly]
    exact profile.toCandidate.assembly.measurableSet_carrier
  have hcertificate := collar_certificate
  have hlower :
      Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ
          Icc ((5 / 2 : ℝ) - 2 * (1 / 8)) (5 / 2 - 1 / 8) ⊆
        profile.carrier := by
    (convert hcertificate.1 using 1; norm_num [lowerCollar])
  have hupper :
      Disjoint
        (Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ
          Icc ((5 / 2 : ℝ) + 1 / 8) (5 / 2 + 2 * (1 / 8)))
        profile.carrier := by
    (convert hcertificate.2.1 using 1; norm_num [upperCollar])
  have hwindow :
      ∀ p ∈ projectionBox (-(1 / 4 : ℝ)) (1 / 4) (5 / 2) (1 / 8),
        (2 : ℝ) ≤ StripDensity 2 p := by
    intro p hp
    have hpbox : p ∈ box := by
      (convert hp using 1; norm_num [projectionBox, box])
    exact (hcertificate.2.2 p hpbox).symm.le
  have h := projection_defect_smoothCost
    (E := profile.carrier) (U := U)
    (a := -(1 / 4 : ℝ)) (b := 1 / 4)
    (y₀ := 5 / 2) (rho := 1 / 8)
    hE hU (by norm_num) hlower hupper 2 2 hwindow
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 8)] at h
  norm_num at h
  exact h

/-- The frozen cap fails the recovery-sequence upper-bound gate at level one:
every smooth sequence converging in characteristic distance has liminf cost at
least one. -/
theorem smoothSequence_cost_ge_one
    (A : SmoothSequence) (hconv : A.ConvergesTo profile.carrier) :
    (1 : ℝ≥0∞) ≤ A.cost 2 := by
  simpa using A.cost_add_ge_of_pointwise_add_distance profile.carrier
    1 16 0 hconv (by norm_num)
    (fun n => by
      simpa only [add_zero] using smoothCost_add_distance_ge_one
        (A.carrier n) (A.smooth n).isOpen)

end FrozenCanonicalCap

end CMVRelaxation
