/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVLocalGraphSurgery
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Compact-core limits of smooth boundary energy

The global relaxation permits smooth approximants with unbounded support and
arbitrarily many components.  This module therefore restricts the literal
weighted complete-frontier measure to one fixed compact core before invoking
finite-measure compactness.  No global tightness assertion is made.
-/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff

noncomputable section

namespace CMVRelaxation
namespace CompactCoreEnergy

/-- The literal density-weighted complete-frontier measure of one smooth set. -/
def smoothEnergyMeasure (lam : ℝ) (U : Set PlanePoint) : Measure PlanePoint :=
  (FrontierMeasure U).withDensity
    (fun p => ENNReal.ofReal (StripDensity lam p))

/-- Values of the energy measure are exactly the existing localized smooth
costs on measurable windows. -/
theorem smoothEnergyMeasure_apply
    (lam : ℝ) (U : Set PlanePoint) {Q : Set PlanePoint}
    (hQ : MeasurableSet Q) :
    smoothEnergyMeasure lam U Q = smoothCostOn lam U Q := by
  rw [smoothEnergyMeasure, withDensity_apply _ hQ]
  rfl

/-- The total mass of the energy measure is the literal global smooth cost. -/
theorem smoothEnergyMeasure_univ (lam : ℝ) (U : Set PlanePoint) :
    smoothEnergyMeasure lam U univ = smoothCost lam U := by
  rw [smoothEnergyMeasure_apply lam U MeasurableSet.univ]
  simp only [smoothCostOn, smoothCost, Measure.restrict_univ]

/-- Restriction to a measurable core has the expected literal local mass. -/
theorem smoothEnergyMeasure_restrict_univ
    (lam : ℝ) (U : Set PlanePoint) {K : Set PlanePoint}
    (hK : MeasurableSet K) :
    (smoothEnergyMeasure lam U).restrict K univ = smoothCostOn lam U K := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smoothEnergyMeasure_apply lam U hK]

/-- A restricted energy measure is finite whenever the corresponding global
smooth cost is finite. -/
noncomputable def restrictedEnergyFiniteMeasure
    (lam : ℝ) (U K : Set PlanePoint)
    (hfinite : smoothCost lam U ≠ ⊤) : FiniteMeasure PlanePoint :=
  ⟨(smoothEnergyMeasure lam U).restrict K,
    isFiniteMeasure_restrict.2 <| ne_of_lt <|
      (measure_mono (subset_univ K)).trans_lt <| by
        rw [smoothEnergyMeasure_univ]
        exact lt_top_iff_ne_top.2 hfinite⟩

@[simp] theorem restrictedEnergyFiniteMeasure_toMeasure
    (lam : ℝ) (U K : Set PlanePoint)
    (hfinite : smoothCost lam U ≠ ⊤) :
    ((restrictedEnergyFiniteMeasure lam U K hfinite :
      FiniteMeasure PlanePoint) : Measure PlanePoint) =
      (smoothEnergyMeasure lam U).restrict K := rfl

/-- The finite measure's mass remains the exact localized cost; it is not an
independently chosen bound. -/
theorem restrictedEnergyFiniteMeasure_mass
    (lam : ℝ) (U : Set PlanePoint) {K : Set PlanePoint}
    (hK : MeasurableSet K) (hfinite : smoothCost lam U ≠ ⊤) :
    ((restrictedEnergyFiniteMeasure lam U K hfinite).mass : ℝ≥0∞) =
      smoothCostOn lam U K := by
  rw [FiniteMeasure.ennreal_mass]
  exact smoothEnergyMeasure_restrict_univ lam U hK

/-- Data extracted from one finite-liminf branch on one fixed compact core. -/
structure Limit
    (lam : ℝ) (A : SmoothSequence) (K : Set PlanePoint) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  cost_tendsto :
    Tendsto (fun n => smoothCost lam (A.carrier (index n))) atTop
      (𝓝 (A.cost lam))
  energy : ℕ → FiniteMeasure PlanePoint
  limitEnergy : FiniteMeasure PlanePoint
  energy_toMeasure : ∀ n,
    (energy n : Measure PlanePoint) =
      (smoothEnergyMeasure lam (A.carrier (index n))).restrict K
  energy_tendsto : Tendsto energy atTop (𝓝 limitEnergy)
  limit_compl_core : (limitEnergy : Measure PlanePoint) Kᶜ = 0
  limit_mass_le_cost : (limitEnergy.mass : ℝ≥0∞) ≤ A.cost lam

namespace Limit

variable {lam : ℝ} {A : SmoothSequence} {K : Set PlanePoint}

/-- Every approximating finite measure has exactly the corresponding localized
smooth cost as total mass. -/
theorem energy_mass_eq_smoothCostOn
    (L : Limit lam A K) (hK : MeasurableSet K) (n : ℕ) :
    ((L.energy n).mass : ℝ≥0∞) =
      smoothCostOn lam (A.carrier (L.index n)) K := by
  rw [FiniteMeasure.ennreal_mass, L.energy_toMeasure n]
  exact smoothEnergyMeasure_restrict_univ lam _ hK

/-- On a measurable subset of the core, the extracted measure is the literal
localized complete-frontier integral. -/
theorem energy_apply_eq_smoothCostOn
    (L : Limit lam A K) {Q : Set PlanePoint}
    (hQ : MeasurableSet Q) (hQK : Q ⊆ K) (n : ℕ) :
    (L.energy n : Measure PlanePoint) Q =
      smoothCostOn lam (A.carrier (L.index n)) Q := by
  rw [L.energy_toMeasure n, Measure.restrict_apply hQ,
    inter_eq_left.mpr hQK, smoothEnergyMeasure_apply lam _ hQ]

/-- Correctly directed closed-set Portmanteau for every extracted compact-core
limit. -/
theorem limsup_energy_closed_le
    (L : Limit lam A K) {Q : Set PlanePoint} (hQ : IsClosed Q) :
    limsup (fun n => (L.energy n : Measure PlanePoint) Q) atTop ≤
      (L.limitEnergy : Measure PlanePoint) Q :=
  FiniteMeasure.limsup_measure_closed_le_of_tendsto L.energy_tendsto hQ

end Limit


/-- A liminf-realizing subsequence and a weak limit of its compact-core energy
measures exist without boundedness, finite-component, or global-tightness
assumptions on the smooth approximants. -/
theorem exists_limit
    {lam : ℝ} (A : SmoothSequence) {K : Set PlanePoint}
    (hK : IsCompact K) (hfinite : A.cost lam < ⊤) :
    Nonempty (Limit lam A K) := by
  let c : ℝ≥0 := (A.cost lam).toNNReal + 1
  have hcost_lt_c : A.cost lam < (c : ℝ≥0∞) := by
    rw [show A.cost lam = ((A.cost lam).toNNReal : ℝ≥0∞) from
      (ENNReal.coe_toNNReal hfinite.ne).symm]
    exact ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ zero_lt_one)
  obtain ⟨u, huStrict, huCostRaw⟩ :=
    (MapClusterPt.liminf
      (u := fun n => smoothCost lam (A.carrier n))
      (f := atTop)).tendsto_subseq
  have huCost :
      Tendsto (fun n => smoothCost lam (A.carrier (u n))) atTop
        (𝓝 (A.cost lam)) := by
    change Tendsto (fun n => smoothCost lam (A.carrier (u n))) atTop
      (𝓝 (liminf (fun n => smoothCost lam (A.carrier n)) atTop)) at huCostRaw
    simpa only [SmoothSequence.cost] using huCostRaw
  have heventually :
      ∀ᶠ n in atTop, smoothCost lam (A.carrier (u n)) < (c : ℝ≥0∞) :=
    huCost.eventually_lt_const hcost_lt_c
  obtain ⟨chi, hchi, hbound⟩ := extraction_of_eventually_atTop heventually
  let v : ℕ → ℕ := u ∘ chi
  have hvStrict : StrictMono v := huStrict.comp hchi
  have hvCost :
      Tendsto (fun n => smoothCost lam (A.carrier (v n))) atTop
        (𝓝 (A.cost lam)) := by
    change Tendsto
      ((fun n => smoothCost lam (A.carrier (u n))) ∘ chi) atTop
        (𝓝 (A.cost lam))
    exact huCost.comp hchi.tendsto_atTop
  have hvBound : ∀ n, smoothCost lam (A.carrier (v n)) < (c : ℝ≥0∞) := by
    intro n
    simpa only [v, Function.comp_apply] using hbound n
  have hvFinite : ∀ n, smoothCost lam (A.carrier (v n)) ≠ ⊤ := by
    intro n
    exact ((hvBound n).trans ENNReal.coe_lt_top).ne
  let nu : ℕ → FiniteMeasure PlanePoint := fun n =>
    restrictedEnergyFiniteMeasure lam (A.carrier (v n)) K (hvFinite n)
  have hnuMass : ∀ n, (nu n).mass ≤ c := by
    intro n
    apply ENNReal.coe_le_coe.1
    rw [restrictedEnergyFiniteMeasure_mass lam _ hK.measurableSet]
    exact (setLIntegral_le_lintegral K _).trans (hvBound n).le
  have hnuSupport : ∀ n, (nu n : Measure PlanePoint) Kᶜ = 0 := by
    intro n
    rw [restrictedEnergyFiniteMeasure_toMeasure,
      Measure.restrict_apply hK.measurableSet.compl]
    simp only [compl_inter_self, measure_empty]
  by_cases hKempty : K = ∅
  · subst K
    exact ⟨{
      index := v
      index_strictMono := hvStrict
      cost_tendsto := hvCost
      energy := fun _ => 0
      limitEnergy := 0
      energy_toMeasure := by
        intro n
        simp only [Measure.restrict_empty, FiniteMeasure.toMeasure_zero]
      energy_tendsto := tendsto_const_nhds
      limit_compl_core := by simp
      limit_mass_le_cost := by
        simp only [FiniteMeasure.zero_mass, ENNReal.coe_zero, zero_le] }⟩
  have hKnonempty : K.Nonempty := nonempty_iff_ne_empty.2 hKempty
  let _ : Nonempty K := hKnonempty.to_subtype
  let _ : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let nuCore : ℕ → FiniteMeasure K := fun n =>
    (nu n).comap (Subtype.val : K → PlanePoint)
  have hnuCoreMass : ∀ n, (nuCore n).mass ≤ c := by
    intro n
    exact (FiniteMeasure.mass_comap_le _ _).trans (hnuMass n)
  let state : ℕ → ℝ≥0 × ProbabilityMeasure K := fun n =>
    ((nuCore n).mass, (nuCore n).normalize)
  have hstateMem : ∀ n,
      state n ∈ Icc (0 : ℝ≥0) c ×ˢ
        (univ : Set (ProbabilityMeasure K)) := by
    intro n
    exact ⟨⟨zero_le, hnuCoreMass n⟩, mem_univ _⟩
  obtain ⟨stateLimit, _hstateLimit, phi, hphi, hstateTendsto⟩ :=
    (isCompact_Icc.prod isCompact_univ).tendsto_subseq hstateMem
  have hmassTendsto :
      Tendsto (fun n => (nuCore (phi n)).mass) atTop
        (𝓝 stateLimit.1) := by
    simpa only [state, Function.comp_apply] using
      (Prod.tendsto_iff _ _).1 hstateTendsto |>.1
  have hprobTendsto :
      Tendsto (fun n => (nuCore (phi n)).normalize) atTop
        (𝓝 stateLimit.2) := by
    simpa only [state, Function.comp_apply] using
      (Prod.tendsto_iff _ _).1 hstateTendsto |>.2
  let nuCoreLimit : FiniteMeasure K :=
    stateLimit.1 • stateLimit.2.toFiniteMeasure
  have hnuCoreTendsto :
      Tendsto (fun n => nuCore (phi n)) atTop (𝓝 nuCoreLimit) := by
    have hprobFinite :
        Tendsto (fun n => (nuCore (phi n)).normalize.toFiniteMeasure) atTop
          (𝓝 stateLimit.2.toFiniteMeasure) :=
      (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        atTop).1 hprobTendsto
    have hsmul := hmassTendsto.smul hprobFinite
    apply hsmul.congr'
    filter_upwards with n
    exact (nuCore (phi n)).self_eq_mass_smul_normalize.symm
  have hmapNuCore : ∀ n,
      (nuCore n).map (Subtype.val : K → PlanePoint) = nu n := by
    intro n
    apply FiniteMeasure.toMeasure_injective
    rw [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap,
      map_comap_subtype_coe hK.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem (hnuSupport n)
  let nuLimit : FiniteMeasure PlanePoint :=
    nuCoreLimit.map (Subtype.val : K → PlanePoint)
  let idx : ℕ → ℕ := v ∘ phi
  let energy : ℕ → FiniteMeasure PlanePoint := nu ∘ phi
  have hidxStrict : StrictMono idx := hvStrict.comp hphi
  have hidxCost :
      Tendsto (fun n => smoothCost lam (A.carrier (idx n))) atTop
        (𝓝 (A.cost lam)) := by
    change Tendsto
      ((fun n => smoothCost lam (A.carrier (v n))) ∘ phi) atTop
        (𝓝 (A.cost lam))
    exact hvCost.comp hphi.tendsto_atTop
  have henergyTendsto : Tendsto energy atTop (𝓝 nuLimit) := by
    have hmapTendsto :=
      FiniteMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n => nuCore (phi n)) nuCoreLimit hnuCoreTendsto
          continuous_subtype_val
    apply hmapTendsto.congr'
    filter_upwards with n
    simpa only [energy, Function.comp_apply] using hmapNuCore (phi n)
  have henergyMeasure : ∀ n,
      (energy n : Measure PlanePoint) =
        (smoothEnergyMeasure lam (A.carrier (idx n))).restrict K := by
    intro n
    rfl
  have hmassTendsto' :
      Tendsto (fun n => ((energy n).mass : ℝ≥0∞)) atTop
        (𝓝 (nuLimit.mass : ℝ≥0∞)) :=
    ENNReal.tendsto_coe.2 henergyTendsto.mass
  have hmassLe : ∀ n,
      ((energy n).mass : ℝ≥0∞) ≤
        smoothCost lam (A.carrier (idx n)) := by
    intro n
    rw [FiniteMeasure.ennreal_mass, henergyMeasure n,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      smoothEnergyMeasure_apply lam _ hK.measurableSet]
    exact setLIntegral_le_lintegral K _
  have hlimitMass : (nuLimit.mass : ℝ≥0∞) ≤ A.cost lam :=
    le_of_tendsto_of_tendsto' hmassTendsto' hidxCost hmassLe
  have hlimitSupport : (nuLimit : Measure PlanePoint) Kᶜ = 0 := by
    dsimp only [nuLimit]
    rw [FiniteMeasure.toMeasure_map,
      Measure.map_apply measurable_subtype_coe hK.measurableSet.compl]
    rw [preimage_compl]
    have hpre : (Subtype.val : K → PlanePoint) ⁻¹' K = univ := by
      ext p
      simp only [mem_preimage, Subtype.coe_prop, mem_univ]
    rw [hpre, compl_univ, measure_empty]
  exact ⟨{
    index := idx
    index_strictMono := hidxStrict
    cost_tendsto := hidxCost
    energy := energy
    limitEnergy := nuLimit
    energy_toMeasure := henergyMeasure
    energy_tendsto := henergyTendsto
    limit_compl_core := hlimitSupport
    limit_mass_le_cost := hlimitMass }⟩
/-- In the infinite-liminf branch every extended target inequality is immediate;
no conversion to a finite or real-valued cost is used. -/
theorem le_cost_of_cost_eq_top
    {lam : ℝ} (A : SmoothSequence) (target : ℝ≥0∞)
    (hcost : A.cost lam = ⊤) : target ≤ A.cost lam := by
  rw [hcost]
  exact le_top

/-- A closed-set lower bound with a vanishing nonnegative error transfers to the
weak finite-measure limit.  The proof uses liminf first and only then the
correctly directed closed-set Portmanteau inequality. -/
theorem target_le_limit_of_closed_with_vanishing_error
    {mu : ℕ → FiniteMeasure PlanePoint} {muLimit : FiniteMeasure PlanePoint}
    (hmu : Tendsto mu atTop (𝓝 muLimit)) {Q : Set PlanePoint}
    (hQ : IsClosed Q) {target : ℝ≥0∞} {error : ℕ → ℝ≥0∞}
    (herror : Tendsto error atTop (𝓝 0))
    (hpoint : ∀ n, target ≤ (mu n : Measure PlanePoint) Q + error n) :
    target ≤ (muLimit : Measure PlanePoint) Q := by
  calc
    target ≤ liminf (fun n => (mu n : Measure PlanePoint) Q + error n) atTop :=
      le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hpoint)
    _ = liminf (fun n => (mu n : Measure PlanePoint) Q) atTop := by
      change liminf
        ((fun n => (mu n : Measure PlanePoint) Q) + error) atTop =
          liminf (fun n => (mu n : Measure PlanePoint) Q) atTop
      exact ENNReal.liminf_add_of_right_tendsto_zero herror
        (fun n => (mu n : Measure PlanePoint) Q)
    _ ≤ limsup (fun n => (mu n : Measure PlanePoint) Q) atTop :=
      liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ (muLimit : Measure PlanePoint) Q :=
      FiniteMeasure.limsup_measure_closed_le_of_tendsto hmu hQ

/-- The retained pointwise rigid projection defect transfers to a compact-core
energy limit at fixed rectangle geometry.  Characteristic distance is removed
only after the sequence limit; no shrinking geometry is interchanged with that
limit. -/
theorem rigid_projection_payoff_le_limit
    {lam : ℝ} {A : SmoothSequence} {E K : Set PlanePoint}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    {a b y0 rho : ℝ} (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : MeasurableSet E) (hrho : 0 < rho)
    (hlower :
      euclideanRigidMap e ''
        (Icc a b ×ˢ Icc (y0 - 2 * rho) (y0 - rho)) ⊆ E)
    (hupper :
      Disjoint
        (euclideanRigidMap e ''
          (Icc a b ×ˢ Icc (y0 + rho) (y0 + 2 * rho))) E)
    (w : ℝ)
    (hwindow : ∀ p ∈ rigidProjectionBox e a b y0 rho,
      w ≤ StripDensity lam p)
    (hboxCore : rigidProjectionBox e a b y0 rho ⊆ K) :
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
      (L.limitEnergy : Measure PlanePoint)
        (rigidProjectionBox e a b y0 rho) := by
  let Q := rigidProjectionBox e a b y0 rho
  let errorCoefficient := ENNReal.ofReal w / ENNReal.ofReal rho
  have herrorCoefficient : errorCoefficient ≠ ⊤ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 hrho).ne'
  have hdistance :
      Tendsto
        (fun n => characteristicDistance (A.carrier (L.index n)) E)
        atTop (𝓝 0) := by
    exact hconv.comp L.index_strictMono.tendsto_atTop
  have herror :
      Tendsto
        (fun n => errorCoefficient *
          characteristicDistance (A.carrier (L.index n)) E)
        atTop (𝓝 0) := by
    simpa only [errorCoefficient, mul_zero] using
      ENNReal.Tendsto.const_mul hdistance (Or.inr herrorCoefficient)
  apply target_le_limit_of_closed_with_vanishing_error
    L.energy_tendsto (isCompact_rigidProjectionBox e a b y0 rho).isClosed
    herror
  intro n
  have hdefect := rigid_projection_defect_setLIntegral e hE
    (A.smooth (L.index n)).isOpen hrho hlower hupper lam w hwindow
  calc
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
        smoothCostOn lam (A.carrier (L.index n)) Q +
          errorCoefficient *
            characteristicDistance (A.carrier (L.index n)) E := by
      simpa only [Q, smoothCostOn, errorCoefficient] using hdefect
    _ = (L.energy n : Measure PlanePoint) Q +
          errorCoefficient *
            characteristicDistance (A.carrier (L.index n)) E := by
      rw [L.energy_apply_eq_smoothCostOn
        (isCompact_rigidProjectionBox e a b y0 rho).measurableSet hboxCore n]

namespace EscapingMassExample

/-- A fixed compact coordinate core. -/
def core : Set PlanePoint := Icc (-1) 1 ×ˢ Icc (-1) 1

/-- The example's localization window is compact. -/
theorem isCompact_core : IsCompact core :=
  isCompact_Icc.prod isCompact_Icc

/-- Unit atoms escaping horizontally from the fixed core. -/
def atomLocation (n : ℕ) : PlanePoint := ((n : ℝ) + 2, 0)

/-- Every term has global mass one. -/
noncomputable def energy (n : ℕ) : FiniteMeasure PlanePoint :=
  ⟨Measure.dirac (atomLocation n), inferInstance⟩

/-- The finite measures do not lose global mass while their locations escape. -/
theorem energy_mass (n : ℕ) : (energy n).mass = 1 := by
  simp [energy, FiniteMeasure.mass]

/-- Every atom lies outside the fixed core. -/
theorem atomLocation_not_mem_core (n : ℕ) : atomLocation n ∉ core := by
  change ¬
    (((n : ℝ) + 2 ∈ Icc (-1 : ℝ) 1) ∧ ((0 : ℝ) ∈ Icc (-1 : ℝ) 1))
  rintro ⟨⟨_, hx⟩, _⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Restriction to the fixed compact core is identically zero. -/
theorem energy_restrict_core (n : ℕ) :
    (energy n : Measure PlanePoint).restrict core = 0 := by
  classical
  rw [show (energy n : Measure PlanePoint) = Measure.dirac (atomLocation n) from rfl,
    restrict_dirac]
  simp only [atomLocation_not_mem_core n, if_false]

/-- The localized energy as a genuine finite measure. -/
noncomputable def restrictedEnergy (n : ℕ) : FiniteMeasure PlanePoint :=
  ⟨(energy n : Measure PlanePoint).restrict core, inferInstance⟩

/-- The localized finite measures converge to zero even though their global
masses remain one, demonstrating why the construction asserts no global
tightness. -/
theorem restricted_energy_tendsto_zero :
    Tendsto restrictedEnergy atTop (𝓝 (0 : FiniteMeasure PlanePoint)) := by
  have hzero : restrictedEnergy = fun _ => (0 : FiniteMeasure PlanePoint) := by
    funext n
    apply FiniteMeasure.toMeasure_injective
    exact energy_restrict_core n
  rw [hzero]
  exact tendsto_const_nhds

end EscapingMassExample
end CompactCoreEnergy
end CMVRelaxation
