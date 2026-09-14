/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxation
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Distributional variation for CMV carriers

This module defines the Euclidean distributional variation of a planar
characteristic function using compactly supported smooth vector fields.  The
vector-field norm is measured after transport to the Euclidean `L²` plane;
the coordinate product norm is not used as a geometric substitute.

The global lower-semicontinuity argument is separated from the geometric
Gauss--Green obligation.  `SmoothGaussGreenBound` is the precise termwise
statement still required for every literal `IsSmoothDomain`; no recovery cost
is identified with the relaxed infimum.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology ContDiff symmDiff

noncomputable section

namespace CMVRelaxation

/-- A compactly supported smooth vector field on the actual Euclidean `L²`
plane, with pointwise norm at most one. -/
structure DistributionalTestField where
  toFun : EuclideanPlane → EuclideanPlane
  contDiff : ContDiff ℝ ∞ toFun
  hasCompactSupport : HasCompactSupport toFun
  norm_le_one : ∀ p, ‖toFun p‖ ≤ 1

instance : CoeFun DistributionalTestField
    (fun _ => EuclideanPlane → EuclideanPlane) :=
  ⟨DistributionalTestField.toFun⟩

namespace DistributionalTestField

/-- Euclidean divergence, expressed in the canonical orthonormal basis of the
finite-dimensional `L²` plane. -/
def divergence (X : DistributionalTestField) (p : EuclideanPlane) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ EuclideanPlane),
    inner ℝ (fderiv ℝ X p (stdOrthonormalBasis ℝ EuclideanPlane i))
      (stdOrthonormalBasis ℝ EuclideanPlane i)

lemma contDiff_divergence (X : DistributionalTestField) :
    ContDiff ℝ ∞ X.divergence := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ X) :=
    (contDiff_infty_iff_fderiv.mp X.contDiff).2
  unfold divergence
  apply ContDiff.sum
  intro i _hi
  exact (hfd.clm_apply contDiff_const).inner ℝ contDiff_const

lemma continuous_divergence (X : DistributionalTestField) :
    Continuous X.divergence :=
  X.contDiff_divergence.continuous

lemma hasCompactSupport_divergence (X : DistributionalTestField) :
    HasCompactSupport X.divergence := by
  classical
  let traceCLM :
      (EuclideanPlane →L[ℝ] EuclideanPlane) → ℝ :=
    fun A => ∑ i : Fin (Module.finrank ℝ EuclideanPlane),
      inner ℝ (A (stdOrthonormalBasis ℝ EuclideanPlane i))
        (stdOrthonormalBasis ℝ EuclideanPlane i)
  have hzero : traceCLM 0 = 0 := by
    simp [traceCLM]
  change HasCompactSupport (fun p : EuclideanPlane =>
    traceCLM (fderiv ℝ X p))
  simpa only [Function.comp_def] using
    (X.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left hzero

lemma integrable_divergence (X : DistributionalTestField) :
    Integrable X.divergence :=
  X.continuous_divergence.integrable_of_hasCompactSupport
    X.hasCompactSupport_divergence

/-- Every test divergence has a strictly positive global scalar bound. -/
theorem exists_pos_norm_divergence_bound (X : DistributionalTestField) :
    ∃ C : ℝ, 0 < C ∧ ∀ p, ‖X.divergence p‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    X.hasCompactSupport_divergence.exists_bound_of_continuous
      X.continuous_divergence
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p
  exact (hC p).trans (le_max_left _ _)

end DistributionalTestField

/-- The coordinate carrier transported to the Euclidean `L²` plane. -/
def euclideanCarrier (E : Set PlanePoint) : Set EuclideanPlane :=
  planeEuclideanHomeomorph '' E

lemma euclideanCarrier_eq_preimage (E : Set PlanePoint) :
    euclideanCarrier E = planeEuclideanHomeomorph.symm ⁻¹' E := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change planeEuclideanHomeomorph.symm
      (planeEuclideanHomeomorph q) ∈ E
    rw [planeEuclideanHomeomorph.symm_apply_apply]
    exact hq
  · intro hp
    exact ⟨planeEuclideanHomeomorph.symm p, hp,
      planeEuclideanHomeomorph.apply_symm_apply p⟩

lemma nullMeasurableSet_euclideanCarrier {E : Set PlanePoint}
    (hE : NullMeasurableSet E volume) :
    NullMeasurableSet (euclideanCarrier E) volume := by
  rw [euclideanCarrier_eq_preimage]
  exact hE.preimage
    (WithLp.volume_preserving_ofLp ℝ ℝ).quasiMeasurePreserving

lemma euclideanCarrier_ae_eq {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    euclideanCarrier E =ᵐ[volume] euclideanCarrier F := by
  rw [euclideanCarrier_eq_preimage, euclideanCarrier_eq_preimage]
  exact (WithLp.volume_preserving_ofLp ℝ ℝ).quasiMeasurePreserving
    |>.preimage_ae_eq hEF

lemma volume_euclideanCarrier {E : Set PlanePoint}
    (hE : NullMeasurableSet E volume) :
    volume (euclideanCarrier E) = volume E := by
  rw [euclideanCarrier_eq_preimage]
  exact (WithLp.volume_preserving_ofLp ℝ ℝ).measure_preimage hE

lemma euclideanCarrier_symmDiff (E F : Set PlanePoint) :
    euclideanCarrier (E ∆ F) =
      euclideanCarrier E ∆ euclideanCarrier F := by
  simpa only [euclideanCarrier] using
    Set.image_symmDiff planeEuclideanHomeomorph.injective E F

lemma volume_euclideanCarrier_symmDiff
    {E F : Set PlanePoint} (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) :
    volume (euclideanCarrier E ∆ euclideanCarrier F) =
      volume (E ∆ F) := by
  rw [← euclideanCarrier_symmDiff,
    volume_euclideanCarrier (hE.symmDiff hF)]

/-- Signed action of the distributional derivative of `χ_E` on one Euclidean
test field, using the convention `∫_E div X`. -/
def characteristicFlux (E : Set PlanePoint)
    (X : DistributionalTestField) : ℝ :=
  ∫ p in euclideanCarrier E, X.divergence p

/-- Euclidean total distributional variation of the characteristic function.
It is the supremum of the absolute flux over all compactly supported smooth
Euclidean vector fields with norm at most one. -/
def distributionalVariation (E : Set PlanePoint) : ℝ≥0∞ :=
  ⨆ X : DistributionalTestField,
    ENNReal.ofReal |characteristicFlux E X|

/-- Every individual admissible flux is bounded by total distributional
variation. -/
theorem ofReal_abs_characteristicFlux_le_distributionalVariation
    (E : Set PlanePoint) (X : DistributionalTestField) :
    ENNReal.ofReal |characteristicFlux E X| ≤
      distributionalVariation E := by
  exact le_iSup (fun Y : DistributionalTestField =>
    ENNReal.ofReal |characteristicFlux E Y|) X

/-- Distributional variation depends only on the characteristic function's
Lebesgue almost-everywhere class. -/
theorem distributionalVariation_congr_ae {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    distributionalVariation E = distributionalVariation F := by
  unfold distributionalVariation characteristicFlux
  congr 1
  funext X
  rw [setIntegral_congr_set (euclideanCarrier_ae_eq hEF)]

/-- A bounded integrable scalar density has Lipschitz set integral with respect
to finite symmetric-difference volume.  Null-measurable representatives are
accepted directly; no topological frontier is transported through AE equality. -/
theorem abs_setIntegral_sub_setIntegral_le_symmDiff
    {E F : Set EuclideanPlane} (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) {f : EuclideanPlane → ℝ}
    (hf : Integrable f) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ p, ‖f p‖ ≤ C)
    (hfinite : volume (E ∆ F) < ⊤) :
    |(∫ p in E, f p) - ∫ p in F, f p| ≤
      C * volume.real (E ∆ F) := by
  rw [← integral_indicator₀ hE, ← integral_indicator₀ hF,
    ← integral_sub (hf.indicator₀ hE) (hf.indicator₀ hF)]
  let d : EuclideanPlane → ℝ := E.indicator f - F.indicator f
  have hdSupport : ∫ p, d p = ∫ p in E ∆ F, d p := by
    rw [← integral_indicator₀ (hE.symmDiff hF)]
    apply integral_congr_ae
    filter_upwards with p
    simp only [d, Pi.sub_apply]
    by_cases hpE : p ∈ E <;> by_cases hpF : p ∈ F <;>
      simp [hpE, hpF, Set.mem_symmDiff]
  change |∫ p, d p| ≤ C * volume.real (E ∆ F)
  rw [hdSupport]
  simpa only [Real.norm_eq_abs] using
    (norm_setIntegral_le_of_norm_le_const (f := d) hfinite fun p hp => by
      rcases hp with hp | hp
      · rw [show d p = E.indicator f p - F.indicator f p by rfl,
          indicator_of_mem hp.1, indicator_of_notMem hp.2, sub_zero]
        exact hbound p
      · rw [show d p = E.indicator f p - F.indicator f p by rfl,
          indicator_of_notMem hp.2, indicator_of_mem hp.1, zero_sub, norm_neg]
        exact hbound p)

/-- Quantitative stability for a specified strictly positive divergence
bound.  Keeping the bound explicit lets one use the same error coefficient
along a complete recovery sequence. -/
theorem ofReal_abs_characteristicFlux_le_add_distance_of_bound
    {E F : Set PlanePoint} (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) (X : DistributionalTestField)
    {C : ℝ} (hCpos : 0 < C) (hC : ∀ p, ‖X.divergence p‖ ≤ C) :
    ENNReal.ofReal |characteristicFlux E X| ≤
      ENNReal.ofReal |characteristicFlux F X| +
        ENNReal.ofReal C * characteristicDistance E F := by
  by_cases hfinite : characteristicDistance E F < ⊤
  · have hvfinite : volume (E ∆ F) < ⊤ := by
      simpa only [characteristicDistance] using hfinite
    have hefinite :
        volume (euclideanCarrier E ∆ euclideanCarrier F) < ⊤ := by
      rwa [volume_euclideanCarrier_symmDiff hE hF]
    have hreal := abs_setIntegral_sub_setIntegral_le_symmDiff
      (nullMeasurableSet_euclideanCarrier hE)
      (nullMeasurableSet_euclideanCarrier hF)
      X.integrable_divergence hCpos.le hC hefinite
    change |characteristicFlux E X - characteristicFlux F X| ≤
      C * volume.real
        (euclideanCarrier E ∆ euclideanCarrier F) at hreal
    change |characteristicFlux E X - characteristicFlux F X| ≤
      C * (volume (euclideanCarrier E ∆ euclideanCarrier F)).toReal at hreal
    rw [volume_euclideanCarrier_symmDiff hE hF] at hreal
    have htriangle :
        |characteristicFlux E X| ≤ |characteristicFlux F X| +
          C * (volume (E ∆ F)).toReal := by
      calc
        |characteristicFlux E X| =
            |(characteristicFlux E X - characteristicFlux F X) +
              characteristicFlux F X| := by ring_nf
        _ ≤ |characteristicFlux E X - characteristicFlux F X| +
              |characteristicFlux F X| := abs_add_le _ _
        _ ≤ |characteristicFlux F X| +
              C * (volume (E ∆ F)).toReal := by
          linarith
    apply (ENNReal.ofReal_le_ofReal htriangle).trans_eq
    unfold characteristicDistance
    rw [ENNReal.ofReal_add (abs_nonneg _), ENNReal.ofReal_mul hCpos.le,
      ENNReal.ofReal_toReal hvfinite.ne]
    positivity
  · have htop : characteristicDistance E F = ⊤ :=
      top_unique (not_lt.mp hfinite)
    rw [htop]
    simp [ENNReal.ofReal_ne_zero_iff.mpr hCpos]

/-- One fixed test flux is stable under the literal extended global
characteristic distance.  The bound remains valid when that distance is
infinite. -/
theorem ofReal_abs_characteristicFlux_le_add_distance
    {E F : Set PlanePoint} (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) (X : DistributionalTestField) :
    ∃ C : ℝ, 0 < C ∧
      ENNReal.ofReal |characteristicFlux E X| ≤
        ENNReal.ofReal |characteristicFlux F X| +
          ENNReal.ofReal C * characteristicDistance E F := by
  obtain ⟨C, hCpos, hC⟩ := X.exists_pos_norm_divergence_bound
  exact ⟨C, hCpos,
    ofReal_abs_characteristicFlux_le_add_distance_of_bound
      hE hF X hCpos hC⟩

/-- The density-free geometric Gauss--Green obligation.  Its right side is the
actual Euclidean `H¹` measure of the complete topological frontier through
`FrontierMeasure`, not a supplied graph-length field. -/
def EuclideanGaussGreenBound (U : Set PlanePoint) : Prop :=
  ∀ X : DistributionalTestField,
    ENNReal.ofReal |characteristicFlux U X| ≤ FrontierMeasure U univ

lemma one_le_stripDensity {lam : ℝ} (hlam : 1 ≤ lam) (p : PlanePoint) :
    1 ≤ StripDensity lam p := by
  by_cases hp : |p.2| ≤ 1
  · simp [StripDensity, hp]
  · simp [StripDensity, hp, hlam]

/-- The exact coefficient-one Gauss--Green obligation for one literal smooth
approximant.  This predicate is deliberately not bundled into `IsSmoothDomain`:
it is the analytic theorem that must be proved from that existing structure. -/
def SmoothGaussGreenBound (lam : ℝ) (U : Set PlanePoint) : Prop :=
  ∀ X : DistributionalTestField,
    ENNReal.ofReal |characteristicFlux U X| ≤ smoothCost lam U
/-- The density-free coefficient-one bound implies the literal strip-weighted
bound for every CMV density `lambda ≥ 1`, including the density-one values on
both interfaces. -/
theorem SmoothGaussGreenBound.of_euclidean
    {lam : ℝ} (hlam : 1 ≤ lam) {U : Set PlanePoint}
    (hU : EuclideanGaussGreenBound U) :
    SmoothGaussGreenBound lam U := by
  intro X
  refine (hU X).trans ?_
  unfold smoothCost
  rw [← lintegral_one]
  apply lintegral_mono
  intro p
  simpa only [Pi.one_apply, ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (one_le_stripDensity hlam p)


/-- Once the termwise Gauss--Green inequality is available, global
characteristic convergence passes its coefficient-one bound through the actual
liminf cost.  This theorem does not assume that an arbitrary recovery realizes
the relaxed infimum. -/
theorem distributionalVariation_le_sequenceCost
    {lam : ℝ} {E : Set PlanePoint} (hE : NullMeasurableSet E volume)
    (A : SmoothSequence) (hconv : A.ConvergesTo E)
    (hterm : ∀ n, SmoothGaussGreenBound lam (A.carrier n)) :
    distributionalVariation E ≤ A.cost lam := by
  unfold distributionalVariation SmoothSequence.cost
  apply iSup_le
  intro X
  obtain ⟨C, hCpos, hC⟩ := X.exists_pos_norm_divergence_bound
  have herr : Tendsto
      (fun n => ENNReal.ofReal C *
        characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv
      (Or.inr ENNReal.ofReal_ne_top)
  rw [← ENNReal.liminf_add_of_right_tendsto_zero herr]
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards with n
  have hflux :=
    ofReal_abs_characteristicFlux_le_add_distance_of_bound hE
      (A.smooth n).isOpen.measurableSet.nullMeasurableSet X hCpos hC
  unfold characteristicDistance at hflux
  rw [symmDiff_comm] at hflux
  exact hflux.trans (add_le_add (hterm n X) le_rfl)

/-- Dependency map for the first BV gate: a genuine Gauss--Green theorem for
all existing smooth domains yields the lower bound for every admissible
sequence. -/
theorem distributionalVariation_le_sequenceCost_of_smooth
    {lam : ℝ}
    (hGaussGreen : ∀ U : Set PlanePoint,
      IsSmoothDomain U → SmoothGaussGreenBound lam U)
    {E : Set PlanePoint} (hE : NullMeasurableSet E volume)
    (A : SmoothSequence) (hconv : A.ConvergesTo E) :
    distributionalVariation E ≤ A.cost lam :=
  distributionalVariation_le_sequenceCost hE A hconv
    (fun n => hGaussGreen (A.carrier n) (A.smooth n))

/-- Infimum-level lower bound with its only unresolved dependency stated at
the correct quantifier: Gauss--Green for every member of the existing smooth
approximation class. -/
theorem distributionalVariation_le_relaxedPerimeter_of_smooth
    {lam : ℝ}
    (hGaussGreen : ∀ U : Set PlanePoint,
      IsSmoothDomain U → SmoothGaussGreenBound lam U)
    (E : Set PlanePoint) :
    distributionalVariation E ≤ relaxedPerimeter lam E := by
  unfold relaxedPerimeter
  apply le_sInf
  intro c hc
  rcases hc with ⟨A, hE, hconv, rfl⟩
  exact distributionalVariation_le_sequenceCost_of_smooth
    hGaussGreen hE A hconv

/-- Density-free Gauss--Green is sufficient for the literal relaxed lower
bound over the entire admissible density range. -/
theorem distributionalVariation_le_relaxedPerimeter_of_euclidean
    {lam : ℝ} (hlam : 1 ≤ lam)
    (hGaussGreen : ∀ U : Set PlanePoint,
      IsSmoothDomain U → EuclideanGaussGreenBound U)
    (E : Set PlanePoint) :
    distributionalVariation E ≤ relaxedPerimeter lam E :=
  distributionalVariation_le_relaxedPerimeter_of_smooth
    (fun U hU =>
      SmoothGaussGreenBound.of_euclidean hlam (hGaussGreen U hU)) E

end CMVRelaxation
