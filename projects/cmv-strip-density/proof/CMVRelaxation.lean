/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FrontierPerimeter
import CMVSourceBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# CMV relaxed perimeter and translation transport

Cañete, Section 2 (printed pages 2--3), defines weighted
perimeter as the lower envelope of weighted boundary costs of smooth sets that
converge globally in the `L¹` topology.  This module records that definition in
`ℝ≥0∞`.  Smooth approximants are open domains with a local one-sided regular
`C∞` defining function at every boundary point; they are not restricted to the
piecewise-circular model.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation

/-- A smooth open domain in the literal local one-sided sense used by the
relaxation.  The continuous linear map explicitly records the nonzero
derivative of each local defining function. -/
structure IsSmoothDomain (U : Set PlanePoint) : Prop where
  isOpen : IsOpen U
  regular_boundary : ∀ p ∈ frontier U,
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      U ∩ V = V ∩ {q | g q < 0}

@[simp] theorem horizontalTranslation_neg_apply (t : ℝ) (p : PlanePoint) :
    horizontalTranslation (-t) (horizontalTranslation t p) = p := by
  ext <;> simp [horizontalTranslation_apply]

@[simp] theorem horizontalTranslation_apply_neg (t : ℝ) (p : PlanePoint) :
    horizontalTranslation t (horizontalTranslation (-t) p) = p := by
  ext <;> simp [horizontalTranslation_apply]

theorem mem_horizontalTranslation_image_iff (t : ℝ)
    (U : Set PlanePoint) (p : PlanePoint) :
    p ∈ horizontalTranslation t '' U ↔
      horizontalTranslation (-t) p ∈ U := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨horizontalTranslation (-t) p, hp, by simp⟩

theorem horizontalTranslation_image_image (t : ℝ) (U : Set PlanePoint) :
    horizontalTranslation (-t) '' (horizontalTranslation t '' U) = U := by
  ext p
  simp only [mem_horizontalTranslation_image_iff]
  simp

private theorem contDiff_horizontalTranslation (t : ℝ) :
    ContDiff ℝ ∞ (horizontalTranslation t : PlanePoint → PlanePoint) := by
  rw [show (horizontalTranslation t : PlanePoint → PlanePoint) =
      fun p => p + (t, 0) by
    funext p
    ext <;> simp [horizontalTranslation_apply]]
  fun_prop

private theorem hasFDerivAt_horizontalTranslation (t : ℝ) (p : PlanePoint) :
    HasFDerivAt (horizontalTranslation t : PlanePoint → PlanePoint)
      (ContinuousLinearMap.id ℝ PlanePoint) p := by
  rw [show (horizontalTranslation t : PlanePoint → PlanePoint) =
      fun q => q + (t, 0) by
    funext q
    ext <;> simp [horizontalTranslation_apply]]
  exact (hasFDerivAt_id p).add_const (t, 0)

/-- Arbitrary horizontal translations preserve the concrete smooth-domain
class, by translating every local defining function. -/
theorem IsSmoothDomain.horizontalTranslation_image {U : Set PlanePoint}
    (hU : IsSmoothDomain U) (t : ℝ) :
    IsSmoothDomain (horizontalTranslation t '' U) := by
  constructor
  · exact (horizontalTranslation t).isOpenMap U hU.isOpen
  · intro p hp
    rw [← (horizontalTranslation t).image_frontier] at hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hU.regular_boundary q hq with
      ⟨V, g, D, hVopen, hqV, hg, hgq, hderiv, hD, hlocal⟩
    let τm : PlanePoint → PlanePoint := horizontalTranslation (-t)
    let Vt : Set PlanePoint := τm ⁻¹' V
    refine ⟨Vt, g ∘ τm, D, ?_, ?_, ?_, ?_, ?_, hD, ?_⟩
    · exact hVopen.preimage (horizontalTranslation (-t)).continuous
    · change horizontalTranslation (-t) (horizontalTranslation t q) ∈ V
      simpa using hqV
    · exact hg.comp (contDiff_horizontalTranslation (-t)).contDiffOn
        (fun _ hz => hz)
    · change g (τm (horizontalTranslation t q)) = 0
      simpa [τm] using hgq
    · have hgAt : HasFDerivAt g D
          (τm (horizontalTranslation t q)) := by
        simpa [τm] using hderiv
      simpa [τm] using hgAt.comp (horizontalTranslation t q)
        (hasFDerivAt_horizontalTranslation (-t)
          (horizontalTranslation t q))
    · ext z
      have hz := Set.ext_iff.mp hlocal (horizontalTranslation (-t) z)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hz
      change
        (z ∈ horizontalTranslation t '' U ∧
            horizontalTranslation (-t) z ∈ V) ↔
          (horizontalTranslation (-t) z ∈ V ∧
            g (horizontalTranslation (-t) z) < 0)
      simpa only [mem_horizontalTranslation_image_iff] using hz

/-- Global extended symmetric-difference distance between characteristic
functions.  No conversion through `Measure.real` is used. -/
def characteristicDistance (E F : Set PlanePoint) : ℝ≥0∞ :=
  volume (E ∆ F)

/-- For null-measurable representatives, symmetric-difference volume is
exactly the extended `L¹` seminorm distance of their characteristic functions. -/
theorem characteristicDistance_eq_eLpNorm
    {E F : Set PlanePoint}
    (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume) :
    characteristicDistance E F =
      eLpNorm
        (E.indicator (fun _ : PlanePoint => (1 : ℝ)) -
          F.indicator (fun _ : PlanePoint => (1 : ℝ)))
        1 volume := by
  rw [characteristicDistance,
    eLpNorm_indicator_sub_indicator E F (fun _ : PlanePoint => (1 : ℝ)),
    eLpNorm_indicator_const₀ (hE.symmDiff hF) one_ne_zero ENNReal.one_ne_top]
  simp

private theorem volume_horizontalTranslation_image (t : ℝ)
    (E : Set PlanePoint) :
    volume (horizontalTranslation t '' E) = volume E := by
  have h := (measurePreserving_horizontalTranslation t).setLIntegral_comp_emb
    (horizontalTranslation t).measurableEmbedding
    (fun _ : PlanePoint => (1 : ℝ≥0∞)) E
  simpa using h.symm

/-- Horizontal translation is an exact isometry for the global extended
characteristic-function distance. -/
theorem characteristicDistance_horizontalTranslation (t : ℝ)
    (E F : Set PlanePoint) :
    characteristicDistance (horizontalTranslation t '' E)
      (horizontalTranslation t '' F) = characteristicDistance E F := by
  rw [characteristicDistance, characteristicDistance,
    ← Set.image_symmDiff (horizontalTranslation t).injective]
  exact volume_horizontalTranslation_image t (E ∆ F)

/-- Extended weighted boundary cost of one smooth approximant.  This is a
Euclidean `H¹` complete-frontier cost; it is not the relaxed target perimeter. -/
def smoothCost (lam : ℝ) (U : Set PlanePoint) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (StripDensity lam p) ∂FrontierMeasure U

/-- Every individual extended smooth cost is preserved exactly, including
infinite costs. -/
theorem smoothCost_horizontalTranslation (lam t : ℝ)
    (U : Set PlanePoint) :
    smoothCost lam (horizontalTranslation t '' U) = smoothCost lam U := by
  rw [smoothCost, frontierMeasure_horizontalTranslation,
    (horizontalTranslation t).measurableEmbedding.lintegral_map]
  apply lintegral_congr
  intro p
  rw [stripDensity_horizontalTranslation]

/-- A sequence in the actual smooth approximation class. -/
structure SmoothSequence where
  carrier : ℕ → Set PlanePoint
  smooth : ∀ n, IsSmoothDomain (carrier n)

@[ext] theorem SmoothSequence.ext {A B : SmoothSequence}
    (h : A.carrier = B.carrier) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Global convergence of characteristic functions to a target carrier. -/
def SmoothSequence.ConvergesTo (A : SmoothSequence)
    (E : Set PlanePoint) : Prop :=
  Tendsto (fun n => characteristicDistance (A.carrier n) E) atTop (𝓝 0)

/-- The extended liminf cost of a smooth sequence. -/
def SmoothSequence.cost (lam : ℝ) (A : SmoothSequence) : ℝ≥0∞ :=
  liminf (fun n => smoothCost lam (A.carrier n)) atTop

/-- Translate every term of a smooth sequence. -/
def SmoothSequence.translate (t : ℝ) (A : SmoothSequence) : SmoothSequence where
  carrier n := horizontalTranslation t '' A.carrier n
  smooth n := (A.smooth n).horizontalTranslation_image t

@[simp] theorem SmoothSequence.translate_carrier (t : ℝ)
    (A : SmoothSequence) (n : ℕ) :
    (A.translate t).carrier n = horizontalTranslation t '' A.carrier n := rfl

/-- Translation by `-t` is the inverse sequence transport, not merely an
existence statement about a replacement sequence. -/
@[simp] theorem SmoothSequence.translate_neg_translate (t : ℝ)
    (A : SmoothSequence) :
    (A.translate t).translate (-t) = A := by
  apply SmoothSequence.ext
  funext n
  exact horizontalTranslation_image_image t (A.carrier n)

@[simp] theorem SmoothSequence.translate_translate_neg (t : ℝ)
    (A : SmoothSequence) :
    (A.translate (-t)).translate t = A := by
  simpa only [neg_neg] using A.translate_neg_translate (-t)
/-- Translation is an equivalence of the full concrete smooth-sequence class. -/
def SmoothSequence.translationEquiv (t : ℝ) :
    SmoothSequence ≃ SmoothSequence where
  toFun := SmoothSequence.translate t
  invFun := SmoothSequence.translate (-t)
  left_inv := SmoothSequence.translate_neg_translate t
  right_inv := SmoothSequence.translate_translate_neg t


/-- Termwise translation preserves the complete extended cost sequence and
therefore its liminf exactly. -/
theorem SmoothSequence.cost_translate (lam t : ℝ)
    (A : SmoothSequence) :
    (A.translate t).cost lam = A.cost lam := by
  unfold SmoothSequence.cost
  apply Filter.liminf_congr
  filter_upwards with n
  exact smoothCost_horizontalTranslation lam t (A.carrier n)

/-- The sequence transport preserves global convergence in both directions. -/
theorem SmoothSequence.convergesTo_translate_iff (t : ℝ)
    (A : SmoothSequence) (E : Set PlanePoint) :
    (A.translate t).ConvergesTo (horizontalTranslation t '' E) ↔
      A.ConvergesTo E := by
  unfold SmoothSequence.ConvergesTo
  simpa only [SmoothSequence.translate_carrier,
    characteristicDistance_horizontalTranslation]

/-- Extended-valued CMV relaxation.  The infimum ranges over all literal smooth
sequences with global characteristic-function convergence.  If the target is
not null-measurable or no admissible sequence exists, the set is empty and its
`ℝ≥0∞` infimum is `∞`. -/
def relaxedPerimeter (lam : ℝ) (E : Set PlanePoint) : ℝ≥0∞ :=
  sInf {c : ℝ≥0∞ | ∃ A : SmoothSequence,
    NullMeasurableSet E volume ∧ A.ConvergesTo E ∧ A.cost lam = c}

/-- The extended infimum has the source-correct empty-family value. -/
theorem relaxedPerimeter_eq_top_of_no_admissible
    (lam : ℝ) (E : Set PlanePoint)
    (h : ¬ ∃ A : SmoothSequence,
      NullMeasurableSet E volume ∧ A.ConvergesTo E) :
    relaxedPerimeter lam E = ⊤ := by
  unfold relaxedPerimeter
  have hempty :
      {c : ℝ≥0∞ | ∃ A : SmoothSequence,
        NullMeasurableSet E volume ∧ A.ConvergesTo E ∧ A.cost lam = c} =
        ∅ := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨A, hE, hconv, -⟩
    exact h ⟨A, hE, hconv⟩
  rw [hempty, sInf_empty]

/-- Null measurability is preserved by horizontal translation. -/
theorem nullMeasurableSet_horizontalTranslation_image
    {E : Set PlanePoint} (hE : NullMeasurableSet E volume) (t : ℝ) :
    NullMeasurableSet (horizontalTranslation t '' E) volume := by
  rw [show horizontalTranslation t '' E =
      horizontalTranslation (-t) ⁻¹' E by
    ext p
    exact mem_horizontalTranslation_image_iff t E p]
  exact hE.preimage
    (measurePreserving_horizontalTranslation (-t)).quasiMeasurePreserving

theorem nullMeasurableSet_horizontalTranslation_iff
    (t : ℝ) (E : Set PlanePoint) :
    NullMeasurableSet (horizontalTranslation t '' E) volume ↔
      NullMeasurableSet E volume := by
  constructor
  · intro hE
    have hback :=
      nullMeasurableSet_horizontalTranslation_image hE (-t)
    simpa only [horizontalTranslation_image_image] using hback
  · intro hE
    exact nullMeasurableSet_horizontalTranslation_image hE t

/-- Replacing the target by an almost-everywhere equal representative leaves
every characteristic-function distance unchanged. -/
theorem characteristicDistance_congr_ae
    (U : Set PlanePoint) {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    characteristicDistance U E = characteristicDistance U F := by
  unfold characteristicDistance
  exact measure_congr ((ae_eq_refl U).symmDiff hEF)

/-- Convergence belongs to the target's almost-everywhere equivalence class. -/
theorem SmoothSequence.convergesTo_congr_ae
    (A : SmoothSequence) {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    A.ConvergesTo E ↔ A.ConvergesTo F := by
  unfold SmoothSequence.ConvergesTo
  have hdist :
      (fun n => characteristicDistance (A.carrier n) E) =
        fun n => characteristicDistance (A.carrier n) F := by
    funext n
    exact characteristicDistance_congr_ae (A.carrier n) hEF
  rw [hdist]

/-- The relaxed functional is exactly translation invariant.  The proof
identifies the two complete cost families, so it also covers the value `∞`. -/
theorem relaxedPerimeter_horizontalTranslation
    (lam t : ℝ) (E : Set PlanePoint) :
    relaxedPerimeter lam (horizontalTranslation t '' E) =
      relaxedPerimeter lam E := by
  unfold relaxedPerimeter
  refine congrArg sInf ?_
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hE, hconv, hcost⟩
    refine ⟨A.translate (-t), ?_, ?_, ?_⟩
    · have hback :=
        nullMeasurableSet_horizontalTranslation_image hE (-t)
      simpa only [horizontalTranslation_image_image] using hback
    · have hback :=
        (A.convergesTo_translate_iff (-t)
          (horizontalTranslation t '' E)).2 hconv
      simpa only [horizontalTranslation_image_image] using hback
    · simpa only [SmoothSequence.cost_translate] using hcost
  · rintro ⟨A, hE, hconv, hcost⟩
    exact ⟨A.translate t,
      nullMeasurableSet_horizontalTranslation_image hE t,
      (A.convergesTo_translate_iff t E).2 hconv,
      by simpa only [SmoothSequence.cost_translate] using hcost⟩

/-- The relaxed functional depends only on the target's almost-everywhere
representative.  This is an equality of extended values, including `∞`. -/
theorem relaxedPerimeter_congr_ae
    (lam : ℝ) {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    relaxedPerimeter lam E = relaxedPerimeter lam F := by
  unfold relaxedPerimeter
  refine congrArg sInf ?_
  ext c
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, hE, hconv, hcost⟩
    exact ⟨A, hE.congr hEF,
      (A.convergesTo_congr_ae hEF).1 hconv, hcost⟩
  · rintro ⟨A, hF, hconv, hcost⟩
    exact ⟨A, hF.congr hEF.symm,
      (A.convergesTo_congr_ae hEF.symm).1 hconv, hcost⟩

/-- Ambient weighted area also depends only on the almost-everywhere
representative. -/
theorem weightedArea_congr_ae
    (lam : ℝ) {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    _root_.WeightedArea lam E = _root_.WeightedArea lam F := by
  unfold _root_.WeightedArea
  exact setIntegral_congr_set hEF

/-- Concrete source semantics induced by the extended CMV relaxation.
Source-finiteness records both null measurability and a genuinely finite
extended perimeter before the value is converted to `ℝ`. -/
def relaxedSourceSemantics (lam : ℝ) : SourcePerimeterSemantics lam where
  IsFinitePerimeter E :=
    NullMeasurableSet E volume ∧ relaxedPerimeter lam E < ⊤
  perimeter E := (relaxedPerimeter lam E).toReal

@[simp] theorem relaxedSourceSemantics_isFinitePerimeter
    (lam : ℝ) (E : Set PlanePoint) :
    (relaxedSourceSemantics lam).IsFinitePerimeter E ↔
      NullMeasurableSet E volume ∧ relaxedPerimeter lam E < ⊤ :=
  Iff.rfl

@[simp] theorem relaxedSourceSemantics_isAdmissible
    (lam : ℝ) (E : Set PlanePoint) :
    (relaxedSourceSemantics lam).IsAdmissible E ↔
      (NullMeasurableSet E volume ∧ relaxedPerimeter lam E < ⊤) ∧
        IntegrableOn (StripDensity lam) E :=
  Iff.rfl


theorem relaxedSourceSemantics_nullMeasurable
    {lam : ℝ} {E : Set PlanePoint}
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E) :
    NullMeasurableSet E volume :=
  hE.1

theorem relaxedSourceSemantics_relaxedPerimeter_lt_top
    {lam : ℝ} {E : Set PlanePoint}
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E) :
    relaxedPerimeter lam E < ⊤ :=
  hE.2

/-- On the finite source domain, the real adapter recovers the exact extended
relaxed perimeter. -/
theorem relaxedSourceSemantics_ofReal_perimeter
    {lam : ℝ} {E : Set PlanePoint}
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E) :
    ENNReal.ofReal ((relaxedSourceSemantics lam).perimeter E) =
      relaxedPerimeter lam E := by
  change ENNReal.ofReal (relaxedPerimeter lam E).toReal =
    relaxedPerimeter lam E
  exact ENNReal.ofReal_toReal
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hE).ne

/-- Real perimeter comparison is exactly extended-perimeter comparison when
both carriers satisfy the adapter's finite-source predicate. -/
theorem relaxedSourceSemantics_perimeter_le_iff
    {lam : ℝ} {E F : Set PlanePoint}
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E)
    (hF : (relaxedSourceSemantics lam).IsFinitePerimeter F) :
    (relaxedSourceSemantics lam).perimeter E ≤
        (relaxedSourceSemantics lam).perimeter F ↔
      relaxedPerimeter lam E ≤ relaxedPerimeter lam F := by
  change (relaxedPerimeter lam E).toReal ≤
      (relaxedPerimeter lam F).toReal ↔
    relaxedPerimeter lam E ≤ relaxedPerimeter lam F
  exact ENNReal.toReal_le_toReal
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hE).ne
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hF).ne

/-- Source-finiteness is invariant under every horizontal placement. -/
theorem relaxedSourceSemantics_isFinitePerimeter_horizontalTranslation_iff
    (lam t : ℝ) (E : Set PlanePoint) :
    (relaxedSourceSemantics lam).IsFinitePerimeter
        (horizontalTranslation t '' E) ↔
      (relaxedSourceSemantics lam).IsFinitePerimeter E := by
  change
    (NullMeasurableSet (horizontalTranslation t '' E) volume ∧
        relaxedPerimeter lam (horizontalTranslation t '' E) < ⊤) ↔
      NullMeasurableSet E volume ∧ relaxedPerimeter lam E < ⊤
  rw [nullMeasurableSet_horizontalTranslation_iff,
    relaxedPerimeter_horizontalTranslation]

/-- The real source perimeter is translation invariant on its finite domain;
both `toReal` arguments are justified by the source-finiteness witnesses. -/
theorem relaxedSourceSemantics_perimeter_horizontalTranslation
    (lam t : ℝ) (E : Set PlanePoint)
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E) :
    (relaxedSourceSemantics lam).perimeter
        (horizontalTranslation t '' E) =
      (relaxedSourceSemantics lam).perimeter E := by
  have hEt :
      (relaxedSourceSemantics lam).IsFinitePerimeter
        (horizontalTranslation t '' E) :=
    (relaxedSourceSemantics_isFinitePerimeter_horizontalTranslation_iff
      lam t E).2 hE
  change
    (relaxedPerimeter lam (horizontalTranslation t '' E)).toReal =
      (relaxedPerimeter lam E).toReal
  apply (ENNReal.toReal_eq_toReal_iff'
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hEt).ne
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hE).ne).2
  exact relaxedPerimeter_horizontalTranslation lam t E

/-- Source-finiteness descends to almost-everywhere equivalence classes. -/
theorem relaxedSourceSemantics_isFinitePerimeter_congr_ae
    (lam : ℝ) {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    (relaxedSourceSemantics lam).IsFinitePerimeter E ↔
      (relaxedSourceSemantics lam).IsFinitePerimeter F := by
  change
    (NullMeasurableSet E volume ∧ relaxedPerimeter lam E < ⊤) ↔
      NullMeasurableSet F volume ∧ relaxedPerimeter lam F < ⊤
  constructor
  · rintro ⟨hE, hperimeter⟩
    exact ⟨hE.congr hEF, by
      rwa [← relaxedPerimeter_congr_ae lam hEF]⟩
  · rintro ⟨hF, hperimeter⟩
    exact ⟨hF.congr hEF.symm, by
      rwa [relaxedPerimeter_congr_ae lam hEF]⟩

/-- The real source perimeter is representative-invariant on its finite
domain, with both conversions justified before comparing them. -/
theorem relaxedSourceSemantics_perimeter_congr_ae
    (lam : ℝ) {E F : Set PlanePoint}
    (hE : (relaxedSourceSemantics lam).IsFinitePerimeter E)
    (hEF : E =ᵐ[volume] F) :
    (relaxedSourceSemantics lam).perimeter E =
      (relaxedSourceSemantics lam).perimeter F := by
  have hF :
      (relaxedSourceSemantics lam).IsFinitePerimeter F :=
    (relaxedSourceSemantics_isFinitePerimeter_congr_ae lam hEF).1 hE
  change (relaxedPerimeter lam E).toReal =
    (relaxedPerimeter lam F).toReal
  apply (ENNReal.toReal_eq_toReal_iff'
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hE).ne
    (relaxedSourceSemantics_relaxedPerimeter_lt_top hF).ne).2
  exact relaxedPerimeter_congr_ae lam hEF

/-- A source-admissible representative that is almost everywhere a horizontal
translate of a canonical type-(iv) carrier has the existing exact
`NormalizationWitness`.  Perimeter finiteness is transported before conversion
to `ℝ`; weighted-area integrability is retained explicitly on both the source
and normalized representatives. -/
theorem relaxedSourceSemantics_normalizationWitness_of_almostEverywhereHorizontalCongruence
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hsourceAdmissible :
      (relaxedSourceSemantics lam).IsAdmissible sourceCarrier)
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent
        sourceCarrier profile.carrier) :
    (relaxedSourceSemantics lam).NormalizationWitness
      sourceCarrier profile := by
  rcases hcongruent with ⟨t, hsource_eq⟩
  have hsourceFinite :
      (relaxedSourceSemantics lam).IsFinitePerimeter sourceCarrier :=
    hsourceAdmissible.1
  have htranslated :
      (relaxedSourceSemantics lam).IsFinitePerimeter
        (horizontalTranslation t '' profile.carrier) :=
    (relaxedSourceSemantics_isFinitePerimeter_congr_ae
      lam hsource_eq).1 hsourceFinite
  have hprofile :
      (relaxedSourceSemantics lam).IsFinitePerimeter profile.carrier :=
    (relaxedSourceSemantics_isFinitePerimeter_horizontalTranslation_iff
      lam t profile.carrier).1 htranslated
  constructor
  · exact ⟨hprofile, profile.integrableOn_carrier⟩
  · calc
      _root_.WeightedArea lam sourceCarrier =
          _root_.WeightedArea lam
            (horizontalTranslation t '' profile.carrier) :=
        weightedArea_congr_ae lam hsource_eq
      _ = _root_.WeightedArea lam profile.carrier :=
        weightedArea_horizontalTranslation lam t profile.carrier
  · calc
      (relaxedSourceSemantics lam).perimeter sourceCarrier =
          (relaxedSourceSemantics lam).perimeter
            (horizontalTranslation t '' profile.carrier) :=
        relaxedSourceSemantics_perimeter_congr_ae
          lam hsourceFinite hsource_eq
      _ = (relaxedSourceSemantics lam).perimeter profile.carrier :=
        relaxedSourceSemantics_perimeter_horizontalTranslation
          lam t profile.carrier hprofile

/-- Exact horizontal classification is the special case of representative
classification with no null-set replacement. -/
theorem relaxedSourceSemantics_normalizationWitness_of_horizontalCongruence
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hsourceAdmissible :
      (relaxedSourceSemantics lam).IsAdmissible sourceCarrier)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier) :
    (relaxedSourceSemantics lam).NormalizationWitness
      sourceCarrier profile :=
  relaxedSourceSemantics_normalizationWitness_of_almostEverywhereHorizontalCongruence
    profile hsourceAdmissible
      (almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
        hcongruent)

/-- The existing minimizer-transfer consumer needs no caller-supplied
normalization witness for an almost-everywhere horizontally classified
source-admissible representative.  Reduced-boundary/model compatibility
remains an explicit, separate premise. -/
theorem relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_aeHorizontalCongruence
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent
        sourceCarrier profile.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel profile)
    (hsource :
      (relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    profile.toCandidate.IsWeightedPerimeterMinimizer :=
  (relaxedSourceSemantics lam)
    |>.candidate_isWeightedPerimeterMinimizer_of_sourceNormalization
      profile
        (relaxedSourceSemantics_normalizationWitness_of_almostEverywhereHorizontalCongruence
          profile hsource.1 hcongruent)
        compatibility hsource

/-- Exact horizontal classification has the same normalization-free modeled
minimizer transfer. -/
theorem relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel profile)
    (hsource :
      (relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    profile.toCandidate.IsWeightedPerimeterMinimizer :=
  relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_aeHorizontalCongruence
    profile
      (almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
        hcongruent)
      compatibility hsource

/-- A source-faithful positive-volume example for the approximation class. -/
def unitDisk : Set PlanePoint :=
  {p | p.1 ^ 2 + p.2 ^ 2 < 1}

theorem isOpen_unitDisk : IsOpen unitDisk := by
  exact isOpen_lt (by fun_prop) continuous_const

/-- The unit disk has the required local one-sided regular defining function. -/
theorem isSmoothDomain_unitDisk : IsSmoothDomain unitDisk := by
  constructor
  · exact isOpen_unitDisk
  · intro p hp
    have hpCircle : p.1 ^ 2 + p.2 ^ 2 = 1 := by
      unfold unitDisk at hp
      exact frontier_lt_subset_eq
        (show Continuous (fun q : PlanePoint => q.1 ^ 2 + q.2 ^ 2) by
          fun_prop)
        continuous_const hp
    let D : PlanePoint →L[ℝ] ℝ :=
      (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
    have hderiv :
        HasFDerivAt (fun q : PlanePoint => q.1 ^ 2 + q.2 ^ 2 - 1) D p := by
      simpa [D, Pi.add_apply] using
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).add
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2)).sub_const 1
    have hD : D ≠ 0 := by
      intro hzero
      have happ := congrArg (fun L : PlanePoint →L[ℝ] ℝ => L p) hzero
      simp [D] at happ
      nlinarith
    refine ⟨Set.univ, (fun q : PlanePoint => q.1 ^ 2 + q.2 ^ 2 - 1),
      D, isOpen_univ, Set.mem_univ p, ?_, ?_, hderiv, hD, ?_⟩
    · fun_prop
    · nlinarith
    · ext q
      change
        ((q.1 ^ 2 + q.2 ^ 2 < 1) ∧ True) ↔
          (True ∧ q.1 ^ 2 + q.2 ^ 2 - 1 < 0)
      constructor
      · rintro ⟨h, -⟩
        exact ⟨trivial, by linarith⟩
      · rintro ⟨-, h⟩
        exact ⟨by linarith, trivial⟩

/-- The disk witness is genuinely two-dimensional: its Lebesgue volume is
strictly positive. -/
theorem volume_unitDisk_pos : 0 < volume unitDisk := by
  let Q : Set PlanePoint :=
    Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)
  have hQ : Q ⊆ unitDisk := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change (-(1 / 2 : ℝ) < x ∧ x < 1 / 2) at hx
    change (-(1 / 2 : ℝ) < y ∧ y < 1 / 2) at hy
    change x ^ 2 + y ^ 2 < 1
    have hx' : x ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      rw [sq_lt_sq, abs_lt]
      constructor <;> norm_num <;> linarith [hx.1, hx.2]
    have hy' : y ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      rw [sq_lt_sq, abs_lt]
      constructor <;> norm_num <;> linarith [hy.1, hy.2]
    norm_num at hx' hy' ⊢
    linarith
  have hmeasure : volume Q ≤ volume unitDisk :=
    measure_mono (μ := volume) hQ
  have hQvolume : volume Q = 1 := by
    simp [Q, Measure.volume_eq_prod, Real.volume_Ioo]
    norm_num
  rw [hQvolume] at hmeasure
  exact zero_lt_one.trans_le hmeasure

/-- Coordinate isometry from the standard complex plane to the repository's
Euclidean `L2` realization. -/
private def complexToEuclidean (z : ℂ) : EuclideanPlane :=
  WithLp.toLp 2 (z.re, z.im)

private theorem isometry_complexToEuclidean :
    Isometry complexToEuclidean := by
  apply Isometry.of_dist_eq
  intro z w
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  norm_num [complexToEuclidean, Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Complex.dist_eq_re_im]

theorem unitDisk_eq_preimage_ball :
    unitDisk =
      planeEuclideanHomeomorph ⁻¹'
        Metric.ball (0 : EuclideanPlane) 1 := by
  ext q
  change (q.1 ^ 2 + q.2 ^ 2 < 1) ↔
    dist (WithLp.toLp 2 q) 0 < 1
  rw [dist_zero_right]
  have hsq :
      ‖WithLp.toLp 2 q‖ ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by
    simpa [sq_abs] using
      WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 q)
  rw [← (sq_lt_sq₀ (norm_nonneg (WithLp.toLp 2 q)) zero_le_one)]
  rw [hsq]
  norm_num

theorem unitDisk_euclidean_image :
    planeEuclideanHomeomorph '' unitDisk =
      Metric.ball (0 : EuclideanPlane) 1 := by
  rw [unitDisk_eq_preimage_ball]
  exact planeEuclideanHomeomorph.surjective.image_preimage _

private theorem complexToEuclidean_zero :
    complexToEuclidean 0 = 0 := by
  rfl

private theorem euclidean_unitSphere_subset_circleImage :
    Metric.sphere (0 : EuclideanPlane) 1 ⊆
      complexToEuclidean ''
        (unitCircleArc 1 '' Icc (-Real.pi) Real.pi) := by
  intro x hx
  let z : ℂ := ⟨(WithLp.ofLp x).1, (WithLp.ofLp x).2⟩
  have hzmap : complexToEuclidean z = x := by
    rfl
  have hnorm : ‖z‖ = 1 := by
    have hdist := isometry_complexToEuclidean.dist_eq z 0
    rw [complexToEuclidean_zero, dist_zero_right, dist_zero_right,
      hzmap] at hdist
    rw [Metric.mem_sphere, dist_zero_right] at hx
    linarith
  have hs_mem : z.arg ∈ Icc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z |>.le, Complex.arg_le_pi z⟩
  have harc : unitCircleArc 1 z.arg = z := by
    simpa [unitCircleArc, hnorm, mul_comm] using
      Complex.norm_mul_exp_arg_mul_I z
  exact ⟨z, ⟨z.arg, hs_mem, harc⟩, hzmap⟩

/-- The complete Euclidean frontier of the unit disk has finite `H¹` mass.
The proof bounds it by one signed-arclength parametrization of the circle. -/
theorem unitDisk_frontier_h1_ne_top :
    (μH[1] : Measure EuclideanPlane)
      (frontier (planeEuclideanHomeomorph '' unitDisk)) ≠ ⊤ := by
  rw [unitDisk_euclidean_image,
    frontier_ball (0 : EuclideanPlane) one_ne_zero]
  apply ne_of_lt
  apply lt_of_le_of_lt
    (measure_mono euclidean_unitSphere_subset_circleImage)
  apply lt_of_le_of_lt
    ((isometry_complexToEuclidean.hausdorffMeasure_image
      (Or.inl (by norm_num))
      (unitCircleArc 1 '' Icc (-Real.pi) Real.pi)).le)
  apply lt_of_le_of_lt
    (hausdorffMeasure_unitCircleArc_image_le one_pos)
  exact ENNReal.ofReal_lt_top

/-- The positive-volume disk has finite extended smooth cost for every density
parameter. -/
theorem smoothCost_unitDisk_lt_top (lam : ℝ) :
    smoothCost lam unitDisk < ⊤ := by
  exact (stripDensity_integrable_frontierMeasure_of_measure_ne_top
    lam unitDisk_frontier_h1_ne_top).lintegral_lt_top

/-- Constant smooth approximation by the unit disk itself. -/
def unitDiskConstantSequence : SmoothSequence where
  carrier _ := unitDisk
  smooth _ := isSmoothDomain_unitDisk

theorem unitDiskConstantSequence_converges :
    unitDiskConstantSequence.ConvergesTo unitDisk := by
  unfold SmoothSequence.ConvergesTo characteristicDistance
  simpa [unitDiskConstantSequence] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
      atTop (𝓝 0))

@[simp] theorem unitDiskConstantSequence_cost (lam : ℝ) :
    unitDiskConstantSequence.cost lam = smoothCost lam unitDisk := by
  unfold SmoothSequence.cost
  simp [unitDiskConstantSequence]

theorem unitDiskConstantSequence_cost_lt_top (lam : ℝ) :
    unitDiskConstantSequence.cost lam < ⊤ := by
  rw [unitDiskConstantSequence_cost]
  exact smoothCost_unitDisk_lt_top lam

/-- The concrete relaxation has a finite value on a positive-volume target,
witnessed without assuming existence of an optimal approximating sequence. -/
theorem relaxedPerimeter_unitDisk_lt_top (lam : ℝ) :
    relaxedPerimeter lam unitDisk < ⊤ := by
  apply lt_of_le_of_lt
    (sInf_le (s := {c : ℝ≥0∞ | ∃ A : SmoothSequence,
      NullMeasurableSet unitDisk volume ∧ A.ConvergesTo unitDisk ∧
        A.cost lam = c}) ?_)
    (unitDiskConstantSequence_cost_lt_top lam)
  exact ⟨unitDiskConstantSequence,
    isOpen_unitDisk.measurableSet.nullMeasurableSet,
    unitDiskConstantSequence_converges, rfl⟩

end CMVRelaxation
