/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Compactly supported smooth ambient transport

This module packages a global smooth ambient equivalence of the coordinate
plane and transports the complete smooth recovery class through it.  The
transport uses literal set images.  Compact support supplies global
bi-Lipschitz bounds, hence preserves characteristic-function convergence.
-/

open Set Filter MeasureTheory Metric Function
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation
/-- Every compact set inside an open planar set admits a `C∞`, compactly
supported cutoff equal to one on that compact set and supported in the given
open set. -/
theorem exists_smoothCompactCutoff
    {K U : Set PlanePoint} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ beta : PlanePoint → ℝ,
      ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
        tsupport beta ⊆ U ∧ EqOn beta 1 K := by
  obtain ⟨L, hLcomp, hLclosed, hKintL, hLU⟩ :=
    exists_compact_closed_between hK hU hKU
  obtain ⟨M, _hMcomp, hMclosed, hLintM, hMU⟩ :=
    exists_compact_closed_between hLcomp hU hLU
  have hdisj : Disjoint L (interior M)ᶜ :=
    disjoint_compl_right_iff_subset.mpr hLintM
  obtain ⟨f, hfL, hfM, hfcompact, _hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hLcomp
      isOpen_interior.isClosed_compl hdisj
  have hf_smooth : ContDiffOn ℝ ∞ (f : PlanePoint → ℝ) L :=
    contDiffOn_const.congr fun x hx => by
      simpa using hfL hx
  obtain ⟨beta, hbeta_smooth, _hbeta_approx, hbetaK, hbeta_support⟩ :=
    f.continuous.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞) continuous_const
      (fun _ => zero_lt_one) hK.isClosed
      (subset_interior_iff_mem_nhdsSet.mp hKintL) hf_smooth
  have hf_support : support (f : PlanePoint → ℝ) ⊆ interior M := by
    intro x hx
    by_contra hxM
    exact hx (hfM hxM)
  have hf_tsupport : tsupport (f : PlanePoint → ℝ) ⊆ M :=
    closure_minimal (hf_support.trans interior_subset) hMclosed
  refine ⟨beta, hbeta_smooth,
    hfcompact.mono' (hbeta_support.trans subset_closure), ?_, ?_⟩
  · exact (closure_mono hbeta_support).trans (hf_tsupport.trans hMU)
  · exact hbetaK.trans (hfL.mono (hKintL.trans interior_subset))


/-- A global `C∞` ambient equivalence whose displacement has compact support. -/
structure SmoothAmbientEquiv where
  toHomeomorph : PlanePoint ≃ₜ PlanePoint
  contDiff_toFun : ContDiff ℝ ∞ toHomeomorph
  contDiff_invFun : ContDiff ℝ ∞ toHomeomorph.symm
  hasCompactSupport_displacement :
    HasCompactSupport (fun p : PlanePoint => toHomeomorph p - p)

namespace SmoothAmbientEquiv

instance : CoeFun SmoothAmbientEquiv (fun _ => PlanePoint → PlanePoint) :=
  ⟨fun Φ => Φ.toHomeomorph⟩

@[simp] theorem coe_toHomeomorph (Φ : SmoothAmbientEquiv) :
    (Φ.toHomeomorph : PlanePoint → PlanePoint) = Φ := rfl

@[simp] theorem symm_apply_apply (Φ : SmoothAmbientEquiv) (p : PlanePoint) :
    Φ.toHomeomorph.symm (Φ p) = p :=
  Φ.toHomeomorph.symm_apply_apply p

@[simp] theorem apply_symm_apply (Φ : SmoothAmbientEquiv) (p : PlanePoint) :
    Φ (Φ.toHomeomorph.symm p) = p :=
  Φ.toHomeomorph.apply_symm_apply p

/-- The compact set outside which the ambient equivalence is literally the identity. -/
def movedSet (Φ : SmoothAmbientEquiv) : Set PlanePoint :=
  tsupport (fun p : PlanePoint => Φ p - p)

lemma movedSet_isCompact (Φ : SmoothAmbientEquiv) : IsCompact Φ.movedSet :=
  Φ.hasCompactSupport_displacement

lemma apply_eq_self_of_not_mem_movedSet (Φ : SmoothAmbientEquiv) {p : PlanePoint}
    (hp : p ∉ Φ.movedSet) : Φ p = p := by
  by_contra hne
  exact hp (subset_tsupport _ (sub_ne_zero.mpr hne))

lemma mem_image_iff (Φ : SmoothAmbientEquiv) (E : Set PlanePoint) (p : PlanePoint) :
    p ∈ Φ '' E ↔ Φ.toHomeomorph.symm p ∈ E := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨Φ.toHomeomorph.symm p, hp, Φ.apply_symm_apply p⟩

/-- The inverse displacement is compactly supported as well. -/
lemma hasCompactSupport_inverseDisplacement (Φ : SmoothAmbientEquiv) :
    HasCompactSupport (fun p : PlanePoint => Φ.toHomeomorph.symm p - p) := by
  refine IsCompact.of_isClosed_subset
    (Φ.movedSet_isCompact.image Φ.toHomeomorph.continuous) isClosed_closure ?_
  apply closure_minimal
  · intro p hp
    change Φ.toHomeomorph.symm p - p ≠ 0 at hp
    let q := Φ.toHomeomorph.symm p
    have hq : q ∈ Φ.movedSet := by
      apply subset_tsupport
      change Φ q - q ≠ 0
      rw [sub_ne_zero]
      intro heq
      apply hp
      rw [sub_eq_zero]
      exact heq.symm.trans (Φ.apply_symm_apply p)
    exact ⟨q, hq, Φ.apply_symm_apply p⟩
  · exact (Φ.movedSet_isCompact.image Φ.toHomeomorph.continuous).isClosed

private lemma contDiff_displacement (Φ : SmoothAmbientEquiv) :
    ContDiff ℝ ∞ (fun p : PlanePoint => Φ p - p) :=
  Φ.contDiff_toFun.sub contDiff_id

private lemma contDiff_inverseDisplacement (Φ : SmoothAmbientEquiv) :
    ContDiff ℝ ∞ (fun p : PlanePoint => Φ.toHomeomorph.symm p - p) :=
  Φ.contDiff_invFun.sub contDiff_id

/-- Every compactly supported smooth ambient equivalence is globally Lipschitz. -/
theorem exists_lipschitzWith (Φ : SmoothAmbientEquiv) :
    ∃ K : ℝ≥0, LipschitzWith K Φ := by
  obtain ⟨C, hC⟩ := Φ.contDiff_displacement.lipschitzWith_of_hasCompactSupport
    Φ.hasCompactSupport_displacement (by simp)
  refine ⟨1 + C, ?_⟩
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    isometry_id.lipschitz.add hC

/-- The inverse of a compactly supported smooth ambient equivalence is globally Lipschitz. -/
theorem exists_lipschitzWith_symm (Φ : SmoothAmbientEquiv) :
    ∃ K : ℝ≥0, LipschitzWith K Φ.toHomeomorph.symm := by
  obtain ⟨C, hC⟩ := Φ.contDiff_inverseDisplacement.lipschitzWith_of_hasCompactSupport
    Φ.hasCompactSupport_inverseDisplacement (by simp)
  refine ⟨1 + C, ?_⟩
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    isometry_id.lipschitz.add hC

/-- A global Lipschitz ambient map controls planar Lebesgue volume by the square
of its Lipschitz constant. -/
theorem volume_image_le (Φ : SmoothAmbientEquiv) {K : ℝ≥0}
    (hK : LipschitzWith K Φ) (E : Set PlanePoint) :
    volume (Φ '' E) ≤ (K : ℝ≥0∞) ^ (2 : ℝ) * volume E := by
  simpa only [hausdorffMeasure_prod_real] using
    hK.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num) E

/-- Null measurability is preserved by literal image under a smooth ambient
 equivalence. -/
theorem nullMeasurableSet_image (Φ : SmoothAmbientEquiv) {E : Set PlanePoint}
    (hE : NullMeasurableSet E volume) : NullMeasurableSet (Φ '' E) volume := by
  exact nullMeasurable_image_of_fderivWithin volume hE
    (fun p _ =>
      (Φ.contDiff_toFun.differentiable (by simp)).differentiableAt.hasFDerivAt
        |>.hasFDerivWithinAt)
    Φ.toHomeomorph.injective.injOn

private lemma inverse_fderiv_comp_fderiv (Φ : SmoothAmbientEquiv) (q : PlanePoint) :
    (fderiv ℝ (Φ.toHomeomorph.symm : PlanePoint → PlanePoint) (Φ q)).comp
        (fderiv ℝ (Φ : PlanePoint → PlanePoint) q) =
      ContinuousLinearMap.id ℝ PlanePoint := by
  have hcomp :=
    (Φ.contDiff_invFun.differentiable (by simp)).differentiableAt.hasFDerivAt.comp q
      (Φ.contDiff_toFun.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hid : HasFDerivAt
      ((Φ.toHomeomorph.symm : PlanePoint → PlanePoint) ∘ Φ)
        (ContinuousLinearMap.id ℝ PlanePoint) q := by
    have hfun :
        ((Φ.toHomeomorph.symm : PlanePoint → PlanePoint) ∘ Φ) = id := by
      funext p
      exact Φ.symm_apply_apply p
    rw [hfun]
    exact hasFDerivAt_id (𝕜 := ℝ) q
  exact hcomp.unique hid

private lemma definingDerivative_comp_inverse_ne_zero
    (Φ : SmoothAmbientEquiv) {q : PlanePoint} {D : PlanePoint →L[ℝ] ℝ}
    (hD : D ≠ 0) :
    D.comp (fderiv ℝ (Φ.toHomeomorph.symm : PlanePoint → PlanePoint) (Φ q)) ≠ 0 := by
  intro hzero
  apply hD
  apply ContinuousLinearMap.ext
  intro z
  have hident := DFunLike.congr_fun
    (Φ.inverse_fderiv_comp_fderiv q) z
  have hz := DFunLike.congr_fun hzero
    ((fderiv ℝ (Φ : PlanePoint → PlanePoint) q) z)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hident hz
  rw [hident] at hz
  simpa using hz

/-- Smooth ambient equivalences preserve the concrete local one-sided smooth
 domain class. -/
theorem IsSmoothDomain.image {U : Set PlanePoint} (hU : IsSmoothDomain U)
    (Φ : SmoothAmbientEquiv) : IsSmoothDomain (Φ '' U) := by
  constructor
  · exact Φ.toHomeomorph.isOpenMap U hU.isOpen
  · intro p hp
    rw [← Φ.toHomeomorph.image_frontier] at hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hU.regular_boundary q hq with
      ⟨V, g, D, hVopen, hqV, hg, hgq, hderiv, hD, hlocal⟩
    let Ψ : PlanePoint → PlanePoint := Φ.toHomeomorph.symm
    let VΦ : Set PlanePoint := Ψ ⁻¹' V
    let DΦ : PlanePoint →L[ℝ] ℝ :=
      D.comp (fderiv ℝ Ψ (Φ q))
    refine ⟨VΦ, g ∘ Ψ, DΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hVopen.preimage Φ.toHomeomorph.symm.continuous
    · change Φ.toHomeomorph.symm (Φ q) ∈ V
      simpa using hqV
    · exact hg.comp Φ.contDiff_invFun.contDiffOn (fun _ hz => hz)
    · change g (Ψ (Φ q)) = 0
      simpa [Ψ] using hgq
    · have hgAt : HasFDerivAt g D (Ψ (Φ q)) := by
        simpa [Ψ] using hderiv
      exact hgAt.comp (Φ q)
        (Φ.contDiff_invFun.differentiable (by simp)).differentiableAt.hasFDerivAt
    · exact Φ.definingDerivative_comp_inverse_ne_zero hD
    · ext z
      have hz := Set.ext_iff.mp hlocal (Ψ z)
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      change (z ∈ Φ '' U ∧ Ψ z ∈ V) ↔ (Ψ z ∈ V ∧ g (Ψ z) < 0)
      simpa only [Φ.mem_image_iff] using hz

/-- Literal termwise image of every smooth recovery sequence. -/
def ambientImage (Φ : SmoothAmbientEquiv)
    (A : SmoothSequence) : SmoothSequence where
  carrier n := Φ '' A.carrier n
  smooth n := IsSmoothDomain.image (A.smooth n) Φ

@[simp] theorem ambientImage_carrier (Φ : SmoothAmbientEquiv)
    (A : SmoothSequence) (n : ℕ) :
    (Φ.ambientImage A).carrier n = Φ '' A.carrier n := rfl

/-- Literal image commutes with symmetric difference for an ambient equivalence. -/
theorem image_symmDiff (Φ : SmoothAmbientEquiv) (E F : Set PlanePoint) :
    Φ '' (E ∆ F) = (Φ '' E) ∆ (Φ '' F) :=
  Set.image_symmDiff Φ.toHomeomorph.injective E F

/-- Ambient image controls characteristic distance by the square of any global
 Lipschitz constant. -/
theorem characteristicDistance_image_le (Φ : SmoothAmbientEquiv) {K : ℝ≥0}
    (hK : LipschitzWith K Φ) (E F : Set PlanePoint) :
    characteristicDistance (Φ '' E) (Φ '' F) ≤
      (K : ℝ≥0∞) ^ (2 : ℝ) * characteristicDistance E F := by
  rw [characteristicDistance, characteristicDistance, ← Φ.image_symmDiff]
  exact Φ.volume_image_le hK (E ∆ F)

/-- Every convergent smooth recovery sequence remains convergent after literal
 ambient transport, to the literal image of its target. -/
theorem convergesTo_ambientImage
    (Φ : SmoothAmbientEquiv) (A : SmoothSequence) (E : Set PlanePoint)
    (hA : A.ConvergesTo E) :
    (Φ.ambientImage A).ConvergesTo (Φ '' E) := by
  obtain ⟨K, hK⟩ := Φ.exists_lipschitzWith
  unfold SmoothSequence.ConvergesTo at hA ⊢
  have hupper : Tendsto
      (fun n => (K : ℝ≥0∞) ^ (2 : ℝ) * characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      (a := (K : ℝ≥0∞) ^ (2 : ℝ)) hA (Or.inr (by finiteness))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le)
    (fun n => Φ.characteristicDistance_image_le hK (A.carrier n) E)

/-- Outside the compact moved set, membership in every carrier and its literal
 ambient image is unchanged. -/
theorem mem_image_iff_of_not_mem_movedSet (Φ : SmoothAmbientEquiv)
    (E : Set PlanePoint) {p : PlanePoint} (hp : p ∉ Φ.movedSet) :
    p ∈ Φ '' E ↔ p ∈ E := by
  rw [Φ.mem_image_iff]
  have hfix := Φ.apply_eq_self_of_not_mem_movedSet hp
  have hinv : Φ.toHomeomorph.symm p = p := by
    have := congrArg Φ.toHomeomorph.symm hfix
    simpa using this.symm
  rw [hinv]


/-! ## Small compactly supported smooth perturbations of the identity -/

private lemma scaledField_lipschitz
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) :
    LipschitzWith (‖t‖₊ * L) (fun p => t • F p) :=
  (lipschitzWith_smul t).comp hF

private lemma translatedContraction
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1)
    (y : PlanePoint) :
    ContractingWith (‖t‖₊ * L) (fun p => y - t • F p) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
  simpa only [dist_comm, dist_eq_norm] using
    (scaledField_lipschitz (t := t) hF).dist_le_mul q p

private noncomputable def perturbationInverse
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1)
    (y : PlanePoint) : PlanePoint :=
  (translatedContraction hF hsmall y).fixedPoint
    (fun p => y - t • F p)

private lemma perturbationInverse_spec
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1)
    (y : PlanePoint) :
    perturbationInverse hF hsmall y +
        t • F (perturbationInverse hF hsmall y) = y := by
  have hfix :=
    (translatedContraction hF hsmall y).fixedPoint_isFixedPt
  change y - t • F (perturbationInverse hF hsmall y) =
    perturbationInverse hF hsmall y at hfix
  calc
    perturbationInverse hF hsmall y +
          t • F (perturbationInverse hF hsmall y) =
        (y - t • F (perturbationInverse hF hsmall y)) +
          t • F (perturbationInverse hF hsmall y) :=
      congrArg
        (fun z => z + t • F (perturbationInverse hF hsmall y))
        hfix.symm
    _ = y := by abel

private lemma perturbationInverse_apply
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1)
    (x : PlanePoint) :
    perturbationInverse hF hsmall (x + t • F x) = x := by
  symm
  apply
    (translatedContraction hF hsmall (x + t • F x)).fixedPoint_unique
  change x + t • F x - t • F x = x
  abel

private noncomputable def smallPerturbationHomeomorph
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1) :
    PlanePoint ≃ₜ PlanePoint where
  toFun p := p + t • F p
  invFun := perturbationInverse hF hsmall
  left_inv := perturbationInverse_apply hF hsmall
  right_inv := perturbationInverse_spec hF hsmall
  continuous_toFun :=
    (LipschitzWith.id.add (scaledField_lipschitz (t := t) hF)).continuous
  continuous_invFun := by
    apply
      ((AntilipschitzWith.id.add_lipschitzWith
        (scaledField_lipschitz (t := t) hF)
        (by simpa using hsmall)).to_rightInverse
          (perturbationInverse_spec hF hsmall)).continuous

private noncomputable def perturbationFDerivEquiv
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hsmall : ‖t‖₊ * L < 1)
    (p : PlanePoint) : PlanePoint ≃L[ℝ] PlanePoint := by
  let A : PlanePoint →L[ℝ] PlanePoint :=
    (1 : PlanePoint →L[ℝ] PlanePoint) + t • fderiv ℝ F p
  have hsmallReal : ‖t‖ * (L : ℝ) < 1 := by
    exact_mod_cast hsmall
  have hnorm : ‖-(t • fderiv ℝ F p)‖ < 1 := by
    calc
      ‖-(t • fderiv ℝ F p)‖ = ‖t‖ * ‖fderiv ℝ F p‖ := by
        rw [norm_neg, norm_smul]
      _ ≤ ‖t‖ * (L : ℝ) :=
        mul_le_mul_of_nonneg_left
          (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg t)
      _ < 1 := hsmallReal
  have hunit : IsUnit A := by
    simpa only [A, sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one hnorm)
  have hbij : Function.Bijective A :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  exact ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2)

private lemma hasFDerivAt_smallPerturbation
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hF_smooth : ContDiff ℝ ∞ F)
    (hsmall : ‖t‖₊ * L < 1) (p : PlanePoint) :
    HasFDerivAt (smallPerturbationHomeomorph hF hsmall)
      (perturbationFDerivEquiv hF hsmall p :
        PlanePoint →L[ℝ] PlanePoint) p := by
  change HasFDerivAt (fun q : PlanePoint => q + t • F q)
    (ContinuousLinearMap.id ℝ PlanePoint + t • fderiv ℝ F p) p
  exact (hasFDerivAt_id p).add
    ((hF_smooth.differentiable (by simp) p).hasFDerivAt.const_smul t)

/-- A compactly supported `C∞` Lipschitz vector field generates a genuine
global smooth ambient equivalence whenever its scaled Lipschitz constant is
strictly below one.  The map is literally `p ↦ p + t • F p`; its inverse is
constructed by the contraction theorem and is proved smooth by the inverse
function theorem. -/
noncomputable def ofSmallPerturbation
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hF_smooth : ContDiff ℝ ∞ F)
    (hF_compact : HasCompactSupport F) (hsmall : ‖t‖₊ * L < 1) :
    SmoothAmbientEquiv where
  toHomeomorph := smallPerturbationHomeomorph hF hsmall
  contDiff_toFun := by
    change ContDiff ℝ ∞ (fun p : PlanePoint => p + t • F p)
    exact contDiff_id.add (hF_smooth.const_smul t)
  contDiff_invFun :=
    (smallPerturbationHomeomorph hF hsmall).contDiff_symm
      (fun p =>
        hasFDerivAt_smallPerturbation hF hF_smooth hsmall p)
      (by
        change ContDiff ℝ ∞ (fun p : PlanePoint => p + t • F p)
        exact contDiff_id.add (hF_smooth.const_smul t))
  hasCompactSupport_displacement := by
    change HasCompactSupport (fun p : PlanePoint => (p + t • F p) - p)
    rw [show (fun p : PlanePoint => (p + t • F p) - p) =
        fun p => t • F p by
      funext p
      abel]
    exact IsCompact.of_isClosed_subset hF_compact (isClosed_tsupport _)
      (tsupport_smul_subset_right (fun _ : PlanePoint => t) F)

@[simp] theorem ofSmallPerturbation_apply
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hF_smooth : ContDiff ℝ ∞ F)
    (hF_compact : HasCompactSupport F) (hsmall : ‖t‖₊ * L < 1)
    (p : PlanePoint) :
    ofSmallPerturbation hF hF_smooth hF_compact hsmall p =
      p + t • F p :=
  rfl

/-- The compact moved set of a small perturbation is contained in the closed
support of its generating vector field. -/
theorem movedSet_ofSmallPerturbation_subset
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hF_smooth : ContDiff ℝ ∞ F)
    (hF_compact : HasCompactSupport F) (hsmall : ‖t‖₊ * L < 1) :
    (ofSmallPerturbation hF hF_smooth hF_compact hsmall).movedSet ⊆
      tsupport F := by
  unfold movedSet
  change tsupport (fun p : PlanePoint => (p + t • F p) - p) ⊆
    tsupport F
  rw [show (fun p : PlanePoint => (p + t • F p) - p) =
      fun p => t • F p by
    funext p
    abel]
  exact tsupport_smul_subset_right (fun _ : PlanePoint => t) F

/-- Every vertical fiber of a small perturbation is strictly ordered in its
second coordinate.  This is the order-preserving ingredient for literal graph
and occupied-side transport. -/
theorem ofSmallPerturbation_fiber_strictMono
    {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}
    (hF : LipschitzWith L F) (hF_smooth : ContDiff ℝ ∞ F)
    (hF_compact : HasCompactSupport F) (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) :
    StrictMono (fun y : ℝ =>
      (ofSmallPerturbation hF hF_smooth hF_compact hsmall (x, y)).2) := by
  intro y z hyz
  have hsmallReal : |t| * (L : ℝ) < 1 := by
    simpa only [Real.norm_eq_abs] using
      (show ‖t‖ * (L : ℝ) < 1 by
        exact_mod_cast hsmall)
  have hcoord :
      |(F (x, z)).2 - (F (x, y)).2| ≤
        (L : ℝ) * (z - y) := by
    calc
      |(F (x, z)).2 - (F (x, y)).2| =
          dist (F (x, z)).2 (F (x, y)).2 := by
            rw [Real.dist_eq]
      _ ≤ dist (F (x, z)) (F (x, y)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ ≤ (L : ℝ) * dist (x, z) (x, y) :=
        hF.dist_le_mul (x, z) (x, y)
      _ = (L : ℝ) * (z - y) := by
        rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        rw [abs_of_pos (sub_pos.mpr hyz),
          max_eq_right (sub_nonneg.mpr hyz.le)]
  have hpert :
      |t * ((F (x, z)).2 - (F (x, y)).2)| < z - y := by
    rw [abs_mul]
    calc
      |t| * |(F (x, z)).2 - (F (x, y)).2| ≤
          |t| * ((L : ℝ) * (z - y)) :=
        mul_le_mul_of_nonneg_left hcoord (abs_nonneg t)
      _ = (|t| * (L : ℝ)) * (z - y) := by ring
      _ < 1 * (z - y) :=
        mul_lt_mul_of_pos_right hsmallReal (sub_pos.mpr hyz)
      _ = z - y := one_mul _
  change y + t * (F (x, y)).2 < z + t * (F (x, z)).2
  have hlower :=
    neg_abs_le (t * ((F (x, z)).2 - (F (x, y)).2))
  nlinarith

end SmoothAmbientEquiv

end CMVRelaxation
