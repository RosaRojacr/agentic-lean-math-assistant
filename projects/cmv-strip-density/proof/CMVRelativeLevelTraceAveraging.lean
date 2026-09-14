import CMVRelativeParameterSelection

open Set Function Filter MeasureTheory
open scoped Topology ContDiff symmDiff Manifold ENNReal BigOperators

noncomputable section

namespace CMVRelaxation

/-- Compact graph trace used as an actual level set of an affine-normal phase. -/
def affineNormalLevelTrace (g : ℝ → ℝ) (a b t : ℝ) : Set PlanePoint :=
  (fun x => (x, g x + t)) '' Icc a b

lemma isCompact_affineNormalLevelTrace {g : ℝ → ℝ} (hg : Continuous g)
    (a b t : ℝ) : IsCompact (affineNormalLevelTrace g a b t) := by
  exact isCompact_Icc.image ((continuous_id.prodMk (hg.add continuous_const)))

lemma weightedTraceCost_eq_const_mul_hausdorff
    (lam w : ℝ) {S : Set PlanePoint} (hS : IsCompact S)
    (hdensity : ∀ p ∈ S, StripDensity lam p = w) :
    weightedTraceCost lam S = ENNReal.ofReal w *
      (μH[1] : Measure EuclideanPlane) (planeEuclideanHomeomorph '' S) := by
  unfold weightedTraceCost
  have hmeas : MeasurableSet (planeEuclideanHomeomorph '' S) :=
    (hS.image planeEuclideanHomeomorph.continuous).measurableSet
  calc
    (∫⁻ z in planeEuclideanHomeomorph '' S,
        ENNReal.ofReal (euclideanStripDensity lam z)
        ∂(μH[1] : Measure EuclideanPlane)) =
        ∫⁻ _z in planeEuclideanHomeomorph '' S, ENNReal.ofReal w
          ∂(μH[1] : Measure EuclideanPlane) := by
      apply setLIntegral_congr_fun hmeas
      rintro z ⟨p, hp, rfl⟩
      change ENNReal.ofReal
        (StripDensity lam
          (planeEuclideanHomeomorph.symm (planeEuclideanHomeomorph p))) =
        ENNReal.ofReal w
      rw [planeEuclideanHomeomorph.symm_apply_apply, hdensity p hp]
    _ = _ := by simp

lemma euclidean_image_affineNormalLevelTrace (g : ℝ → ℝ)
    (a b t : ℝ) :
    planeEuclideanHomeomorph '' affineNormalLevelTrace g a b t =
      IsometryEquiv.addLeft (WithLp.toLp 2 ((0, t) : PlanePoint)) ''
        (planeEuclideanHomeomorph '' affineNormalLevelTrace g a b 0) := by
  rw [affineNormalLevelTrace, affineNormalLevelTrace,
    Set.image_image, Set.image_image, Set.image_image]
  apply congrArg (fun h : ℝ → EuclideanPlane => h '' Icc a b)
  funext x
  simp only [planeEuclideanHomeomorph_apply,
    IsometryEquiv.addLeft_apply]
  rw [← WithLp.toLp_add]
  congr 1
  ext <;> simp [add_comm]

/-- Actual weighted `H¹` level-trace cost is constant across a compact family
that remains in one constant-density phase. -/
theorem weightedTraceCost_affineNormalLevelTrace_eq
    {lam w : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {a b s t : ℝ}
    (hs : ∀ p ∈ affineNormalLevelTrace g a b s,
      StripDensity lam p = w)
    (ht : ∀ p ∈ affineNormalLevelTrace g a b t,
      StripDensity lam p = w) :
    weightedTraceCost lam (affineNormalLevelTrace g a b s) =
      weightedTraceCost lam (affineNormalLevelTrace g a b t) := by
  rw [weightedTraceCost_eq_const_mul_hausdorff lam w
        (isCompact_affineNormalLevelTrace hg a b s) hs,
      weightedTraceCost_eq_const_mul_hausdorff lam w
        (isCompact_affineNormalLevelTrace hg a b t) ht]
  congr 1
  rw [euclidean_image_affineNormalLevelTrace g a b s,
    euclidean_image_affineNormalLevelTrace g a b t]
  let es : EuclideanPlane ≃ᵢ EuclideanPlane :=
    IsometryEquiv.addLeft (WithLp.toLp 2 ((0, s) : PlanePoint))
  let et : EuclideanPlane ≃ᵢ EuclideanPlane :=
    IsometryEquiv.addLeft (WithLp.toLp 2 ((0, t) : PlanePoint))
  rw [es.isometry.hausdorffMeasure_image (Or.inl (by norm_num)),
    et.isometry.hausdorffMeasure_image (Or.inl (by norm_num))]

/-- Phase whose compact level traces are vertical translates of one graph. -/
def affineNormalPhase (g : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  p.2 - g p.1

lemma affineNormalLevelTrace_eq_levelSet (g : ℝ → ℝ)
    (a b t : ℝ) :
    affineNormalLevelTrace g a b t =
      {p | p.1 ∈ Icc a b ∧ affineNormalPhase g p = t} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, by simp [affineNormalPhase]⟩
  · rintro ⟨hp, hlevel⟩
    refine ⟨p.1, hp, ?_⟩
    ext
    · rfl
    · dsimp [affineNormalPhase] at hlevel ⊢
      linarith

/-- Every value of an affine-normal phase is regular: its vertical derivative
is one. -/
theorem affineNormalPhase_regular
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (t : ℝ) :
    ∀ p : PlanePoint, affineNormalPhase g p = t →
      fderiv ℝ (affineNormalPhase g) p ≠ 0 := by
  intro p _hlevel hzero
  have hphase : DifferentiableAt ℝ (affineNormalPhase g) p := by
    unfold affineNormalPhase
    exact differentiableAt_snd.sub
      ((hg.differentiable (by simp) p.1).comp p differentiableAt_fst)
  have hline :
      HasDerivAt (fun y : ℝ => ((p.1, y) : PlanePoint)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hcomp :=
    hphase.hasFDerivAt.comp_hasDerivAt p.2 hline
  have hderiv :
      deriv (fun y : ℝ => affineNormalPhase g (p.1, y)) p.2 =
        fderiv ℝ (affineNormalPhase g) p (0, 1) := by
    simpa only [Function.comp_def] using hcomp.deriv
  have hone :
      deriv (fun y : ℝ => affineNormalPhase g (p.1, y)) p.2 = 1 := by
    simp [affineNormalPhase]
  rw [hone, hzero] at hderiv
  simp at hderiv

/-- The actual weighted `H¹` trace cost is measurable on any measurable
parameter set on which the trace remains in one constant-density phase. -/
theorem aemeasurable_weightedTraceCost_affineNormalLevelTrace
    {lam w : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    {J : Set ℝ} (hJ : MeasurableSet J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hdensity : ∀ t ∈ J, ∀ p ∈ affineNormalLevelTrace g a b t,
      StripDensity lam p = w) :
    AEMeasurable
      (fun t => weightedTraceCost lam
        (affineNormalLevelTrace g a b t))
      (volume.restrict J) := by
  let C := weightedTraceCost lam (affineNormalLevelTrace g a b t₀)
  have hC : AEMeasurable (fun _ : ℝ => C) (volume.restrict J) :=
    measurable_const.aemeasurable
  apply hC.congr
  filter_upwards [ae_restrict_mem hJ] with t ht
  exact weightedTraceCost_affineNormalLevelTrace_eq hg
    (hdensity t₀ ht₀) (hdensity t ht)

/-- On a protected compact phase interval, averaging the actual weighted
`H¹` level-trace cost returns that same trace cost. -/
theorem setLAverage_weightedTraceCost_affineNormalLevelTrace
    {lam w : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hJ₀ : volume J ≠ 0) (hJ_top : volume J ≠ (∞ : ℝ≥0∞))
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hdensity : ∀ t ∈ J, ∀ p ∈ affineNormalLevelTrace g a b t,
      StripDensity lam p = w) :
    (⨍⁻ t in J, weightedTraceCost lam
      (affineNormalLevelTrace g a b t) ∂volume) =
      weightedTraceCost lam (affineNormalLevelTrace g a b t₀) := by
  rw [setLAverage_congr_fun hJ
    (fun t ht => weightedTraceCost_affineNormalLevelTrace_eq hg
      (hdensity t ht) (hdensity t₀ ht₀))]
  exact setLAverage_const hJ₀ hJ_top _

/-- Sharp graph-speed upper bound, with coefficient one, for every translated
compact level trace in a constant-density phase. -/
theorem weightedTraceCost_affineNormalLevelTrace_le_intervalIntegral
    {lam w : ℝ} (hw : 0 ≤ w) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a b t : ℝ} (hab : a ≤ b)
    (hdensity : ∀ p ∈ affineNormalLevelTrace g a b t,
      StripDensity lam p = w) :
    weightedTraceCost lam (affineNormalLevelTrace g a b t) ≤
      ENNReal.ofReal
        (w * ∫ x in a..b,
          Real.sqrt
            (1 + (deriv (fun y => g y + t) x) ^ 2)) := by
  let gt : ℝ → ℝ := fun x => g x + t
  have hgt : ContDiff ℝ 1 gt := hg.add contDiff_const
  rw [weightedTraceCost_eq_const_mul_hausdorff lam w
    (isCompact_affineNormalLevelTrace hg.continuous a b t) hdensity]
  change ENNReal.ofReal w *
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, gt x)) '' Icc a b)) ≤
    ENNReal.ofReal
      (w * ∫ x in a..b, Real.sqrt (1 + (deriv gt x) ^ 2))
  calc
    ENNReal.ofReal w *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            ((fun x : ℝ => (x, gt x)) '' Icc a b)) ≤
        ENNReal.ofReal w *
          ENNReal.ofReal
            (∫ x in a..b, Real.sqrt (1 + (deriv gt x) ^ 2)) := by
      gcongr
      exact hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral
        hgt hab
    _ = _ := (ENNReal.ofReal_mul hw).symm

/-- Explicit curved compact level trace: a vertically translated parabola. -/
def quadraticLevelTrace (t : ℝ) : Set PlanePoint :=
  affineNormalLevelTrace (fun x : ℝ => x ^ 2)
    (-1 / 2) (1 / 2) t

/-- The protected family of quadratic traces stays in the unit strip. -/
lemma quadraticLevelTrace_stripDensity_eq_one
    (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (-1 / 2) (1 / 2)) :
    ∀ p ∈ quadraticLevelTrace t, StripDensity lam p = 1 := by
  rintro p ⟨x, hx, rfl⟩
  have hxleft : 0 ≤ x + 1 / 2 := by linarith [hx.1]
  have hxright : 0 ≤ 1 / 2 - x := by linarith [hx.2]
  have hxsq : x ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hxleft hxright]
  have hy : |x ^ 2 + t| ≤ 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg x, ht.1]
    · nlinarith [hxsq, ht.2]
  simp [StripDensity, hy]

/-- Three certified points witness that the specimen is a nonempty curved
parabolic trace rather than a zero or straight-line placeholder. -/
theorem quadraticLevelTrace_curved_witness :
    ((-1 / 2, 1 / 4) : PlanePoint) ∈ quadraticLevelTrace 0 ∧
    ((0, 0) : PlanePoint) ∈ quadraticLevelTrace 0 ∧
    ((1 / 2, 1 / 4) : PlanePoint) ∈ quadraticLevelTrace 0 := by
  constructor
  · refine ⟨(-1 / 2 : ℝ), by norm_num, ?_⟩
    norm_num
  constructor
  · refine ⟨(0 : ℝ), by norm_num, ?_⟩
    norm_num
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    norm_num

/-- The actual weighted `H¹` costs of the protected curved level traces have
an exact set average. -/
theorem setLAverage_weightedTraceCost_quadraticLevelTrace (lam : ℝ) :
    (⨍⁻ t in Icc (-1 / 2) (1 / 2),
      weightedTraceCost lam (quadraticLevelTrace t) ∂volume) =
      weightedTraceCost lam (quadraticLevelTrace 0) := by
  apply setLAverage_weightedTraceCost_affineNormalLevelTrace
    (w := 1) (g := fun x : ℝ => x ^ 2)
    (continuous_pow 2) measurableSet_Icc
  · norm_num
  · simp
  · norm_num
  · intro t ht
    exact quadraticLevelTrace_stripDensity_eq_one lam ht

/-- Every trace in the curved specimen obeys the sharp coefficient-one
graph-speed estimate. -/
theorem weightedTraceCost_quadraticLevelTrace_le
    (lam : ℝ) {t : ℝ} (ht : t ∈ Icc (-1 / 2) (1 / 2)) :
    weightedTraceCost lam (quadraticLevelTrace t) ≤
      ENNReal.ofReal
        (∫ x in (-1 / 2)..(1 / 2),
          Real.sqrt
            (1 + (deriv (fun y : ℝ => y ^ 2 + t) x) ^ 2)) := by
  simpa [quadraticLevelTrace] using
    weightedTraceCost_affineNormalLevelTrace_le_intervalIntegral
      (lam := lam) (w := 1) (g := fun x : ℝ => x ^ 2)
      (by norm_num) (contDiff_id.pow 2) (by norm_num)
      (quadraticLevelTrace_stripDensity_eq_one lam ht)

/-- End-to-end selection: in a small three-parameter ball, an actual curved
weighted `H¹` trace cost can be used as the averaged selection criterion while
retaining regularity and quantitative `C⁰`/`C¹` perturbation control. -/
theorem exists_small_regularBoundedPerturb_with_quadraticTraceCost
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, boundedPerturb f c p = 0 →
        fderiv ℝ (boundedPerturb f c) p ≠ 0) ∧
      (∀ p, |boundedPerturb f c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (boundedPerturb f c) p -
        fderiv ℝ f p‖ < 2 * ε) ∧
      weightedTraceCost lam (quadraticLevelTrace c.2) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          weightedTraceCost lam (quadraticLevelTrace q.2)
          ∂boundedParameterMeasure := by
  have hcostEq :
      ∀ c ∈ Metric.ball (0 : PlanePoint × ℝ) ε,
        weightedTraceCost lam (quadraticLevelTrace c.2) =
          weightedTraceCost lam (quadraticLevelTrace 0) := by
    intro c hc
    have hnorm : ‖c‖ < ε := by
      simpa [Metric.mem_ball] using hc
    have hsndNorm : ‖c.2‖ < ε :=
      (norm_snd_le c).trans_lt hnorm
    have hsndAbs : |c.2| < ε := by
      simpa [Real.norm_eq_abs] using hsndNorm
    have ht : c.2 ∈ Icc (-1 / 2) (1 / 2) := by
      rw [abs_lt] at hsndAbs
      exact ⟨by linarith [hsndAbs.1], by linarith [hsndAbs.2]⟩
    simpa [quadraticLevelTrace] using
      weightedTraceCost_affineNormalLevelTrace_eq
        (lam := lam) (w := 1) (g := fun x : ℝ => x ^ 2)
        (continuous_pow 2)
        (quadraticLevelTrace_stripDensity_eq_one lam ht)
        (quadraticLevelTrace_stripDensity_eq_one lam (by norm_num))
  have hL : AEMeasurable
      (fun c : PlanePoint × ℝ =>
        weightedTraceCost lam (quadraticLevelTrace c.2))
      (boundedParameterMeasure.restrict
        (Metric.ball (0 : PlanePoint × ℝ) ε)) := by
    let C := weightedTraceCost lam (quadraticLevelTrace 0)
    have hC : AEMeasurable (fun _ : PlanePoint × ℝ => C)
        (boundedParameterMeasure.restrict
          (Metric.ball (0 : PlanePoint × ℝ) ε)) :=
      measurable_const.aemeasurable
    apply hC.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with c hc
    exact (hcostEq c hc).symm
  exact exists_small_regularBoundedPerturb_with_C1_control hf hε hL

variable {α : Type*} [MeasurableSpace α]

/-- The part in `K` of the zero trace of a parameterized scalar phase. -/
def parameterZeroTrace (F : α → PlanePoint → ℝ) (K : Set PlanePoint)
    (c : α) : Set PlanePoint :=
  {p | p ∈ K ∧ F c p = 0}

omit [MeasurableSpace α] in
lemma euclidean_image_parameterZeroTrace
    (F : α → PlanePoint → ℝ) (K : Set PlanePoint) (c : α) :
    planeEuclideanHomeomorph '' parameterZeroTrace F K c =
      {z | planeEuclideanHomeomorph.symm z ∈ K ∧
        F c (planeEuclideanHomeomorph.symm z) = 0} := by
  ext z
  constructor
  · rintro ⟨p, ⟨hpK, hpzero⟩, rfl⟩
    simpa using ⟨hpK, hpzero⟩
  · rintro ⟨hzK, hzero⟩
    refine ⟨planeEuclideanHomeomorph.symm z, ⟨hzK, hzero⟩, ?_⟩
    simp

/-- Actual density-weighted Euclidean `H¹` cost of measurable parameterized
zero traces is measurable when all traces lie in one finite-`H¹` carrier. -/
theorem measurable_weightedTraceCost_parameterZeroTrace_of_finiteCarrier
    (lam : ℝ) (F : α → PlanePoint → ℝ) (K R : Set PlanePoint)
    (hF : Measurable (fun q : α × PlanePoint => F q.1 q.2))
    (hK : MeasurableSet K)
    (hsub : ∀ c, parameterZeroTrace F K c ⊆ R)
    (hRfinite : (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' R) ≠ (⊤ : ℝ≥0∞)) :
    Measurable (fun c => weightedTraceCost lam (parameterZeroTrace F K c)) := by
  let RE : Set EuclideanPlane := planeEuclideanHomeomorph '' R
  let ν : Measure EuclideanPlane := (μH[1] : Measure EuclideanPlane).restrict RE
  let _ : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by
    simpa only [ν, RE] using hRfinite)
  let T : Set (α × EuclideanPlane) :=
    {q | planeEuclideanHomeomorph.symm q.2 ∈ K ∧
      F q.1 (planeEuclideanHomeomorph.symm q.2) = 0}
  have hcoord : Measurable (fun q : α × EuclideanPlane =>
      (q.1, planeEuclideanHomeomorph.symm q.2)) :=
    measurable_fst.prodMk
      (planeEuclideanHomeomorph.symm.continuous.measurable.comp measurable_snd)
  have hT : MeasurableSet T := by
    apply (hK.preimage
      (planeEuclideanHomeomorph.symm.continuous.measurable.comp measurable_snd)).inter
    exact measurableSet_eq_fun (hF.comp hcoord) measurable_const
  have hdensity : Measurable (fun q : α × EuclideanPlane =>
      ENNReal.ofReal (euclideanStripDensity lam q.2)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_stripDensity lam).comp
        (planeEuclideanHomeomorph.symm.continuous.measurable.comp measurable_snd))
  have hjoint : Measurable (fun q : α × EuclideanPlane =>
      T.indicator (fun q => ENNReal.ofReal (euclideanStripDensity lam q.2)) q) :=
    hdensity.indicator hT
  have hjoint' : Measurable (Function.uncurry (fun c z =>
      T.indicator (fun q => ENNReal.ofReal (euclideanStripDensity lam q.2)) (c, z))) := by
    change Measurable (fun q : α × EuclideanPlane =>
      T.indicator (fun q => ENNReal.ofReal (euclideanStripDensity lam q.2)) q)
    exact hjoint
  have hsections := hjoint'.lintegral_prod_right (ν := ν)
  convert hsections using 1
  funext c
  unfold weightedTraceCost
  rw [euclidean_image_parameterZeroTrace]
  let S : Set EuclideanPlane :=
    {z | planeEuclideanHomeomorph.symm z ∈ K ∧
      F c (planeEuclideanHomeomorph.symm z) = 0}
  have hS : MeasurableSet S := by
    apply (hK.preimage planeEuclideanHomeomorph.symm.continuous.measurable).inter
    exact measurableSet_eq_fun
      ((hF.comp (measurable_const.prodMk
        planeEuclideanHomeomorph.symm.continuous.measurable))) measurable_const
  have hSsub : S ⊆ RE := by
    intro z hz
    have hp : planeEuclideanHomeomorph.symm z ∈ parameterZeroTrace F K c := hz
    have hpR := hsub c hp
    exact ⟨planeEuclideanHomeomorph.symm z, hpR, by simp⟩
  rw [show {z : EuclideanPlane |
      planeEuclideanHomeomorph.symm z ∈ K ∧
        F c (planeEuclideanHomeomorph.symm z) = 0} = S from rfl]
  rw [← lintegral_indicator hS]
  change (∫⁻ z, S.indicator
      (fun z => ENNReal.ofReal (euclideanStripDensity lam z)) z
      ∂(μH[1] : Measure EuclideanPlane)) =
    ∫⁻ z, T.indicator
      (fun q => ENNReal.ofReal (euclideanStripDensity lam q.2)) (c, z) ∂ν
  rw [lintegral_indicator hS]
  have hTS : (fun z => T.indicator
      (fun q => ENNReal.ofReal (euclideanStripDensity lam q.2)) (c, z)) =
      S.indicator (fun z => ENNReal.ofReal (euclideanStripDensity lam z)) := by
    funext z
    have hiff : (c, z) ∈ T ↔ z ∈ S := Iff.rfl
    by_cases hz : z ∈ S
    · have ht : (c, z) ∈ T := hiff.mpr hz
      simp [Set.indicator, hz, ht]
    · have ht : (c, z) ∉ T := fun h => hz (hiff.mp h)
      simp [Set.indicator, hz, ht]
  rw [hTS, lintegral_indicator hS]
  change (∫⁻ z in S, ENNReal.ofReal (euclideanStripDensity lam z)
      ∂(μH[1] : Measure EuclideanPlane)) =
    ∫⁻ z in S, ENNReal.ofReal (euclideanStripDensity lam z) ∂ν
  unfold ν
  rw [Measure.restrict_restrict hS]
  rw [inter_eq_left.mpr hSsub]
variable {α : Type*}

/-- One parameterized graph chart, represented as a compact level trace. -/
def parameterGraphTrace (g : α → ℝ → ℝ) (a b : ℝ) (c : α) : Set PlanePoint :=
  affineNormalLevelTrace (g c) a b 0

/-- A fixed finite graph atlas at parameter `c`. -/
def parameterGraphAtlasTrace {N : ℕ} (g : Fin N → α → ℝ → ℝ)
    (a b : Fin N → ℝ) (c : α) : Set PlanePoint :=
  ⋃ i, parameterGraphTrace (g i) (a i) (b i) c

/-- The coefficient-one sum of weighted graph-speed integrals for an atlas. -/
def parameterGraphAtlasSpeedBudget {N : ℕ} (w : ℝ)
    (D : Fin N → α → ℝ → ℝ) (a b : Fin N → ℝ) (c : α) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal
    (w * ∫ x in a i..b i, Real.sqrt (1 + (D i c x) ^ 2))

/-- Joint continuity of chart slopes makes the finite graph-speed budget
measurable in the perturbation parameter. -/
theorem measurable_parameterGraphAtlasSpeedBudget
    {N : ℕ} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (w : ℝ) (D : Fin N → α → ℝ → ℝ) (a b : Fin N → ℝ)
    (hD : ∀ i, Continuous (Function.uncurry (D i))) :
    Measurable (parameterGraphAtlasSpeedBudget w D a b) := by
  apply Finset.measurable_sum Finset.univ
  intro i _hi
  have hIntegrand : Continuous (Function.uncurry (fun c x =>
      Real.sqrt (1 + (D i c x) ^ 2))) := by
    change Continuous (fun q : α × ℝ =>
      Real.sqrt (1 + (D i q.1 q.2) ^ 2))
    exact Real.continuous_sqrt.comp
      (continuous_const.add ((hD i).pow 2))
  exact (ENNReal.continuous_ofReal.comp
    (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hIntegrand (a i) (b i)))).measurable

/-- Every actual density-weighted `H¹` atlas trace is bounded by the
coefficient-one speed budget of the same charts and same parameter. -/
theorem weightedTraceCost_parameterGraphAtlasTrace_le_speedBudget
    {N : ℕ} {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → α → ℝ → ℝ) (D : Fin N → α → ℝ → ℝ)
    (a b : Fin N → ℝ) (c : α)
    (hg : ∀ i, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i x, deriv (g i c) x = D i c x)
    (hdensity : ∀ i p, p ∈ parameterGraphTrace (g i) (a i) (b i) c →
      StripDensity lam p = w) :
    weightedTraceCost lam (parameterGraphAtlasTrace g a b c) ≤
      parameterGraphAtlasSpeedBudget w D a b c := by
  refine (weightedTraceCost_iUnion_fin_le lam
    (fun i => parameterGraphTrace (g i) (a i) (b i) c)).trans ?_
  apply Finset.sum_le_sum
  intro i _hi
  have hi := weightedTraceCost_affineNormalLevelTrace_le_intervalIntegral
    hw (hg i) (hab i) (hdensity i)
  simpa only [parameterGraphTrace, add_zero, hderiv] using hi

/-- Regular perturbation selection can minimize the measurable speed budget
while controlling the actual weighted trace of the selected atlas. -/
theorem exists_small_regularBoundedPerturb_with_C1_control_and_graphAtlasCost
    {N : ℕ} {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (D : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (a b : Fin N → ℝ)
    (hD : ∀ i, Continuous (Function.uncurry (D i)))
    (hg : ∀ i c, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i c x, deriv (g i c) x = D i c x)
    (hdensity : ∀ c, c ∈ Metric.ball (0 : PlanePoint × ℝ) ε → ∀ i p,
      p ∈ parameterGraphTrace (g i) (a i) (b i) c → StripDensity lam p = w) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, boundedPerturb f c p = 0 →
        fderiv ℝ (boundedPerturb f c) p ≠ 0) ∧
      (∀ p, |boundedPerturb f c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (boundedPerturb f c) p -
        fderiv ℝ f p‖ < 2 * ε) ∧
      weightedTraceCost lam (parameterGraphAtlasTrace g a b c) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          parameterGraphAtlasSpeedBudget w D a b q
          ∂boundedParameterMeasure := by
  have hL : AEMeasurable (parameterGraphAtlasSpeedBudget w D a b)
      (boundedParameterMeasure.restrict
        (Metric.ball (0 : PlanePoint × ℝ) ε)) :=
    (measurable_parameterGraphAtlasSpeedBudget w D a b hD).aemeasurable
  obtain ⟨c, hc, hreg, hC0, hC1, hcost⟩ :=
    exists_small_regularBoundedPerturb_with_C1_control hf hε hL
  refine ⟨c, hc, hreg, hC0, hC1, ?_⟩
  exact (weightedTraceCost_parameterGraphAtlasTrace_le_speedBudget hw
    g D a b c (fun i => hg i c) hab (fun i => hderiv i c)
    (fun i p hp => hdensity c (by simpa [Metric.mem_ball] using hc) i p hp)).trans hcost

/-- The complete zero trace of one localized bounded perturbation. -/
def localizedBoundedPerturbZeroTrace
    (f χ : PlanePoint → ℝ) (c : PlanePoint × ℝ) : Set PlanePoint :=
  {p | localizedBoundedPerturb f χ c p = 0}

/-- A finite graph atlas for the actual localized zero trace gives a
coefficient-one averaged selector for that same compactly supported phase
family.  The trace estimate is derived chart by chart rather than supplied as
a separate coarea hypothesis. -/
theorem exists_small_regularLocalizedBoundedPerturb_with_graphAtlasCost
    {N : ℕ} {f χ : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχsupport : HasCompactSupport χ)
    (hχrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {M : ℝ} (hχderiv : ∀ p, ‖fderiv ℝ χ p‖ ≤ M)
    (K : Set PlanePoint) (hχone : ∀ p ∈ K, χ =ᶠ[𝓝 p] fun _ => 1)
    {ε : ℝ} (hε : 0 < ε)
    (hfaway : ∀ p ∉ K, (Real.pi + 1) * ε ≤ |f p|)
    {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (D : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (a b : Fin N → ℝ)
    (hD : ∀ i, Continuous (Function.uncurry (D i)))
    (hg : ∀ i c, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i c x, deriv (g i c) x = D i c x)
    (hcover : ∀ c, c ∈ Metric.ball (0 : PlanePoint × ℝ) ε →
      localizedBoundedPerturbZeroTrace f χ c ⊆
        parameterGraphAtlasTrace g a b c)
    (hdensity : ∀ c, c ∈ Metric.ball (0 : PlanePoint × ℝ) ε → ∀ i p,
      p ∈ parameterGraphTrace (g i) (a i) (b i) c →
        StripDensity lam p = w) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, localizedBoundedPerturb f χ c p = 0 →
        fderiv ℝ (localizedBoundedPerturb f χ c) p ≠ 0) ∧
      (∀ p, |localizedBoundedPerturb f χ c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (localizedBoundedPerturb f χ c) p -
        fderiv ℝ f p‖ < (2 + (Real.pi + 1) * M) * ε) ∧
      HasCompactSupport
        (fun p => localizedBoundedPerturb f χ c p - f p) ∧
      weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ c) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          parameterGraphAtlasSpeedBudget w D a b q
          ∂boundedParameterMeasure := by
  have hL : AEMeasurable (parameterGraphAtlasSpeedBudget w D a b)
      (boundedParameterMeasure.restrict
        (Metric.ball (0 : PlanePoint × ℝ) ε)) :=
    (measurable_parameterGraphAtlasSpeedBudget w D a b hD).aemeasurable
  obtain ⟨c, hc, hreg, hC0, hC1, hsupport, hcost⟩ :=
    exists_small_regularLocalizedBoundedPerturb_with_C1_control
      hf hχ hχsupport hχrange hχderiv K hχone hε hfaway hL
  refine ⟨c, hc, hreg, hC0, hC1, hsupport, ?_⟩
  have hcball : c ∈ Metric.ball (0 : PlanePoint × ℝ) ε := by
    simpa [Metric.mem_ball] using hc
  calc
    weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ c) ≤
        weightedTraceCost lam (parameterGraphAtlasTrace g a b c) :=
      weightedTraceCost_mono lam (hcover c hcball)
    _ ≤ parameterGraphAtlasSpeedBudget w D a b c :=
      weightedTraceCost_parameterGraphAtlasTrace_le_speedBudget hw
        g D a b c (fun i => hg i c) hab (fun i => hderiv i c)
        (fun i p hp => hdensity c hcball i p hp)
    _ ≤ ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
        parameterGraphAtlasSpeedBudget w D a b q
        ∂boundedParameterMeasure := hcost


/-- A parameterized curved chart whose linear, vertical, and curvature
coefficients all vary with the selected three-dimensional parameter. -/
def quadraticParameterGraph (c : PlanePoint × ℝ) (x : ℝ) : ℝ :=
  (1 + c.1.1) * x ^ 2 + c.1.2 * x + c.2

def quadraticParameterSlope (c : PlanePoint × ℝ) (x : ℝ) : ℝ :=
  2 * (1 + c.1.1) * x + c.1.2

def quadraticParameterTrace (c : PlanePoint × ℝ) : Set PlanePoint :=
  parameterGraphTrace quadraticParameterGraph (-1 / 2) (1 / 2) c

def quadraticParameterSpeedBudget (c : PlanePoint × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (∫ x in (-1 / 2)..(1 / 2),
      Real.sqrt (1 + (quadraticParameterSlope c x) ^ 2))

lemma deriv_quadraticParameterGraph (c : PlanePoint × ℝ) (x : ℝ) :
    deriv (quadraticParameterGraph c) x = quadraticParameterSlope c x := by
  have h := (((hasDerivAt_id x).pow 2).const_mul (1 + c.1.1)).add
    ((hasDerivAt_id x).const_mul c.1.2) |>.add_const c.2
  apply HasDerivAt.deriv
  convert h using 1
  · funext y
    rw [quadraticParameterGraph]
    simp only [id_eq, Pi.pow_apply, Pi.add_apply]
  · rw [quadraticParameterSlope]
    simp only [id_eq]
    ring

lemma contDiff_quadraticParameterGraph (c : PlanePoint × ℝ) :
    ContDiff ℝ 1 (quadraticParameterGraph c) := by
  unfold quadraticParameterGraph
  fun_prop

lemma continuous_uncurry_quadraticParameterSlope :
    Continuous (Function.uncurry quadraticParameterSlope) := by
  unfold quadraticParameterSlope
  fun_prop

lemma quadraticParameterTrace_stripDensity_eq_one
    (lam : ℝ) {ε : ℝ} (hε : ε ≤ 1 / 4)
    {c : PlanePoint × ℝ} (hc : c ∈ Metric.ball 0 ε) :
    ∀ p ∈ quadraticParameterTrace c, StripDensity lam p = 1 := by
  have hcnorm : ‖c‖ < ε := by
    simpa [Metric.mem_ball] using hc
  have hc1norm : ‖c.1‖ < ε := (norm_fst_le c).trans_lt hcnorm
  have hc11 : |c.1.1| < ε := by
    simpa [Real.norm_eq_abs] using (norm_fst_le c.1).trans_lt hc1norm
  have hc12 : |c.1.2| < ε := by
    simpa [Real.norm_eq_abs] using (norm_snd_le c.1).trans_lt hc1norm
  have hc2 : |c.2| < ε := by
    simpa [Real.norm_eq_abs] using (norm_snd_le c).trans_lt hcnorm
  rintro p ⟨x, hx, rfl⟩
  have hxleft : 0 ≤ x + 1 / 2 := by linarith [hx.1]
  have hxright : 0 ≤ 1 / 2 - x := by linarith [hx.2]
  have hxsq : x ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hxleft hxright]
  have hcx2 : |c.1.1 * x ^ 2| ≤ 1 / 16 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    calc
      |c.1.1| * x ^ 2 ≤ (1 / 4) * (1 / 4) := by
        exact mul_le_mul (hc11.trans_le hε).le hxsq (sq_nonneg x)
          (by norm_num)
      _ = 1 / 16 := by norm_num
  have hcx : |c.1.2 * x| ≤ 1 / 8 := by
    rw [abs_mul]
    have hxabs : |x| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    calc
      |c.1.2| * |x| ≤ (1 / 4) * (1 / 2) := by
        exact mul_le_mul (hc12.trans_le hε).le hxabs (abs_nonneg x)
          (by norm_num)
      _ = 1 / 8 := by norm_num
  have hytriangle :
      |x ^ 2 + c.1.1 * x ^ 2 + c.1.2 * x + c.2| ≤
        |x ^ 2| + |c.1.1 * x ^ 2| + |c.1.2 * x| + |c.2| := by
    exact (abs_add_le _ _).trans
      (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
        le_rfl)
  have hy : |quadraticParameterGraph c x| ≤ 1 := by
    rw [quadraticParameterGraph]
    have hrearrange :
        (1 + c.1.1) * x ^ 2 + c.1.2 * x + c.2 =
          x ^ 2 + c.1.1 * x ^ 2 + c.1.2 * x + c.2 := by ring
    rw [hrearrange]
    calc
      _ ≤ |x ^ 2| + |c.1.1 * x ^ 2| + |c.1.2 * x| + |c.2| := hytriangle
      _ ≤ 1 / 4 + 1 / 16 + 1 / 8 + 1 / 4 := by
        rw [abs_of_nonneg (sq_nonneg x)]
        exact add_le_add (add_le_add (add_le_add hxsq hcx2) hcx)
          (hc2.trans_le hε).le
      _ ≤ 1 := by norm_num
  simp [StripDensity, hy]

/-- The regular low-cost selector applies to an actually parameter-varying
curved graph, not only to vertical translates of one fixed trace. -/
theorem exists_small_regularBoundedPerturb_with_quadraticParameterTraceCost
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hεquarter : ε ≤ 1 / 4) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, boundedPerturb f c p = 0 →
        fderiv ℝ (boundedPerturb f c) p ≠ 0) ∧
      (∀ p, |boundedPerturb f c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (boundedPerturb f c) p -
        fderiv ℝ f p‖ < 2 * ε) ∧
      weightedTraceCost lam (quadraticParameterTrace c) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          quadraticParameterSpeedBudget q ∂boundedParameterMeasure := by
  obtain ⟨c, hc, hreg, hC0, hC1, hcost⟩ :=
    exists_small_regularBoundedPerturb_with_C1_control_and_graphAtlasCost
      (N := 1) hf hε (lam := lam) (w := 1) (by norm_num)
      (fun _ : Fin 1 => quadraticParameterGraph)
      (fun _ : Fin 1 => quadraticParameterSlope)
      (fun _ : Fin 1 => (-1 / 2 : ℝ))
      (fun _ : Fin 1 => (1 / 2 : ℝ))
      (fun _ => continuous_uncurry_quadraticParameterSlope)
      (fun _ => contDiff_quadraticParameterGraph)
      (fun _ => by norm_num)
      (fun _ => deriv_quadraticParameterGraph)
      (fun c hc _ => quadraticParameterTrace_stripDensity_eq_one lam
        hεquarter hc)
  refine ⟨c, hc, hreg, hC0, hC1, ?_⟩
  have htrace :
      parameterGraphAtlasTrace
          (fun _ : Fin 1 => quadraticParameterGraph)
          (fun _ : Fin 1 => (-1 / 2 : ℝ))
          (fun _ : Fin 1 => (1 / 2 : ℝ)) c =
        quadraticParameterTrace c := by
    ext p
    simp only [parameterGraphAtlasTrace, quadraticParameterTrace,
      Set.mem_iUnion]
    constructor
    · rintro ⟨_i, hi⟩
      exact hi
    · intro hp
      exact ⟨0, hp⟩
  rw [htrace] at hcost
  simpa [quadraticParameterSpeedBudget,
    parameterGraphAtlasSpeedBudget] using hcost

/-- Point `i` of the uniform `N`-cell partition of `[a,b]`. -/
def uniformPartitionPoint (a b : ℝ) (N i : ℕ) : ℝ :=
  a + (i : ℝ) * ((b - a) / (N : ℝ))

/-- Uniform polygonal chord sums are bounded by the `H¹` mass of an
injectively parametrized continuous interval image. -/
theorem uniformPartitionChordSum_le_hausdorffMeasure_image_Icc
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → E} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    {N : ℕ} (hN : 0 < N) (hinj : Set.InjOn f (Icc a b)) :
    (∑ i : Fin N, ENNReal.ofReal
      (dist (f (uniformPartitionPoint a b N i.1))
        (f (uniformPartitionPoint a b N (i.1 + 1))))) ≤
      (μH[1] : Measure E) (f '' Icc a b) := by
  let d : ℝ := (b - a) / (N : ℝ)
  let p : ℕ → ℝ := uniformPartitionPoint a b N
  let A : ℕ → Set ℝ := fun i => Ico (p i) (p (i + 1))
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hp0 : p 0 = a := by simp [p, uniformPartitionPoint]
  have hpN : p N = b := by
    dsimp [p, uniformPartitionPoint]
    field_simp [hNreal.ne']
    ring
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p, uniformPartitionPoint]
    gcongr
  have hp_mem (i : ℕ) (hi : i ≤ N) : p i ∈ Icc a b := by
    constructor
    · rw [← hp0]
      exact hpmono (Nat.zero_le i)
    · rw [← hpN]
      exact hpmono hi
  have hpiece_sub (i : ℕ) (hi : i < N) : Icc (p i) (p (i + 1)) ⊆ Icc a b := by
    intro x hx
    exact ⟨(hp_mem i hi.le).1.trans hx.1,
      hx.2.trans (hp_mem (i + 1) (Nat.succ_le_iff.mpr hi)).2⟩
  have hpair : Set.Pairwise (↑(Finset.range N))
      (Function.onFun Disjoint fun i => f '' A i) := by
    intro i hi j hj hij
    change Disjoint (f '' A i) (f '' A j)
    have hsrc : Disjoint (A i) (A j) :=
      hpmono.pairwise_disjoint_on_Ico_succ hij
    rw [Set.disjoint_left]
    rintro y ⟨x, hxi, rfl⟩ ⟨z, hzj, hzx⟩
    have hiN : i < N := Finset.mem_range.mp hi
    have hjN : j < N := Finset.mem_range.mp hj
    have hxS : x ∈ Icc a b := hpiece_sub i hiN ⟨hxi.1, hxi.2.le⟩
    have hzS : z ∈ Icc a b := hpiece_sub j hjN ⟨hzj.1, hzj.2.le⟩
    have hxz : x = z := hinj hxS hzS hzx.symm
    exact (Set.disjoint_left.mp hsrc) hxi (hxz ▸ hzj)
  have hmeas (i : ℕ) (hi : i ∈ Finset.range N) : MeasurableSet (f '' A i) := by
    have hiN : i < N := Finset.mem_range.mp hi
    rw [show f '' A i = f '' Icc (p i) (p (i + 1)) \ {f (p (i + 1))} by
      exact image_Ico_eq_image_Icc_diff_endpoint hinj (hpmono (Nat.le_succ i))
        (hpiece_sub i hiN)]
    exact (isCompact_Icc.image hf).measurableSet.diff (measurableSet_singleton _)
  have hunion_sub : (⋃ i ∈ Finset.range N, f '' A i) ⊆ f '' Icc a b := by
    intro y hy
    rcases mem_iUnion.mp hy with ⟨i, hy⟩
    rcases mem_iUnion.mp hy with ⟨hi, hy⟩
    rcases hy with ⟨x, hxA, rfl⟩
    exact ⟨x, hpiece_sub i (Finset.mem_range.mp hi) ⟨hxA.1, hxA.2.le⟩, rfl⟩
  change (∑ i : Fin N,
      ENNReal.ofReal (dist (f (p i.1)) (f (p (i.1 + 1))))) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ENNReal.ofReal (dist (f (p i)) (f (p (i + 1))))) N]
  calc
    (∑ i ∈ Finset.range N,
        ENNReal.ofReal (dist (f (p i)) (f (p (i + 1))))) ≤
        ∑ i ∈ Finset.range N, (μH[1] : Measure E) (f '' A i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [hausdorffMeasure_image_Ico_eq_Icc hinj (hpmono (Nat.le_succ i))
        (hpiece_sub i hiN)]
      exact ofReal_dist_le_hausdorffMeasure_image_Icc hf
        (hpmono (Nat.le_succ i))
    _ = (μH[1] : Measure E) (⋃ i ∈ Finset.range N, f '' A i) :=
      (measure_biUnion_finset hpair hmeas).symm
    _ ≤ (μH[1] : Measure E) (f '' Icc a b) := measure_mono hunion_sub


/-- On every nondegenerate graph subinterval, the endpoint chord has the
graph speed at one intermediate point times the interval width. -/
lemma exists_dist_euclideanGraph_eq_mul_speed
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {u v : ℝ} (huv : u < v) :
    ∃ z ∈ Ioo u v,
      dist (planeEuclideanHomeomorph (u, g u))
          (planeEuclideanHomeomorph (v, g v)) =
        (v - u) * Real.sqrt (1 + (deriv g z) ^ 2) := by
  obtain ⟨z, hz, hzderiv⟩ := exists_deriv_eq_slope g huv
    hg.continuous.continuousOn
    (fun x _hx => (hg.differentiable (by norm_num) x).differentiableWithinAt)
  refine ⟨z, hz, ?_⟩
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (dist u v ^ 2 + dist (g u) (g v) ^ 2) =
    (v - u) * Real.sqrt (1 + deriv g z ^ 2)
  rw [Real.dist_eq, Real.dist_eq]
  have hwidth : 0 < v - u := sub_pos.mpr huv
  have hgdiff : g v - g u = deriv g z * (v - u) := by
    rw [hzderiv]
    field_simp [hwidth.ne']
  rw [show u - v = -(v - u) by ring,
    show g u - g v = -(g v - g u) by ring, hgdiff]
  rw [abs_neg, abs_of_pos hwidth]
  rw [sq_abs, neg_sq]
  have hradicand : 0 ≤ 1 + deriv g z ^ 2 := by positivity
  calc
    Real.sqrt ((v - u) ^ 2 + (deriv g z * (v - u)) ^ 2) =
        Real.sqrt ((v - u) ^ 2 * (1 + deriv g z ^ 2)) := by
      congr 1
      ring
    _ = Real.sqrt ((v - u) ^ 2) *
        Real.sqrt (1 + deriv g z ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg (v - u))]
    _ = (v - u) * Real.sqrt (1 + deriv g z ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hwidth]

/-- The graph-speed integral is also a lower bound for Euclidean `H¹` of a
`C¹` graph.  Combined with the existing upper bound, this identifies the
actual trace mass without an area-formula axiom. -/
theorem intervalIntegral_le_hausdorffMeasure_euclideanGraph_Icc
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal
        (∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2)) ≤
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let F : ℝ → ℝ := fun x => Real.sqrt (1 + (deriv g x) ^ 2)
  have hderiv : Continuous (deriv g) :=
    hg.continuous_deriv (by norm_num)
  have hF : Continuous F :=
    (continuous_const.add (hderiv.pow 2)).sqrt
  have hFone (x : ℝ) : 1 ≤ F x := by
    dsimp [F]
    rw [Real.one_le_sqrt]
    nlinarith [sq_nonneg (deriv g x)]
  have hInt : 0 ≤ ∫ x in a..b, F x :=
    intervalIntegral.integral_nonneg hab.le
      (fun x _ => Real.sqrt_nonneg _)
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _hmeasureTop
  have hηreal : 0 < (η : ℝ) := by exact_mod_cast hη
  let ε : ℝ := min ((η : ℝ) / (4 * (b - a))) (1 / 2)
  have hε : 0 < ε := lt_min
    (div_pos hηreal (mul_pos (by norm_num) (sub_pos.mpr hab)))
    (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hεbudget : ε ≤ (η : ℝ) / (4 * (b - a)) := min_le_left _ _
  have huc : UniformContinuousOn F (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hcloseF⟩ := huc ε hε
  obtain ⟨N, hN, hdδ, hmid⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral hF hab
      (div_pos hηreal (by norm_num : (0 : ℝ) < 4)) hδ
  let d : ℝ := (b - a) / (N : ℝ)
  let p : ℕ → ℝ := uniformPartitionPoint a b N
  let m : Fin N → ℝ := fun i => a + ((i : ℝ) + 1 / 2) * d
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hpstep (i : ℕ) : p (i + 1) - p i = d := by
    dsimp [p, uniformPartitionPoint, d]
    push_cast
    ring
  have hp0 : p 0 = a := by simp [p, uniformPartitionPoint]
  have hpN : p N = b := by
    dsimp [p, uniformPartitionPoint]
    field_simp [hNreal.ne']
    ring
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p, uniformPartitionPoint]
    gcongr
  have hcell_mem (i : Fin N) :
      Icc (p i.1) (p (i.1 + 1)) ⊆ Icc a b := by
    intro x hx
    constructor
    · rw [← hp0]
      exact (hpmono (Nat.zero_le i.1)).trans hx.1
    · rw [← hpN]
      exact hx.2.trans (hpmono (Nat.succ_le_iff.mpr i.2))
  have hm_between (i : Fin N) :
      m i ∈ Icc (p i.1) (p (i.1 + 1)) := by
    have hm_eq : m i = (p i.1 + p (i.1 + 1)) / 2 := by
      dsimp [m, p, uniformPartitionPoint, d]
      push_cast
      ring
    rw [hm_eq]
    constructor <;> linarith [hpmono (Nat.le_succ i.1)]
  have hchord (i : Fin N) :
      ENNReal.ofReal ((F (m i) - ε) * d) ≤
        ENNReal.ofReal
          (dist
            (planeEuclideanHomeomorph (p i.1, g (p i.1)))
            (planeEuclideanHomeomorph (p (i.1 + 1), g (p (i.1 + 1))))) := by
    have hp_lt : p i.1 < p (i.1 + 1) := by
      rw [← sub_pos, hpstep]
      exact hd
    obtain ⟨z, hz, hzdist⟩ :=
      exists_dist_euclideanGraph_eq_mul_speed hg hp_lt
    have hzcell : z ∈ Icc (p i.1) (p (i.1 + 1)) := ⟨hz.1.le, hz.2.le⟩
    have hzm : |z - m i| ≤ d := by
      rw [abs_le]
      have hm := hm_between i
      constructor <;> linarith [hz.1, hz.2, hm.1, hm.2, hpstep i.1]
    have hdist : dist z (m i) < δ := by
      rw [Real.dist_eq]
      exact hzm.trans_lt hdδ
    have hzglobal := hcell_mem i hzcell
    have hmglobal := hcell_mem i (hm_between i)
    have hclose := hcloseF z hzglobal (m i) hmglobal hdist
    rw [Real.dist_eq] at hclose
    apply ENNReal.ofReal_le_ofReal
    rw [hzdist, hpstep i.1,
      show Real.sqrt (1 + deriv g z ^ 2) = F z from rfl]
    have hspeed : F (m i) - ε ≤ F z := by
      linarith [neg_abs_le (F z - F (m i))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hspeed hd.le
  have hterm_nonneg (i : Fin N) : 0 ≤ (F (m i) - ε) * d :=
    mul_nonneg (by linarith [hFone (m i), hεhalf]) hd.le
  have hsumENN :
      ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) =
        ∑ i : Fin N, ENNReal.ofReal ((F (m i) - ε) * d) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm_nonneg i)
  have hcurveContinuous : Continuous
      (fun x : ℝ => planeEuclideanHomeomorph (x, g x)) :=
    planeEuclideanHomeomorph.continuous.comp
      (continuous_id.prodMk hg.continuous)
  have hcurveInj : Set.InjOn
      (fun x : ℝ => planeEuclideanHomeomorph (x, g x)) (Icc a b) := by
    intro x _hx y _hy hxy
    exact congrArg Prod.fst (planeEuclideanHomeomorph.injective hxy)
  have hpolygon :=
    uniformPartitionChordSum_le_hausdorffMeasure_image_Icc
      hcurveContinuous hab hN hcurveInj
  have hlowerMeasure :
      ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) ≤
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            ((fun x : ℝ => (x, g x)) '' Icc a b)) := by
    rw [hsumENN]
    refine (Finset.sum_le_sum fun i _ => hchord i).trans ?_
    simpa only [Set.image_image, Function.comp_apply, p,
      uniformPartitionPoint] using hpolygon
  have hNd : (N : ℝ) * d = b - a := by
    dsimp [d]
    field_simp [hNreal.ne']
  have herror : (N : ℝ) * (ε * d) ≤ (η : ℝ) / 4 := by
    calc
      (N : ℝ) * (ε * d) = ε * ((N : ℝ) * d) := by ring
      _ = ε * (b - a) := by rw [hNd]
      _ ≤ ((η : ℝ) / (4 * (b - a))) * (b - a) :=
        mul_le_mul_of_nonneg_right hεbudget (sub_pos.mpr hab).le
      _ = (η : ℝ) / 4 := by
        field_simp [(sub_pos.mpr hab).ne']
  have hsumExpand :
      (∑ i : Fin N, (F (m i) - ε) * d) =
        (∑ i : Fin N, F (m i) * d) - (N : ℝ) * (ε * d) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hreal :
      (∫ x in a..b, F x) ≤
        (∑ i : Fin N, (F (m i) - ε) * d) + (η : ℝ) / 2 := by
    rw [hsumExpand]
    change (∫ x in a..b, F x) ≤
      (∑ i : Fin N, F (m i) * d) + (η : ℝ) / 4 at hmid
    linarith
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, (F (m i) - ε) * d :=
    Finset.sum_nonneg fun i _ => hterm_nonneg i
  change ENNReal.ofReal (∫ x in a..b, F x) ≤ _
  calc
    ENNReal.ofReal (∫ x in a..b, F x) ≤
        ENNReal.ofReal
          ((∑ i : Fin N, (F (m i) - ε) * d) + (η : ℝ) / 2) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) +
        ENNReal.ofReal ((η : ℝ) / 2) := by
      rw [ENNReal.ofReal_add hsum_nonneg (div_nonneg hηreal.le (by norm_num))]
    _ ≤ (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            ((fun x : ℝ => (x, g x)) '' Icc a b)) + η := by
      apply add_le_add hlowerMeasure
      calc
        ENNReal.ofReal ((η : ℝ) / 2) ≤ ENNReal.ofReal (η : ℝ) := by
          apply ENNReal.ofReal_le_ofReal
          linarith
        _ = η := ENNReal.ofReal_coe_nnreal

/-- Exact Euclidean `H¹` graph length formula for every compact `C¹` graph. -/
theorem hausdorffMeasure_euclideanGraph_Icc_eq_intervalIntegral
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b)) =
      ENNReal.ofReal
        (∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2)) :=
  le_antisymm
    (hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral hg hab)
    (intervalIntegral_le_hausdorffMeasure_euclideanGraph_Icc hg hab)

variable {α : Type*}

/-- A single parameterized graph chart has exactly its coefficient-one speed
budget when the density is constant on the trace. -/
theorem weightedTraceCost_parameterGraphTrace_eq_speedBudget
    {lam w : ℝ} (hw : 0 ≤ w) (g : α → ℝ → ℝ) (D : α → ℝ → ℝ)
    {a b : ℝ} (c : α) (hg : ContDiff ℝ 1 (g c)) (hab : a ≤ b)
    (hderiv : ∀ x, deriv (g c) x = D c x)
    (hdensity : ∀ p ∈ parameterGraphTrace g a b c,
      StripDensity lam p = w) :
    weightedTraceCost lam (parameterGraphTrace g a b c) =
      ENNReal.ofReal
        (w * ∫ x in a..b, Real.sqrt (1 + (D c x) ^ 2)) := by
  unfold parameterGraphTrace at hdensity ⊢
  rw [weightedTraceCost_eq_const_mul_hausdorff lam w
    (isCompact_affineNormalLevelTrace hg.continuous a b 0) hdensity]
  unfold affineNormalLevelTrace
  simp only [add_zero]
  rw [hausdorffMeasure_euclideanGraph_Icc_eq_intervalIntegral hg hab]
  simp_rw [hderiv]
  exact (ENNReal.ofReal_mul hw).symm

/-- Pairwise disjoint graph charts have exactly additive actual weighted trace
cost; no chart-overlap multiplicity is paid. -/
theorem weightedTraceCost_parameterGraphAtlasTrace_eq_sum
    {N : ℕ} (lam : ℝ) (g : Fin N → α → ℝ → ℝ)
    (a b : Fin N → ℝ) (c : α)
    (hg : ∀ i, Continuous (g i c))
    (hdisjoint : Set.Pairwise Set.univ
      (Function.onFun Disjoint
        (fun i => parameterGraphTrace (g i) (a i) (b i) c))) :
    weightedTraceCost lam (parameterGraphAtlasTrace g a b c) =
      ∑ i, weightedTraceCost lam
        (parameterGraphTrace (g i) (a i) (b i) c) := by
  have hmeas (i : Fin N) : MeasurableSet
      (planeEuclideanHomeomorph ''
        parameterGraphTrace (g i) (a i) (b i) c) :=
    (isCompact_affineNormalLevelTrace (hg i) (a i) (b i) 0).image
      planeEuclideanHomeomorph.continuous |>.measurableSet
  have hpair : Pairwise (Disjoint on fun i : Fin N =>
      planeEuclideanHomeomorph ''
        parameterGraphTrace (g i) (a i) (b i) c) := by
    intro i j hij
    change Disjoint
      (planeEuclideanHomeomorph ''
        parameterGraphTrace (g i) (a i) (b i) c)
      (planeEuclideanHomeomorph ''
        parameterGraphTrace (g j) (a j) (b j) c)
    rw [Set.disjoint_left]
    rintro z ⟨pi, hpi, rfl⟩ ⟨pj, hpj, heq⟩
    have hpij : pi = pj := planeEuclideanHomeomorph.injective heq.symm
    exact (Set.disjoint_left.mp
      (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hpi (hpij ▸ hpj)
  unfold weightedTraceCost parameterGraphAtlasTrace
  rw [image_iUnion]
  rw [lintegral_iUnion hmeas hpair]
  simp

/-- A pairwise-disjoint finite graph atlas has exact actual cost equal to the
sum of its coefficient-one chart-speed budgets. -/
theorem weightedTraceCost_parameterGraphAtlasTrace_eq_speedBudget
    {N : ℕ} {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → α → ℝ → ℝ) (D : Fin N → α → ℝ → ℝ)
    (a b : Fin N → ℝ) (c : α)
    (hg : ∀ i, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i x, deriv (g i c) x = D i c x)
    (hdisjoint : Set.Pairwise Set.univ
      (Function.onFun Disjoint
        (fun i => parameterGraphTrace (g i) (a i) (b i) c)))
    (hdensity : ∀ i p, p ∈ parameterGraphTrace (g i) (a i) (b i) c →
      StripDensity lam p = w) :
    weightedTraceCost lam (parameterGraphAtlasTrace g a b c) =
      parameterGraphAtlasSpeedBudget w D a b c := by
  rw [weightedTraceCost_parameterGraphAtlasTrace_eq_sum lam g a b c
    (fun i => (hg i).continuous) hdisjoint]
  unfold parameterGraphAtlasSpeedBudget
  apply Finset.sum_congr rfl
  intro i _hi
  exact weightedTraceCost_parameterGraphTrace_eq_speedBudget hw
    (g i) (D i) c (hg i) (hab i) (hderiv i) (hdensity i)

/-- Jointly continuous slopes make the actual weighted `H¹` cost of a
pairwise-disjoint finite graph atlas measurable. -/
theorem measurable_weightedTraceCost_parameterGraphAtlasTrace
    {N : ℕ} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → α → ℝ → ℝ) (D : Fin N → α → ℝ → ℝ)
    (a b : Fin N → ℝ)
    (hD : ∀ i, Continuous (Function.uncurry (D i)))
    (hg : ∀ i c, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i c x, deriv (g i c) x = D i c x)
    (hdisjoint : ∀ c, Set.Pairwise Set.univ
      (Function.onFun Disjoint
        (fun i => parameterGraphTrace (g i) (a i) (b i) c)))
    (hdensity : ∀ c i p,
      p ∈ parameterGraphTrace (g i) (a i) (b i) c →
        StripDensity lam p = w) :
    Measurable (fun c =>
      weightedTraceCost lam (parameterGraphAtlasTrace g a b c)) := by
  rw [show (fun c =>
      weightedTraceCost lam (parameterGraphAtlasTrace g a b c)) =
      parameterGraphAtlasSpeedBudget w D a b by
    funext c
    exact weightedTraceCost_parameterGraphAtlasTrace_eq_speedBudget hw
      g D a b c (fun i => hg i c) hab (fun i => hderiv i c)
      (hdisjoint c) (fun i p hp => hdensity c i p hp)]
  exact measurable_parameterGraphAtlasSpeedBudget w D a b hD

/-- Once a localized smooth phase is represented by a pairwise-disjoint finite
implicit graph atlas, its actual trace cost—not merely a majorant—is a valid
below-average selection criterion for the same compactly supported family. -/
theorem exists_small_regularLocalizedBoundedPerturb_with_actualGraphAtlasAverage
    {N : ℕ} {f χ : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχsupport : HasCompactSupport χ)
    (hχrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {M : ℝ} (hχderiv : ∀ p, ‖fderiv ℝ χ p‖ ≤ M)
    (K : Set PlanePoint) (hχone : ∀ p ∈ K, χ =ᶠ[𝓝 p] fun _ => 1)
    {ε : ℝ} (hε : 0 < ε)
    (hfaway : ∀ p ∉ K, (Real.pi + 1) * ε ≤ |f p|)
    {lam w : ℝ} (hw : 0 ≤ w)
    (g : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (D : Fin N → (PlanePoint × ℝ) → ℝ → ℝ)
    (a b : Fin N → ℝ)
    (hD : ∀ i, Continuous (Function.uncurry (D i)))
    (hg : ∀ i c, ContDiff ℝ 1 (g i c))
    (hab : ∀ i, a i ≤ b i)
    (hderiv : ∀ i c x, deriv (g i c) x = D i c x)
    (htrace : ∀ c, localizedBoundedPerturbZeroTrace f χ c =
      parameterGraphAtlasTrace g a b c)
    (hdisjoint : ∀ c, Set.Pairwise Set.univ
      (Function.onFun Disjoint
        (fun i => parameterGraphTrace (g i) (a i) (b i) c)))
    (hdensity : ∀ c i p,
      p ∈ parameterGraphTrace (g i) (a i) (b i) c →
        StripDensity lam p = w) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, localizedBoundedPerturb f χ c p = 0 →
        fderiv ℝ (localizedBoundedPerturb f χ c) p ≠ 0) ∧
      (∀ p, |localizedBoundedPerturb f χ c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (localizedBoundedPerturb f χ c) p -
        fderiv ℝ f p‖ < (2 + (Real.pi + 1) * M) * ε) ∧
      HasCompactSupport
        (fun p => localizedBoundedPerturb f χ c p - f p) ∧
      weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ c) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ q)
          ∂boundedParameterMeasure := by
  have hcostMeas : Measurable (fun c : PlanePoint × ℝ =>
      weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ c)) := by
    rw [show (fun c : PlanePoint × ℝ =>
        weightedTraceCost lam (localizedBoundedPerturbZeroTrace f χ c)) =
        (fun c => weightedTraceCost lam
          (parameterGraphAtlasTrace g a b c)) by
      funext c
      rw [htrace c]]
    exact measurable_weightedTraceCost_parameterGraphAtlasTrace hw
      g D a b hD hg hab hderiv hdisjoint hdensity
  exact exists_small_regularLocalizedBoundedPerturb_with_C1_control
    hf hχ hχsupport hχrange hχderiv K hχone hε hfaway
      hcostMeas.aemeasurable

/-- The actual weighted trace cost of the curved specimen equals its speed
budget throughout the small parameter ball. -/
theorem weightedTraceCost_quadraticParameterTrace_eq_speedBudget
    (lam : ℝ) {ε : ℝ} (hεquarter : ε ≤ 1 / 4)
    {c : PlanePoint × ℝ} (hc : c ∈ Metric.ball 0 ε) :
    weightedTraceCost lam (quadraticParameterTrace c) =
      quadraticParameterSpeedBudget c := by
  simpa [quadraticParameterTrace, quadraticParameterSpeedBudget] using
    weightedTraceCost_parameterGraphTrace_eq_speedBudget
      (α := PlanePoint × ℝ) (lam := lam) (w := 1) (by norm_num)
      quadraticParameterGraph quadraticParameterSlope c
      (contDiff_quadraticParameterGraph c) (by norm_num)
      (deriv_quadraticParameterGraph c)
      (quadraticParameterTrace_stripDensity_eq_one lam hεquarter hc)

/-- The curved specimen's speed budget is measurable in all three parameters. -/
theorem measurable_quadraticParameterSpeedBudget :
    Measurable quadraticParameterSpeedBudget := by
  rw [show quadraticParameterSpeedBudget =
      parameterGraphAtlasSpeedBudget 1
        (fun _ : Fin 1 => quadraticParameterSlope)
        (fun _ : Fin 1 => (-1 / 2 : ℝ))
        (fun _ : Fin 1 => (1 / 2 : ℝ)) by
    funext c
    simp [quadraticParameterSpeedBudget, parameterGraphAtlasSpeedBudget]]
  exact measurable_parameterGraphAtlasSpeedBudget
    (α := PlanePoint × ℝ) (N := 1) (w := 1)
    (fun _ : Fin 1 => quadraticParameterSlope)
    (fun _ : Fin 1 => (-1 / 2 : ℝ))
    (fun _ : Fin 1 => (1 / 2 : ℝ))
    (fun _ => continuous_uncurry_quadraticParameterSlope)

/-- On a small parameter ball, the curved specimen's actual weighted trace
cost is measurable. -/
theorem aemeasurable_weightedTraceCost_quadraticParameterTrace
    (lam : ℝ) {ε : ℝ} (hεquarter : ε ≤ 1 / 4) :
    AEMeasurable (fun c : PlanePoint × ℝ =>
      weightedTraceCost lam (quadraticParameterTrace c))
      (boundedParameterMeasure.restrict
        (Metric.ball (0 : PlanePoint × ℝ) ε)) := by
  refine measurable_quadraticParameterSpeedBudget.aemeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with c hc
  exact (weightedTraceCost_quadraticParameterTrace_eq_speedBudget
    lam hεquarter hc).symm

/-- The genuinely parameter-varying curved specimen admits regular selection
below the average of its own actual weighted trace cost. -/
theorem exists_small_regularBoundedPerturb_with_quadraticParameterTraceAverage
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hεquarter : ε ≤ 1 / 4) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, boundedPerturb f c p = 0 →
        fderiv ℝ (boundedPerturb f c) p ≠ 0) ∧
      (∀ p, |boundedPerturb f c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (boundedPerturb f c) p -
        fderiv ℝ f p‖ < 2 * ε) ∧
      weightedTraceCost lam (quadraticParameterTrace c) ≤
        ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε,
          weightedTraceCost lam (quadraticParameterTrace q)
          ∂boundedParameterMeasure := by
  exact exists_small_regularBoundedPerturb_with_C1_control hf hε
    (aemeasurable_weightedTraceCost_quadraticParameterTrace lam hεquarter)

def euclideanGraphParam (g : ℝ → ℝ) (x : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (x, g x)

noncomputable def euclideanGraphPullbackMeasure (g : ℝ → ℝ) : Measure ℝ :=
  Measure.map (fun z : EuclideanPlane => (planeEuclideanHomeomorph.symm z).1)
    ((μH[1] : Measure EuclideanPlane).restrict (Set.range (euclideanGraphParam g)))

lemma euclideanGraphParam_injective (g : ℝ → ℝ) :
    Function.Injective (euclideanGraphParam g) := by
  intro x y hxy
  have h := congrArg (fun z : EuclideanPlane =>
    (planeEuclideanHomeomorph.symm z).1) hxy
  simpa [euclideanGraphParam] using h

lemma graph_projection_preimage_inter_range
    (g : ℝ → ℝ) (s : Set ℝ) :
    (fun z : EuclideanPlane => (planeEuclideanHomeomorph.symm z).1) ⁻¹' s ∩
        Set.range (euclideanGraphParam g) =
      euclideanGraphParam g '' s := by
  ext z
  constructor
  · rintro ⟨hzs, x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simpa [euclideanGraphParam] using hzs
  · rintro ⟨x, hxs, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    simpa [euclideanGraphParam] using hxs

lemma euclideanGraphPullbackMeasure_Ico
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) :
    euclideanGraphPullbackMeasure g (Ico a b) =
      ENNReal.ofReal (∫ x in a..b,
        Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hproj : Measurable
      (fun z : EuclideanPlane => (planeEuclideanHomeomorph.symm z).1) :=
    (continuous_fst.comp planeEuclideanHomeomorph.symm.continuous).measurable
  rw [euclideanGraphPullbackMeasure,
    Measure.map_apply hproj measurableSet_Ico,
    Measure.restrict_apply (measurableSet_Ico.preimage hproj),
    graph_projection_preimage_inter_range,
    hausdorffMeasure_image_Ico_eq_Icc (S := Set.univ)
      (euclideanGraphParam_injective g).injOn hab (by simp)]
  unfold euclideanGraphParam
  simpa only [Set.image_image] using
    hausdorffMeasure_euclideanGraph_Icc_eq_intervalIntegral hg hab
theorem euclideanGraphPullbackMeasure_eq_withDensity
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    euclideanGraphPullbackMeasure g =
      volume.withDensity (fun x =>
        ENNReal.ofReal (Real.sqrt (1 + (deriv g x) ^ 2))) := by
  apply Measure.ext_of_Ico'
  · intro a b hab
    rw [euclideanGraphPullbackMeasure_Ico hg hab.le]
    exact ENNReal.ofReal_ne_top
  · intro a b hab
    rw [euclideanGraphPullbackMeasure_Ico hg hab.le,
      withDensity_apply _ measurableSet_Ico]
    let speed : ℝ → ℝ := fun x => Real.sqrt (1 + (deriv g x) ^ 2)
    have hspeed : Continuous speed :=
      (continuous_const.add ((hg.continuous_deriv (by norm_num)).pow 2)).sqrt
    have h_integrable : Integrable speed (volume.restrict (Ico a b)) :=
      (hspeed.integrableOn_Icc).mono_set Ico_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal h_integrable
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)]
    congr 1
    rw [intervalIntegral.integral_of_le hab.le,
      ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico]

theorem hausdorffMeasure_euclideanGraph_image_eq_setLIntegral
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {s : Set ℝ} (hs : MeasurableSet s) :
    (μH[1] : Measure EuclideanPlane) (euclideanGraphParam g '' s) =
      ∫⁻ x in s,
        ENNReal.ofReal (Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hproj : Measurable
      (fun z : EuclideanPlane => (planeEuclideanHomeomorph.symm z).1) :=
    (continuous_fst.comp planeEuclideanHomeomorph.symm.continuous).measurable
  have hpull := congrArg (fun μ : Measure ℝ => μ s)
    (euclideanGraphPullbackMeasure_eq_withDensity hg)
  rw [euclideanGraphPullbackMeasure,
    Measure.map_apply hproj hs,
    Measure.restrict_apply (hs.preimage hproj),
    graph_projection_preimage_inter_range,
    withDensity_apply _ hs] at hpull
  exact hpull


theorem hausdorffMeasure_euclideanGraph_inter_eq_setLIntegral
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {A : Set EuclideanPlane} (hA : MeasurableSet A) :
    (μH[1] : Measure EuclideanPlane)
        (Set.range (euclideanGraphParam g) ∩ A) =
      ∫⁻ x in euclideanGraphParam g ⁻¹' A,
        ENNReal.ofReal (Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hcurve : Continuous (euclideanGraphParam g) :=
    planeEuclideanHomeomorph.continuous.comp
      (continuous_id.prodMk hg.continuous)
  have hsource : MeasurableSet (euclideanGraphParam g ⁻¹' A) :=
    hA.preimage hcurve.measurable
  rw [show Set.range (euclideanGraphParam g) ∩ A =
      euclideanGraphParam g '' (euclideanGraphParam g ⁻¹' A) by
        ext z
        constructor
        · rintro ⟨⟨x, rfl⟩, hxA⟩
          exact ⟨x, hxA, rfl⟩
        · rintro ⟨x, hxA, rfl⟩
          exact ⟨⟨x, rfl⟩, hxA⟩]
  exact hausdorffMeasure_euclideanGraph_image_eq_setLIntegral hg hsource

lemma weightedTraceCost_eq_const_mul_hausdorff_of_measurable
    (lam w : ℝ) {S : Set PlanePoint} (hS : MeasurableSet S)
    (hdensity : ∀ p ∈ S, StripDensity lam p = w) :
    weightedTraceCost lam S = ENNReal.ofReal w *
      (μH[1] : Measure EuclideanPlane) (planeEuclideanHomeomorph '' S) := by
  unfold weightedTraceCost
  have hmeas : MeasurableSet (planeEuclideanHomeomorph '' S) :=
    (planeEuclideanHomeomorph.continuous.measurableEmbedding
      planeEuclideanHomeomorph.injective).measurableSet_image' hS
  calc
    (∫⁻ z in planeEuclideanHomeomorph '' S,
        ENNReal.ofReal (euclideanStripDensity lam z)
        ∂(μH[1] : Measure EuclideanPlane)) =
        ∫⁻ _z in planeEuclideanHomeomorph '' S, ENNReal.ofReal w
          ∂(μH[1] : Measure EuclideanPlane) := by
      apply setLIntegral_congr_fun hmeas
      rintro z ⟨p, hp, rfl⟩
      change ENNReal.ofReal
        (StripDensity lam
          (planeEuclideanHomeomorph.symm (planeEuclideanHomeomorph p))) =
        ENNReal.ofReal w
      rw [planeEuclideanHomeomorph.symm_apply_apply, hdensity p hp]
    _ = _ := by simp

theorem weightedTraceCost_graph_image_eq_const_mul_setLIntegral
    (lam w : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hdensity : ∀ p ∈ (fun x : ℝ => (x, g x)) '' s,
      StripDensity lam p = w) :
    weightedTraceCost lam ((fun x : ℝ => (x, g x)) '' s) =
      ENNReal.ofReal w *
        ∫⁻ x in s,
          ENNReal.ofReal (Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hgraph : Continuous (fun x : ℝ => (x, g x)) :=
    continuous_id.prodMk hg.continuous
  have hgraphMeas : MeasurableSet ((fun x : ℝ => (x, g x)) '' s) :=
    (hgraph.measurableEmbedding fun x y hxy => by
      simpa using congrArg Prod.fst hxy).measurableSet_image' hs
  rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam w hgraphMeas hdensity]
  congr 1
  have hmass := hausdorffMeasure_euclideanGraph_image_eq_setLIntegral hg hs
  unfold euclideanGraphParam at hmass
  simpa only [Set.image_image] using hmass


/-- Coordinate exchange on the Euclidean plane, used to transport the exact
graph restriction formula to charts over the second coordinate. -/
def euclideanGraphCoordinateSwap : EuclideanPlane ≃ᵢ EuclideanPlane where
  toEquiv :=
    { toFun := fun p =>
        WithLp.toLp 2 ((WithLp.ofLp p).2, (WithLp.ofLp p).1)
      invFun := fun p =>
        WithLp.toLp 2 ((WithLp.ofLp p).2, (WithLp.ofLp p).1)
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
    change Real.sqrt
        (dist (WithLp.ofLp p).2 (WithLp.ofLp q).2 ^ 2 +
          dist (WithLp.ofLp p).1 (WithLp.ofLp q).1 ^ 2) =
      Real.sqrt
        (dist (WithLp.ofLp p).1 (WithLp.ofLp q).1 ^ 2 +
          dist (WithLp.ofLp p).2 (WithLp.ofLp q).2 ^ 2)
    rw [add_comm]

def euclideanHorizontalGraphParam (g : ℝ → ℝ) (y : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (g y, y)

lemma euclideanHorizontalGraphParam_eq_swap
    (g : ℝ → ℝ) :
    euclideanHorizontalGraphParam g =
      euclideanGraphCoordinateSwap ∘ euclideanGraphParam g := by
  funext y
  rfl

theorem hausdorffMeasure_euclideanHorizontalGraph_image_eq_setLIntegral
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {s : Set ℝ} (hs : MeasurableSet s) :
    (μH[1] : Measure EuclideanPlane)
        (euclideanHorizontalGraphParam g '' s) =
      ∫⁻ y in s,
        ENNReal.ofReal (Real.sqrt (1 + (deriv g y) ^ 2)) := by
  rw [euclideanHorizontalGraphParam_eq_swap, Function.comp_def,
    ← Set.image_image,
    euclideanGraphCoordinateSwap.isometry.hausdorffMeasure_image
      (Or.inl (by norm_num : (0 : ℝ) ≤ 1))]
  exact hausdorffMeasure_euclideanGraph_image_eq_setLIntegral hg hs

theorem weightedTraceCost_horizontalGraph_image_eq_const_mul_setLIntegral
    (lam w : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s)
    (hdensity : ∀ p ∈ (fun y : ℝ => (g y, y)) '' s,
      StripDensity lam p = w) :
    weightedTraceCost lam ((fun y : ℝ => (g y, y)) '' s) =
      ENNReal.ofReal w *
        ∫⁻ y in s,
          ENNReal.ofReal (Real.sqrt (1 + (deriv g y) ^ 2)) := by
  have hgraph : Continuous (fun y : ℝ => (g y, y)) :=
    hg.continuous.prodMk continuous_id
  have hgraphMeas : MeasurableSet ((fun y : ℝ => (g y, y)) '' s) :=
    (hgraph.measurableEmbedding fun x y hxy => by
      simpa using congrArg Prod.snd hxy).measurableSet_image' hs
  rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam w hgraphMeas hdensity]
  congr 1
  have hmass :=
    hausdorffMeasure_euclideanHorizontalGraph_image_eq_setLIntegral hg hs
  unfold euclideanHorizontalGraphParam at hmass
  simpa only [Set.image_image] using hmass

def smoothPhaseZeroTrace (F : PlanePoint → ℝ) (K : Set PlanePoint) : Set PlanePoint :=
  K ∩ {p | F p = 0}

def regularSmoothPhaseZeroTrace (F : PlanePoint → ℝ) (K : Set PlanePoint) : Set PlanePoint :=
  {p | p ∈ K ∧ F p = 0 ∧ fderiv ℝ F p ≠ 0}

def criticalSmoothPhaseZeroTrace (F : PlanePoint → ℝ) (K : Set PlanePoint) : Set PlanePoint :=
  {p | p ∈ K ∧ F p = 0 ∧ fderiv ℝ F p = 0}

def regularSmoothPhaseExhaustion (F : PlanePoint → ℝ) (K : Set PlanePoint)
    (n : ℕ) : Set PlanePoint :=
  {p | p ∈ K ∧ F p = 0 ∧ 1 / (n + 1 : ℝ) ≤ ‖fderiv ℝ F p‖}

lemma smoothPhaseZeroTrace_eq_regular_union_critical (F : PlanePoint → ℝ)
    (K : Set PlanePoint) :
    smoothPhaseZeroTrace F K =
      regularSmoothPhaseZeroTrace F K ∪ criticalSmoothPhaseZeroTrace F K := by
  ext p
  simp only [smoothPhaseZeroTrace, regularSmoothPhaseZeroTrace,
    criticalSmoothPhaseZeroTrace, mem_inter_iff, mem_ofPred_eq, mem_union]
  by_cases hD : fderiv ℝ F p = 0 <;> simp [hD]

lemma regularSmoothPhaseZeroTrace_disjoint_critical (F : PlanePoint → ℝ)
    (K : Set PlanePoint) :
    Disjoint (regularSmoothPhaseZeroTrace F K) (criticalSmoothPhaseZeroTrace F K) := by
  rw [Set.disjoint_left]
  rintro p ⟨_hpK, _hp0, hpD⟩ ⟨_hpK', _hp0', hpD'⟩
  exact hpD hpD'

lemma isCompact_regularSmoothPhaseExhaustion
    {F : PlanePoint → ℝ} {K : Set PlanePoint}
    (hF : ContDiff ℝ ∞ F) (hK : IsCompact K) (n : ℕ) :
    IsCompact (regularSmoothPhaseExhaustion F K n) := by
  have hD : Continuous (fun p => ‖fderiv ℝ F p‖) :=
    (contDiff_infty_iff_fderiv.mp hF).2.continuous.norm
  have hzero : IsClosed {p : PlanePoint | F p = 0} :=
    isClosed_eq hF.continuous continuous_const
  have hbound : IsClosed {p : PlanePoint |
      1 / (n + 1 : ℝ) ≤ ‖fderiv ℝ F p‖} :=
    isClosed_le continuous_const hD
  change IsCompact (K ∩ ({p : PlanePoint | F p = 0} ∩
    {p : PlanePoint | 1 / (n + 1 : ℝ) ≤ ‖fderiv ℝ F p‖}))
  exact hK.inter_right (hzero.inter hbound)

lemma iUnion_regularSmoothPhaseExhaustion
    (F : PlanePoint → ℝ) (K : Set PlanePoint) :
    (⋃ n : ℕ, regularSmoothPhaseExhaustion F K n) =
      regularSmoothPhaseZeroTrace F K := by
  apply Set.Subset.antisymm
  · rintro p hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hpK, hp0, hpD⟩
    refine ⟨hpK, hp0, ?_⟩
    have hpos : 0 < (1 / (n + 1 : ℝ)) := by positivity
    exact (norm_pos_iff.mp (hpos.trans_le hpD))
  · rintro p ⟨hpK, hp0, hpD⟩
    have hnorm : 0 < ‖fderiv ℝ F p‖ := norm_pos_iff.mpr hpD
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm
    exact Set.mem_iUnion.mpr ⟨n, hpK, hp0, hn.le⟩


/-- Whether an implicit-function chart is a graph over the first or second coordinate. -/
inductive SmoothPhaseGraphOrientation
  | overFirst
  | overSecond
  deriving DecidableEq

def SmoothPhaseGraphOrientation.OnGraph
    (o : SmoothPhaseGraphOrientation) (φ : ℝ → ℝ) (p : PlanePoint) : Prop :=
  match o with
  | .overFirst => p.2 = φ p.1
  | .overSecond => p.1 = φ p.2

/-- A genuine implicit-function chart for the zero set of one smooth phase. -/
structure SmoothPhaseGraphChart (F : PlanePoint → ℝ) where
  base : PlanePoint
  orientation : SmoothPhaseGraphOrientation
  window : Set PlanePoint
  window_open : IsOpen window
  base_mem_window : base ∈ window
  graph : ℝ → ℝ
  graph_smooth : ContDiff ℝ ∞ graph
  zero_iff_onGraph :
    ∀ p ∈ window, F p = 0 ↔ orientation.OnGraph graph p


/-- A regular zero has a smooth graph chart in one of the two coordinate
orientations; no orientation is supplied by the caller. -/
theorem exists_smoothPhaseGraphChart
    {F : PlanePoint → ℝ} (hF : ContDiff ℝ ∞ F)
    {p : PlanePoint} (hp0 : F p = 0) (hpreg : fderiv ℝ F p ≠ 0) :
    ∃ C : SmoothPhaseGraphChart F, C.base = p := by
  rcases continuousLinearMap_ne_zero_has_coordinate (fderiv ℝ F p) hpreg with
      hx | hy
  · let e : PlanePoint ≃L[ℝ] PlanePoint :=
      ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    let u : PlanePoint := (p.2, p.1)
    have hFs : ContDiff ℝ ∞ (F ∘ e) := hF.comp e.contDiff
    have hFsderiv :
        HasFDerivAt (F ∘ e) ((fderiv ℝ F p).comp (e : PlanePoint →L[ℝ] PlanePoint)) u := by
      simpa [u, e] using
        (hF.differentiable (by simp) p).hasFDerivAt.comp u e.hasFDerivAt
    have htrans : fderiv ℝ (F ∘ e) u (0, 1) ≠ 0 := by
      simpa [hFsderiv.fderiv, ContinuousLinearMap.comp_apply, e, u] using hx
    obtain ⟨φ, hφ, hφu, hlocalSwap⟩ :=
      exists_contDiff_infty_implicitGraph_of_contDiffOn
        (V := Set.univ) (u := u) (f := F ∘ e) isOpen_univ
        (by simp [u]) hFs.contDiffOn htrans
    have hlocal :
        ∀ᶠ q : PlanePoint in 𝓝 p,
          F q = F p ↔ φ q.2 = q.1 := by
      have hs := e.continuousAt.tendsto.eventually hlocalSwap
      simpa [e, u] using hs
    rcases mem_nhds_iff.mp hlocal with ⟨V, hVsub, hVopen, hpV⟩
    refine ⟨{
      base := p
      orientation := .overSecond
      window := V
      window_open := hVopen
      base_mem_window := hpV
      graph := φ
      graph_smooth := hφ
      zero_iff_onGraph := ?_ }, rfl⟩
    intro q hq
    simpa [SmoothPhaseGraphOrientation.OnGraph, hp0, eq_comm] using hVsub hq
  · obtain ⟨φ, hφ, hφp, hlocal⟩ :=
      exists_contDiff_infty_implicitGraph_of_contDiffOn
        (V := Set.univ) (u := p) (f := F) isOpen_univ
        (by simp) hF.contDiffOn hy
    rcases mem_nhds_iff.mp hlocal with ⟨V, hVsub, hVopen, hpV⟩
    refine ⟨{
      base := p
      orientation := .overFirst
      window := V
      window_open := hVopen
      base_mem_window := hpV
      graph := φ
      graph_smooth := hφ
      zero_iff_onGraph := ?_ }, rfl⟩
    intro q hq
    simpa [SmoothPhaseGraphOrientation.OnGraph, hp0, eq_comm] using hVsub hq


/-- Compactness extracts a finite family of genuine implicit charts from the
regularity of a phase; neither an atlas nor exact atlas equality is assumed. -/
theorem exists_finite_smoothPhaseGraphChart_cover
    {F : PlanePoint → ℝ} {S : Set PlanePoint}
    (hF : ContDiff ℝ ∞ F) (hS : IsCompact S)
    (hzero : ∀ p ∈ S, F p = 0)
    (hreg : ∀ p ∈ S, fderiv ℝ F p ≠ 0) :
    ∃ (N : ℕ) (C : Fin N → SmoothPhaseGraphChart F),
      S ⊆ ⋃ i, (C i).window := by
  let A : (p : S) → SmoothPhaseGraphChart F := fun p =>
    Classical.choose
      (exists_smoothPhaseGraphChart hF (hzero p p.property) (hreg p p.property))
  have hAbase (p : S) : (A p).base = p :=
    Classical.choose_spec
      (exists_smoothPhaseGraphChart hF (hzero p p.property) (hreg p p.property))
  have hcover : S ⊆ ⋃ p : S, (A p).window := by
    intro p hp
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    simpa [hAbase] using (A ⟨p, hp⟩).base_mem_window
  obtain ⟨t, ht⟩ :=
    hS.elim_finite_subcover (fun p : S => (A p).window)
      (fun p => (A p).window_open) hcover
  let e : Fin (Fintype.card {p : S // p ∈ t}) ≃ {p : S // p ∈ t} :=
    (Fintype.equivFin {p : S // p ∈ t}).symm
  refine ⟨Fintype.card {p : S // p ∈ t}, fun i => A (e i).1, ?_⟩
  intro p hp
  rcases Set.mem_iUnion.mp (ht hp) with ⟨q, hq⟩
  rcases Set.mem_iUnion.mp hq with ⟨hqt, hpwindow⟩
  refine Set.mem_iUnion.mpr ⟨e.symm ⟨q, hqt⟩, ?_⟩
  simpa using hpwindow


/-- The `n`th member of a finite chart cover, padded by empty sets to a
countable family. -/
def finiteSmoothPhaseChartSource
    {F : PlanePoint → ℝ} {N : ℕ} (S : Set PlanePoint)
    (C : Fin N → SmoothPhaseGraphChart F) (n : ℕ) : Set PlanePoint :=
  if hn : n < N then S ∩ (C ⟨n, hn⟩).window else ∅

/-- Canonical overlap removal. `disjointed` retains the first occurrence of
each point and therefore does not require supplied chart disjointness. -/
def finiteSmoothPhaseChartPiece
    {F : PlanePoint → ℝ} {N : ℕ} (S : Set PlanePoint)
    (C : Fin N → SmoothPhaseGraphChart F) (n : ℕ) : Set PlanePoint :=
  disjointed (finiteSmoothPhaseChartSource S C) n

lemma iUnion_finiteSmoothPhaseChartSource
    {F : PlanePoint → ℝ} {N : ℕ} {S : Set PlanePoint}
    {C : Fin N → SmoothPhaseGraphChart F}
    (hcover : S ⊆ ⋃ i, (C i).window) :
    (⋃ n : ℕ, finiteSmoothPhaseChartSource S C n) = S := by
  apply Set.Subset.antisymm
  · refine Set.iUnion_subset fun n => ?_
    simp only [finiteSmoothPhaseChartSource]
    split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  · intro p hp
    rcases Set.mem_iUnion.mp (hcover hp) with ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨i.1, ?_⟩
    simpa [finiteSmoothPhaseChartSource, i.2] using And.intro hp hi

lemma iUnion_finiteSmoothPhaseChartPiece
    {F : PlanePoint → ℝ} {N : ℕ} {S : Set PlanePoint}
    {C : Fin N → SmoothPhaseGraphChart F}
    (hcover : S ⊆ ⋃ i, (C i).window) :
    (⋃ n : ℕ, finiteSmoothPhaseChartPiece S C n) = S := by
  change (⋃ n : ℕ, disjointed (finiteSmoothPhaseChartSource S C) n) = S
  rw [iUnion_disjointed, iUnion_finiteSmoothPhaseChartSource hcover]

lemma measurableSet_finiteSmoothPhaseChartSource
    {F : PlanePoint → ℝ} {N : ℕ} {S : Set PlanePoint}
    (hS : MeasurableSet S) (C : Fin N → SmoothPhaseGraphChart F) (n : ℕ) :
    MeasurableSet (finiteSmoothPhaseChartSource S C n) := by
  simp only [finiteSmoothPhaseChartSource]
  split_ifs with hn
  · exact hS.inter (C ⟨n, hn⟩).window_open.measurableSet
  · exact MeasurableSet.empty

lemma measurableSet_finiteSmoothPhaseChartPiece
    {F : PlanePoint → ℝ} {N : ℕ} {S : Set PlanePoint}
    (hS : MeasurableSet S) (C : Fin N → SmoothPhaseGraphChart F) (n : ℕ) :
    MeasurableSet (finiteSmoothPhaseChartPiece S C n) :=
  MeasurableSet.disjointed
    (measurableSet_finiteSmoothPhaseChartSource hS C) n

lemma pairwise_disjoint_finiteSmoothPhaseChartPiece
    {F : PlanePoint → ℝ} {N : ℕ} (S : Set PlanePoint)
    (C : Fin N → SmoothPhaseGraphChart F) :
    Pairwise (Disjoint on finiteSmoothPhaseChartPiece S C) :=
  disjoint_disjointed _

lemma finiteSmoothPhaseChartPiece_subset_onGraph
    {F : PlanePoint → ℝ} {N : ℕ} {S : Set PlanePoint}
    (hzero : ∀ p ∈ S, F p = 0)
    (C : Fin N → SmoothPhaseGraphChart F) {n : ℕ} (hn : n < N) :
    finiteSmoothPhaseChartPiece S C n ⊆
      {p | (C ⟨n, hn⟩).orientation.OnGraph (C ⟨n, hn⟩).graph p} := by
  intro p hp
  have hsource :
      p ∈ finiteSmoothPhaseChartSource S C n :=
    disjointed_subset _ n hp
  have hpSW : p ∈ S ∩ (C ⟨n, hn⟩).window := by
    simpa [finiteSmoothPhaseChartSource, hn] using hsource
  exact ((C ⟨n, hn⟩).zero_iff_onGraph p hpSW.2).mp (hzero p hpSW.1)

lemma finiteSmoothPhaseChartPiece_eq_empty_of_le
    {F : PlanePoint → ℝ} {N : ℕ} (S : Set PlanePoint)
    (C : Fin N → SmoothPhaseGraphChart F) {n : ℕ} (hn : N ≤ n) :
    finiteSmoothPhaseChartPiece S C n = ∅ := by
  ext p
  constructor
  · intro hp
    have hsource := disjointed_subset (finiteSmoothPhaseChartSource S C) n hp
    simpa [finiteSmoothPhaseChartSource, not_lt.mpr hn] using hsource
  · simp


lemma finiteSmoothPhaseChartPiece_subset
    {F : PlanePoint → ℝ} {N : ℕ} (S : Set PlanePoint)
    (C : Fin N → SmoothPhaseGraphChart F) (n : ℕ) :
    finiteSmoothPhaseChartPiece S C n ⊆ S := by
  refine (disjointed_subset (finiteSmoothPhaseChartSource S C) n).trans ?_
  simp only [finiteSmoothPhaseChartSource]
  split_ifs
  · exact inter_subset_left
  · exact empty_subset _

/-- Disjoint compact-exhaustion layers of the regular zero locus. -/
def regularSmoothPhaseLayer (F : PlanePoint → ℝ) (K : Set PlanePoint)
    (n : ℕ) : Set PlanePoint :=
  disjointed (regularSmoothPhaseExhaustion F K) n

lemma measurableSet_regularSmoothPhaseLayer
    {F : PlanePoint → ℝ} {K : Set PlanePoint}
    (hF : ContDiff ℝ ∞ F) (hK : IsCompact K) (n : ℕ) :
    MeasurableSet (regularSmoothPhaseLayer F K n) := by
  exact MeasurableSet.disjointed
    (fun m => (isCompact_regularSmoothPhaseExhaustion hF hK m).measurableSet) n

lemma pairwise_disjoint_regularSmoothPhaseLayer
    (F : PlanePoint → ℝ) (K : Set PlanePoint) :
    Pairwise (Disjoint on regularSmoothPhaseLayer F K) :=
  disjoint_disjointed _

lemma iUnion_regularSmoothPhaseLayer
    (F : PlanePoint → ℝ) (K : Set PlanePoint) :
    (⋃ n : ℕ, regularSmoothPhaseLayer F K n) =
      regularSmoothPhaseZeroTrace F K := by
  change (⋃ n : ℕ, disjointed (regularSmoothPhaseExhaustion F K) n) =
    regularSmoothPhaseZeroTrace F K
  rw [iUnion_disjointed, iUnion_regularSmoothPhaseExhaustion]

/-- The regular zero locus of a general smooth phase on a compact set admits a
derived countable measurable disjoint decomposition into restrictions of
smooth coordinate graphs. Critical zeros remain in the explicit complementary
`criticalSmoothPhaseZeroTrace`; they are not silently discarded. -/
theorem exists_countable_measurable_disjoint_smoothPhaseGraph_decomposition
    {F : PlanePoint → ℝ} {K : Set PlanePoint}
    (hF : ContDiff ℝ ∞ F) (hK : IsCompact K) :
    ∃ (N : ℕ → ℕ)
      (C : ∀ n, Fin (N n) → SmoothPhaseGraphChart F),
      (⋃ n : ℕ, ⋃ m : ℕ,
          finiteSmoothPhaseChartPiece (regularSmoothPhaseLayer F K n) (C n) m) =
        regularSmoothPhaseZeroTrace F K ∧
      (∀ n m, MeasurableSet
        (finiteSmoothPhaseChartPiece (regularSmoothPhaseLayer F K n) (C n) m)) ∧
      Pairwise (Disjoint on fun q : ℕ × ℕ =>
        finiteSmoothPhaseChartPiece
          (regularSmoothPhaseLayer F K q.1) (C q.1) q.2) ∧
      (∀ n m (hm : m < N n),
        finiteSmoothPhaseChartPiece (regularSmoothPhaseLayer F K n) (C n) m ⊆
          {p | (C n ⟨m, hm⟩).orientation.OnGraph
            (C n ⟨m, hm⟩).graph p}) ∧
      (∀ n m, N n ≤ m →
        finiteSmoothPhaseChartPiece
          (regularSmoothPhaseLayer F K n) (C n) m = ∅) := by
  have hexists (n : ℕ) :
      ∃ (M : ℕ) (D : Fin M → SmoothPhaseGraphChart F),
        regularSmoothPhaseExhaustion F K n ⊆ ⋃ i, (D i).window := by
    apply exists_finite_smoothPhaseGraphChart_cover hF
      (isCompact_regularSmoothPhaseExhaustion hF hK n)
    · intro p hp
      exact hp.2.1
    · intro p hp
      have hpos : 0 < (1 / (n + 1 : ℝ)) := by positivity
      exact norm_pos_iff.mp (hpos.trans_le hp.2.2)
  choose N C hcover using hexists
  have hlayerSubset (n : ℕ) :
      regularSmoothPhaseLayer F K n ⊆
        regularSmoothPhaseExhaustion F K n :=
    disjointed_subset _ n
  have hlayerCover (n : ℕ) :
      regularSmoothPhaseLayer F K n ⊆ ⋃ i, (C n i).window :=
    hlayerSubset n |>.trans (hcover n)
  have hzeroLayer (n : ℕ) :
      ∀ p ∈ regularSmoothPhaseLayer F K n, F p = 0 := by
    intro p hp
    exact (hlayerSubset n hp).2.1
  refine ⟨N, C, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (⋃ n : ℕ, ⋃ m : ℕ,
          finiteSmoothPhaseChartPiece
            (regularSmoothPhaseLayer F K n) (C n) m) =
          ⋃ n : ℕ, regularSmoothPhaseLayer F K n := by
            apply iUnion_congr
            intro n
            exact iUnion_finiteSmoothPhaseChartPiece (hlayerCover n)
      _ = regularSmoothPhaseZeroTrace F K :=
        iUnion_regularSmoothPhaseLayer F K
  · intro n m
    exact measurableSet_finiteSmoothPhaseChartPiece
      (measurableSet_regularSmoothPhaseLayer hF hK n) (C n) m
  · rintro ⟨n, m⟩ ⟨n', m'⟩ hne
    by_cases hnn : n = n'
    · subst n'
      have hmm : m ≠ m' := by
        intro h
        subst m'
        exact hne rfl
      exact pairwise_disjoint_finiteSmoothPhaseChartPiece
        (regularSmoothPhaseLayer F K n) (C n) hmm
    · exact Disjoint.mono
        (finiteSmoothPhaseChartPiece_subset
          (regularSmoothPhaseLayer F K n) (C n) m)
        (finiteSmoothPhaseChartPiece_subset
          (regularSmoothPhaseLayer F K n') (C n') m')
        (pairwise_disjoint_regularSmoothPhaseLayer F K hnn)
  · intro n m hm
    exact finiteSmoothPhaseChartPiece_subset_onGraph
      (hzeroLayer n) (C n) hm
  · intro n m hm
    exact finiteSmoothPhaseChartPiece_eq_empty_of_le
      (regularSmoothPhaseLayer F K n) (C n) hm
variable {F : PlanePoint → ℝ}

def SmoothPhaseGraphChart.source
    (C : SmoothPhaseGraphChart F) (S : Set PlanePoint) : Set ℝ :=
  match C.orientation with
  | .overFirst => (fun x : ℝ => (x, C.graph x)) ⁻¹' S
  | .overSecond => (fun y : ℝ => (C.graph y, y)) ⁻¹' S

lemma SmoothPhaseGraphChart.measurableSet_source
    (C : SmoothPhaseGraphChart F) {S : Set PlanePoint} (hS : MeasurableSet S) :
    MeasurableSet (C.source S) := by
  cases h : C.orientation with
  | overFirst =>
      simpa [SmoothPhaseGraphChart.source, h] using
        hS.preimage (continuous_id.prodMk C.graph_smooth.continuous).measurable
  | overSecond =>
      simpa [SmoothPhaseGraphChart.source, h] using
        hS.preimage (C.graph_smooth.continuous.prodMk continuous_id).measurable

lemma SmoothPhaseGraphChart.eq_orientedGraph_image_source
    (C : SmoothPhaseGraphChart F) {S : Set PlanePoint}
    (hgraph : S ⊆ {p | C.orientation.OnGraph C.graph p}) :
    S = match C.orientation with
      | .overFirst => (fun x : ℝ => (x, C.graph x)) '' C.source S
      | .overSecond => (fun y : ℝ => (C.graph y, y)) '' C.source S := by
  cases h : C.orientation with
  | overFirst =>
      simp only [h, SmoothPhaseGraphOrientation.OnGraph] at hgraph
      simp only [SmoothPhaseGraphChart.source, h]
      ext p
      constructor
      · intro hp
        refine ⟨p.1, ?_, ?_⟩
        · change (p.1, C.graph p.1) ∈ S
          rw [show (p.1, C.graph p.1) = p by
            ext
            · rfl
            · exact (hgraph hp).symm]
          exact hp
        · ext
          · rfl
          · exact (hgraph hp).symm
      · rintro ⟨x, hx, rfl⟩
        simpa [SmoothPhaseGraphChart.source, h] using hx
  | overSecond =>
      simp only [h, SmoothPhaseGraphOrientation.OnGraph] at hgraph
      simp only [SmoothPhaseGraphChart.source, h]
      ext p
      constructor
      · intro hp
        refine ⟨p.2, ?_, ?_⟩
        · change (C.graph p.2, p.2) ∈ S
          rw [show (C.graph p.2, p.2) = p by
            ext
            · exact (hgraph hp).symm
            · rfl]
          exact hp
        · ext
          · exact (hgraph hp).symm
          · rfl
      · rintro ⟨y, hy, rfl⟩
        simpa [SmoothPhaseGraphChart.source, h] using hy

/-- Every measurable restriction of a derived phase chart has the exact
coefficient-one weighted graph formula when its trace lies in one
constant-density region. -/
theorem weightedTraceCost_smoothPhaseGraphChart_subset_eq
    (lam w : ℝ) (C : SmoothPhaseGraphChart F)
    {S : Set PlanePoint} (hS : MeasurableSet S)
    (hgraph : S ⊆ {p | C.orientation.OnGraph C.graph p})
    (hdensity : ∀ p ∈ S, StripDensity lam p = w) :
    weightedTraceCost lam S = ENNReal.ofReal w *
      ∫⁻ t in C.source S,
        ENNReal.ofReal (Real.sqrt (1 + (deriv C.graph t) ^ 2)) := by
  have hsource := C.measurableSet_source hS
  cases h : C.orientation with
  | overFirst =>
      have hset := C.eq_orientedGraph_image_source hgraph
      simp only [h] at hset
      calc
        weightedTraceCost lam S =
            weightedTraceCost lam
              ((fun x : ℝ => (x, C.graph x)) '' C.source S) :=
          congrArg (weightedTraceCost lam) hset
        _ = _ := weightedTraceCost_graph_image_eq_const_mul_setLIntegral
          lam w (C.graph_smooth.of_le (by norm_num)) hsource (by
            intro p hp
            apply hdensity p
            rw [hset]
            exact hp)
  | overSecond =>
      have hset := C.eq_orientedGraph_image_source hgraph
      simp only [h] at hset
      calc
        weightedTraceCost lam S =
            weightedTraceCost lam
              ((fun y : ℝ => (C.graph y, y)) '' C.source S) :=
          congrArg (weightedTraceCost lam) hset
        _ = _ := weightedTraceCost_horizontalGraph_image_eq_const_mul_setLIntegral
          lam w (C.graph_smooth.of_le (by norm_num)) hsource (by
            intro p hp
            apply hdensity p
            rw [hset]
            exact hp)

/-- Exact local cost for each nonempty member of the internally disjointized
finite chart cover. -/
theorem weightedTraceCost_finiteSmoothPhaseChartPiece_eq
    (lam w : ℝ) {N : ℕ} {S : Set PlanePoint}
    (hS : MeasurableSet S) (hzero : ∀ p ∈ S, F p = 0)
    (C : Fin N → SmoothPhaseGraphChart F) {n : ℕ} (hn : n < N)
    (hdensity : ∀ p ∈ finiteSmoothPhaseChartPiece S C n,
      StripDensity lam p = w) :
    weightedTraceCost lam (finiteSmoothPhaseChartPiece S C n) =
      ENNReal.ofReal w *
        ∫⁻ t in (C ⟨n, hn⟩).source (finiteSmoothPhaseChartPiece S C n),
          ENNReal.ofReal
            (Real.sqrt (1 + (deriv (C ⟨n, hn⟩).graph t) ^ 2)) := by
  exact weightedTraceCost_smoothPhaseGraphChart_subset_eq lam w (C ⟨n, hn⟩)
    (measurableSet_finiteSmoothPhaseChartPiece hS C n)
    (finiteSmoothPhaseChartPiece_subset_onGraph hzero C hn) hdensity
lemma weightedTraceCost_iUnion_eq_tsum
    {ι : Type*} [Countable ι] (lam : ℝ) (S : ι → Set PlanePoint)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise (Disjoint on S)) :
    weightedTraceCost lam (⋃ i, S i) = ∑' i, weightedTraceCost lam (S i) := by
  have himageMeas (i : ι) : MeasurableSet
      (planeEuclideanHomeomorph '' S i) :=
    (planeEuclideanHomeomorph.continuous.measurableEmbedding
      planeEuclideanHomeomorph.injective).measurableSet_image' (hmeas i)
  have himagePair : Pairwise (Disjoint on fun i : ι =>
      planeEuclideanHomeomorph '' S i) := by
    intro i j hij
    change Disjoint
      (planeEuclideanHomeomorph '' S i)
      (planeEuclideanHomeomorph '' S j)
    rw [Set.disjoint_left]
    rintro z ⟨pi, hpi, rfl⟩ ⟨pj, hpj, heq⟩
    have hpij : pi = pj := planeEuclideanHomeomorph.injective heq.symm
    exact (Set.disjoint_left.mp (hpair hij)) hpi (hpij ▸ hpj)
  unfold weightedTraceCost
  rw [image_iUnion, lintegral_iUnion himageMeas himagePair]

lemma smoothPhaseZeroTrace_eq_regular_of_regular
    {F : PlanePoint → ℝ} {K : Set PlanePoint}
    (hreg : ∀ p ∈ K, F p = 0 → fderiv ℝ F p ≠ 0) :
    smoothPhaseZeroTrace F K = regularSmoothPhaseZeroTrace F K := by
  ext p
  constructor
  · rintro ⟨hpK, hp0⟩
    exact ⟨hpK, hp0, hreg p hpK hp0⟩
  · rintro ⟨hpK, hp0, _hpreg⟩
    exact ⟨hpK, hp0⟩

def smoothPhaseChartPieceCost
    (w : ℝ) {F : PlanePoint → ℝ} (K : Set PlanePoint)
    (N : ℕ → ℕ) (C : ∀ n, Fin (N n) → SmoothPhaseGraphChart F)
    (q : ℕ × ℕ) : ℝ≥0∞ :=
  if hq : q.2 < N q.1 then
    ENNReal.ofReal w *
      ∫⁻ t in (C q.1 ⟨q.2, hq⟩).source
          (finiteSmoothPhaseChartPiece
            (regularSmoothPhaseLayer F K q.1) (C q.1) q.2),
        ENNReal.ofReal
          (Real.sqrt (1 + (deriv (C q.1 ⟨q.2, hq⟩).graph t) ^ 2))
  else 0

/-- A compact regular zero trace of a general smooth phase has an internally
derived, coefficient-one actual weighted `H¹` formula. The chart family,
exhaustion, and disjointization are outputs rather than premises. -/
theorem exists_smoothPhaseZeroTrace_cost_eq_tsum_graphPieces
    {F : PlanePoint → ℝ} {K : Set PlanePoint}
    (hF : ContDiff ℝ ∞ F) (hK : IsCompact K)
    (hreg : ∀ p ∈ K, F p = 0 → fderiv ℝ F p ≠ 0)
    (lam w : ℝ)
    (hdensity : ∀ p ∈ smoothPhaseZeroTrace F K,
      StripDensity lam p = w) :
    ∃ (N : ℕ → ℕ)
      (C : ∀ n, Fin (N n) → SmoothPhaseGraphChart F),
      weightedTraceCost lam (smoothPhaseZeroTrace F K) =
        ∑' q : ℕ × ℕ, smoothPhaseChartPieceCost w K N C q := by
  obtain ⟨N, C, hunion, hmeas, hpair, hgraph, hempty⟩ :=
    exists_countable_measurable_disjoint_smoothPhaseGraph_decomposition hF hK
  let P : ℕ × ℕ → Set PlanePoint := fun q =>
    finiteSmoothPhaseChartPiece
      (regularSmoothPhaseLayer F K q.1) (C q.1) q.2
  have hprodUnion : (⋃ q : ℕ × ℕ, P q) =
      regularSmoothPhaseZeroTrace F K := by
    rw [show (⋃ q : ℕ × ℕ, P q) = ⋃ n : ℕ, ⋃ m : ℕ, P (n, m) by
      ext p
      simp only [mem_iUnion]
      constructor
      · rintro ⟨⟨n, m⟩, hp⟩
        exact ⟨n, m, hp⟩
      · rintro ⟨n, m, hp⟩
        exact ⟨(n, m), hp⟩]
    exact hunion
  refine ⟨N, C, ?_⟩
  calc
    weightedTraceCost lam (smoothPhaseZeroTrace F K) =
        weightedTraceCost lam (regularSmoothPhaseZeroTrace F K) := by
      rw [smoothPhaseZeroTrace_eq_regular_of_regular hreg]
    _ = weightedTraceCost lam (⋃ q : ℕ × ℕ, P q) := by rw [hprodUnion]
    _ = ∑' q : ℕ × ℕ, weightedTraceCost lam (P q) :=
      weightedTraceCost_iUnion_eq_tsum lam P
        (fun q => hmeas q.1 q.2) hpair
    _ = ∑' q : ℕ × ℕ, smoothPhaseChartPieceCost w K N C q := by
      apply tsum_congr
      rintro ⟨n, m⟩
      by_cases hm : m < N n
      · rw [weightedTraceCost_finiteSmoothPhaseChartPiece_eq lam w
          (measurableSet_regularSmoothPhaseLayer hF hK n)
          (fun p hp =>
            ((disjointed_subset (regularSmoothPhaseExhaustion F K) n hp).2.1))
          (C n) hm]
        · simp [smoothPhaseChartPieceCost, hm]
        · intro p hp
          apply hdensity p
          have hplayer := finiteSmoothPhaseChartPiece_subset
            (regularSmoothPhaseLayer F K n) (C n) m hp
          have hpexhaustion :=
            disjointed_subset (regularSmoothPhaseExhaustion F K) n hplayer
          exact ⟨hpexhaustion.1, hpexhaustion.2.1⟩
      · have hpiece :
            finiteSmoothPhaseChartPiece
                (regularSmoothPhaseLayer F K n) (C n) m = ∅ :=
          hempty n m (Nat.le_of_not_gt hm)
        simp [P, hpiece, smoothPhaseChartPieceCost, hm, weightedTraceCost]
end CMVRelaxation
