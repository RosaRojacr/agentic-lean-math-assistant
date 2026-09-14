import CMVRegularGermInterfaceExtension

/-!
# Exact weighted-area compensation for a regular interface extension

A remote density-local graph patch on the unchanged representative supplies the
internally normalized compensation bump.  The corrected carrier is defined by
symmetric-difference replacement, so the extension and compensation remain two
literal alterations of the same representative.  No minimality, contact law,
first variation, or perimeter comparison is assumed here.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

open CMVTwoPatchGraphVariation

/-- Replace `old` by `new` inside an ambient carrier by toggling exactly their
symmetric difference. -/
def replaceBySymmDiff (ambient old new : Set PlanePoint) : Set PlanePoint :=
  ambient ∆ (old ∆ new)

lemma measurableSet_replaceBySymmDiff {ambient old new : Set PlanePoint}
    (hambient : MeasurableSet ambient) (hold : MeasurableSet old)
    (hnew : MeasurableSet new) :
    MeasurableSet (replaceBySymmDiff ambient old new) :=
  hambient.symmDiff (hold.symmDiff hnew)

lemma replaceBySymmDiff_subset_union (ambient old new : Set PlanePoint) :
    replaceBySymmDiff ambient old new ⊆ ambient ∪ old ∪ new := by
  intro p hp
  simp only [replaceBySymmDiff, Set.mem_symmDiff] at hp
  rcases hp with ⟨hpAmbient, _⟩ | ⟨hpLocal, _⟩
  · exact Or.inl (Or.inl hpAmbient)
  · rcases hpLocal with ⟨hpOld, _⟩ | ⟨hpNew, _⟩
    · exact Or.inl (Or.inr hpOld)
    · exact Or.inr hpNew

lemma isBounded_replaceBySymmDiff {ambient old new : Set PlanePoint}
    (hambient : Bornology.IsBounded ambient)
    (hold : Bornology.IsBounded old) (hnew : Bornology.IsBounded new) :
    Bornology.IsBounded (replaceBySymmDiff ambient old new) :=
  (hambient.union hold |>.union hnew).subset
    (replaceBySymmDiff_subset_union ambient old new)

lemma replaceBySymmDiff_symmDiff_ambient
    (ambient old new : Set PlanePoint) :
    replaceBySymmDiff ambient old new ∆ ambient = old ∆ new := by
  ext p
  simp only [replaceBySymmDiff, Set.mem_symmDiff]
  tauto

/-- If the ambient carrier agrees with the old local model wherever the old
and new models differ, symmetric-difference replacement changes the literal
weighted area by exactly the local model's weighted-area change. -/
theorem weightedArea_replaceBySymmDiff_sub
    {lam : ℝ} {ambient old new W : Set PlanePoint}
    (hambientMeas : MeasurableSet ambient) (holdMeas : MeasurableSet old)
    (hnewMeas : MeasurableSet new)
    (hambientBounded : Bornology.IsBounded ambient)
    (holdBounded : Bornology.IsBounded old)
    (hnewBounded : Bornology.IsBounded new)
    (hchange : old ∆ new ⊆ W)
    (hlocal : ∀ p ∈ W, (p ∈ ambient ↔ p ∈ old)) :
    WeightedArea lam (replaceBySymmDiff ambient old new) -
        WeightedArea lam ambient =
      WeightedArea lam new - WeightedArea lam old := by
  let f : PlanePoint → ℝ := StripDensity lam
  have hreplMeas : MeasurableSet (replaceBySymmDiff ambient old new) :=
    measurableSet_replaceBySymmDiff hambientMeas holdMeas hnewMeas
  have hreplBounded : Bornology.IsBounded
      (replaceBySymmDiff ambient old new) :=
    isBounded_replaceBySymmDiff hambientBounded holdBounded hnewBounded
  have hintAmbient : IntegrableOn f ambient :=
    stripDensity_integrableOn_of_volume_ne_top lam
      hambientBounded.measure_lt_top.ne
  have hintOld : IntegrableOn f old :=
    stripDensity_integrableOn_of_volume_ne_top lam holdBounded.measure_lt_top.ne
  have hintNew : IntegrableOn f new :=
    stripDensity_integrableOn_of_volume_ne_top lam hnewBounded.measure_lt_top.ne
  have hintRepl : IntegrableOn f (replaceBySymmDiff ambient old new) :=
    stripDensity_integrableOn_of_volume_ne_top lam hreplBounded.measure_lt_top.ne
  have hpoint : ∀ p : PlanePoint,
      (replaceBySymmDiff ambient old new).indicator f p - ambient.indicator f p =
        new.indicator f p - old.indicator f p := by
    intro p
    by_cases holdp : p ∈ old <;> by_cases hnewp : p ∈ new
    · by_cases hambientp : p ∈ ambient <;>
        simp [replaceBySymmDiff, Set.mem_symmDiff, holdp, hnewp, hambientp]
    · have hpchange : p ∈ old ∆ new := by
        simp [Set.mem_symmDiff, holdp, hnewp]
      have hambientp : p ∈ ambient := (hlocal p (hchange hpchange)).2 holdp
      simp [replaceBySymmDiff, Set.mem_symmDiff, holdp, hnewp, hambientp]
    · have hpchange : p ∈ old ∆ new := by
        simp [Set.mem_symmDiff, holdp, hnewp]
      have hambientp : p ∉ ambient := by
        intro hp
        exact holdp ((hlocal p (hchange hpchange)).1 hp)
      simp [replaceBySymmDiff, Set.mem_symmDiff, holdp, hnewp, hambientp]
    · by_cases hambientp : p ∈ ambient <;>
        simp [replaceBySymmDiff, Set.mem_symmDiff, holdp, hnewp, hambientp]
  unfold WeightedArea
  rw [← integral_indicator hreplMeas, ← integral_indicator hambientMeas,
    ← integral_indicator hnewMeas, ← integral_indicator holdMeas,
    ← integral_sub (hintRepl.integrable_indicator hreplMeas)
      (hintAmbient.integrable_indicator hambientMeas),
    ← integral_sub (hintNew.integrable_indicator hnewMeas)
      (hintOld.integrable_indicator holdMeas)]
  exact integral_congr_ae (Eventually.of_forall hpoint)

end CMVRelaxation.RegularTraceCornerComparison

namespace CMVTwoPatchGraphVariation.GraphPatch

/-- The canonical normalized bump, packaged as a primary graph variation. -/
def normalizedCompensationVariation (P : GraphPatch) : PrimaryVariation P where
  toFun := P.compensationBump
  contDiff := P.compensationBump_contDiff.of_le (by
    apply WithTop.coe_le_coe.mpr
    exact le_top)
  tsupport_subset := P.tsupport_compensationBump_subset

@[simp] theorem normalizedCompensationVariation_apply (P : GraphPatch) (x : ℝ) :
    P.normalizedCompensationVariation x = P.compensationBump x := rfl

/-- Forced scalar multiplying the unit-integral bump to create a prescribed
signed weighted-area change. -/
def prescribedAreaScale (P : GraphPatch) (lam delta : ℝ) : ℝ :=
  delta / (P.side.areaSign * P.zone.weight lam)

/-- The normalized graph bump changes literal weighted area by the prescribed
amount.  Both the occupied-side orientation and the local density price are
accounted for in `prescribedAreaScale`. -/
theorem weightedArea_variedCarrier_prescribedAreaScale_sub
    (P : GraphPatch) {lam delta : ℝ} (hlam : 1 < lam)
    (hvalid : P.ValidAt P.compensationBump (P.prescribedAreaScale lam delta)) :
    WeightedArea lam
        (P.variedCarrier P.compensationBump (P.prescribedAreaScale lam delta)) -
      WeightedArea lam P.carrier = delta := by
  have hnew := P.weightedArea_variedCarrier (lam := lam)
    P.compensationBump_contDiff.continuous hvalid
  have hold := P.weightedArea_variedCarrier (lam := lam)
    P.compensationBump_contDiff.continuous
    (P.validAt_zero P.compensationBump)
  rw [P.intervalIntegral_verticalThickness
      P.compensationBump_contDiff.continuous (P.prescribedAreaScale lam delta),
    P.intervalIntegral_compensationBump] at hnew
  rw [P.intervalIntegral_verticalThickness
      P.compensationBump_contDiff.continuous 0] at hold
  rw [P.variedCarrier_zero] at hold
  rw [hnew, hold]
  rw [prescribedAreaScale]
  field_simp [OccupiedSide.areaSign_ne_zero,
    DensityZone.weight_ne_zero hlam]
  ring

/-- Every valid varied graph ribbon is bounded by its fixed finite box. -/
theorem isBounded_variedCarrier (P : GraphPatch) {v : ℝ → ℝ} {t : ℝ}
    (hvalid : P.ValidAt v t) :
    Bornology.IsBounded (P.variedCarrier v t) := by
  apply ((isCompact_Icc.prod isCompact_Icc).isBounded).subset
  exact (P.variedCarrier_subset_box hvalid).trans
    (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)

/-- The protected graph tube is closed. -/
theorem isClosed_closedGraphTube (P : GraphPatch) (T : P.Tube) :
    IsClosed (P.closedGraphTube T) := by
  unfold closedGraphTube
  exact isClosed_Icc.preimage continuous_fst |>.inter <|
    isClosed_le
      ((continuous_snd.sub (P.graph_contDiff.continuous.comp continuous_fst)).abs)
      continuous_const

/-- The normalized bump has one finite positive global absolute bound. -/
theorem exists_compensationBump_bound (P : GraphPatch) :
    ∃ M > 0, ∀ x, |P.compensationBump x| ≤ M := by
  have hcompact : HasCompactSupport P.compensationBump :=
    P.compensationKernel.hasCompactSupport_normed
  obtain ⟨M0, hM0⟩ :=
    P.compensationBump_contDiff.continuous.bounded_above_of_compact_support
      hcompact
  refine ⟨max 1 M0, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  rw [← Real.norm_eq_abs]
  exact (hM0 x).trans (le_max_right _ _)

/-- Compactness of the fixed patch interval gives a finite global bound for
the derivative of the normalized compensation bump on that interval. -/
theorem exists_compensationBump_deriv_bound (P : GraphPatch) :
    ∃ D ≥ 0, ∀ x ∈ Icc P.a P.b, |deriv P.compensationBump x| ≤ D := by
  have hcontinuous : Continuous (fun x : ℝ => |deriv P.compensationBump x|) :=
    (P.compensationBump_contDiff.continuous_deriv (by simp)).abs
  obtain ⟨D0, hD0⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontinuous.continuousOn)
  refine ⟨max 0 D0, le_max_left _ _, ?_⟩
  intro x hx
  exact (hD0 _ (mem_image_of_mem _ hx)).trans (le_max_right _ _)

/-- A feasible normalized bump changes the literal weighted graph functional
by at most a finite constant times its scalar amplitude. -/
theorem abs_weightedGraphLength_compensationBump_sub_le
    (P : GraphPatch) (T : P.Tube) {lam t D : ℝ}
    (hlam : 1 < lam)
    (_hD : 0 ≤ D)
    (hDbound : ∀ x ∈ Icc P.a P.b, |deriv P.compensationBump x| ≤ D)
    (hshift : ∀ x ∈ Ioc P.a P.b,
      |t * P.compensationBump x| < T.radius) :
    |weightedGraphLength lam P P.compensationBump t -
        weightedGraphLength lam P P.compensationBump 0| ≤
      P.zone.weight lam * D * (P.b - P.a) * |t| := by
  have hw : 0 < P.zone.weight lam := DensityZone.weight_pos hlam
  have hzoneT : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph P.compensationBump t x) :=
    P.variedGraph_in_zone_of_pointwise_mul_lt T hshift
  have hshiftZero : ∀ x ∈ Ioc P.a P.b,
      |(0 : ℝ) * P.compensationBump x| < T.radius := by
    intro x _hx
    simpa using T.radius_pos
  have hzoneZero : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph P.compensationBump 0 x) :=
    P.variedGraph_in_zone_of_pointwise_mul_lt T hshiftZero
  rw [weightedGraphLength_eq_weight lam P hzoneT,
    weightedGraphLength_eq_weight lam P hzoneZero, ← mul_sub, abs_mul,
    abs_of_pos hw]
  have hvariedT : ContDiff ℝ 1 (P.variedGraph P.compensationBump t) := by
    change ContDiff ℝ 1 (fun x =>
      P.graph x + t * P.compensationBump x)
    exact P.graph_contDiff.of_le (by norm_num) |>.add
      (contDiff_const.mul (P.compensationBump_contDiff.of_le (by simp)))
  have hvariedZero : ContDiff ℝ 1
      (P.variedGraph P.compensationBump 0) := by
    change ContDiff ℝ 1 (fun x =>
      P.graph x + 0 * P.compensationBump x)
    exact P.graph_contDiff.of_le (by norm_num) |>.add
      (contDiff_const.mul (P.compensationBump_contDiff.of_le (by simp)))
  have hspeedT : Continuous (fun x =>
      Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2)) :=
    (continuous_const.add
      ((hvariedT.continuous_deriv (by norm_num)).pow 2)).sqrt
  have hspeedZero : Continuous (fun x =>
      Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump 0) x) ^ 2)) :=
    (continuous_const.add
      ((hvariedZero.continuous_deriv (by norm_num)).pow 2)).sqrt
  rw [← intervalIntegral.integral_sub
    (hspeedT.intervalIntegrable P.a P.b)
    (hspeedZero.intervalIntegrable P.a P.b)]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := P.a) (b := P.b) (C := |t| * D)
    (f := fun x =>
      Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2) -
        Real.sqrt
          (1 + (deriv (P.variedGraph P.compensationBump 0) x) ^ 2))
    (fun x hx => by
      have hxIcc : x ∈ Icc P.a P.b := by
        have hxIoc : x ∈ Ioc P.a P.b := by
          simpa [Set.uIoc_of_le P.a_lt_b.le] using hx
        exact ⟨hxIoc.1.le, hxIoc.2⟩
      rw [Real.norm_eq_abs]
      refine (CMVRelaxation.abs_graphSpeed_sub_graphSpeed_le _ _).trans ?_
      rw [deriv_variedGraph P
          (P.compensationBump_contDiff.differentiable (by simp)) t x,
        deriv_variedGraph P
          (P.compensationBump_contDiff.differentiable (by simp)) 0 x,
        zero_mul, add_zero, add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_left (hDbound x hxIcc) (abs_nonneg t))
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr P.a_lt_b.le)] at hbound
  calc
    P.zone.weight lam *
        |∫ (x : ℝ) in P.a..P.b,
          (Real.sqrt
              (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2) -
            Real.sqrt
              (1 + (deriv (P.variedGraph P.compensationBump 0) x) ^ 2))| ≤
        P.zone.weight lam * ((|t| * D) * (P.b - P.a)) :=
      mul_le_mul_of_nonneg_left hbound hw.le
    _ = P.zone.weight lam * D * (P.b - P.a) * |t| := by ring

end CMVTwoPatchGraphVariation.GraphPatch


open CMVTwoPatchGraphVariation
namespace CMVRelaxation.RegularTraceCornerComparison

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

/-- A remote compensation graph belonging to the unchanged representative.
The local carrier identity and graph-frontier inclusion expose the genuine
source geometry.  Separation from the contact is derived from closedness and
`junction_not_mem_tube`; no competitor or area correction is a field. -/
structure RemoteCompensationPatch
    (A : RegularCornerChartApplicability C) where
  patch : GraphPatch
  tube : patch.Tube
  junction_not_mem_tube : C.junction ∉ patch.closedGraphTube tube
  representative_local :
    ∀ p ∈ patch.graphTube tube,
      (p ∈ C.representative ↔ p ∈ patch.carrier)
  graph_frontier :
    ∀ x ∈ Ioo patch.a patch.b,
      (x, patch.graph x) ∈ frontier C.representative

namespace RemoteCompensationPatch

variable (R : RemoteCompensationPatch A)

/-- A fixed positive source radius separates all sufficiently small contact
windows from the remote compensation tube. -/
theorem exists_disjoint_window_radius :
    ∃ rho > 0, ∀ r, 0 < r → r < rho →
      2 * r < A.localRadius ∧ Disjoint (A.window r)
        (R.patch.closedGraphTube R.tube) := by
  have hopen : IsOpen ((R.patch.closedGraphTube R.tube)ᶜ) :=
    R.patch.isClosed_closedGraphTube R.tube |>.isOpen_compl
  have hj : C.junction ∈ (R.patch.closedGraphTube R.tube)ᶜ :=
    R.junction_not_mem_tube
  rcases Metric.isOpen_iff.mp hopen C.junction hj with ⟨eps, heps, hball⟩
  let rho := min (A.localRadius / 4)
    (eps / (8 * A.coordinateBound))
  have hrho : 0 < rho := lt_min (div_pos A.localRadius_pos (by norm_num))
    (div_pos heps (mul_pos (by norm_num) A.coordinateBound_pos))
  refine ⟨rho, hrho, ?_⟩
  intro r hr hrrho
  have hrlocal : r < A.localRadius / 4 :=
    hrrho.trans_le (min_le_left _ _)
  have hreps : r < eps / (8 * A.coordinateBound) :=
    hrrho.trans_le (min_le_right _ _)
  have hlocal : 2 * r < A.localRadius := by linarith
  refine ⟨hlocal, ?_⟩
  rw [Set.disjoint_left]
  intro p hpWindow hpTube
  have hpSquare := A.window_subset_localizationSquare hlocal hpWindow
  exact (hball (by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    rcases hpSquare with ⟨hx, hy⟩
    have hxabs : |p.1 - C.junction.1| ≤ 4 * A.coordinateBound * r :=
      (abs_le).2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hyabs : |p.2 - C.junction.2| ≤ 4 * A.coordinateBound * r :=
      (abs_le).2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hscale : 4 * A.coordinateBound * r < eps := by
      have hden : 0 < 8 * A.coordinateBound :=
        mul_pos (by norm_num) A.coordinateBound_pos
      have := (lt_div_iff₀ hden).mp hreps
      nlinarith [A.coordinateBound_pos]
    exact max_lt (hxabs.trans_lt hscale) (hyabs.trans_lt hscale))) hpTube

/-- Actual signed area defect left by the contact extension. -/
def extensionAreaDefect (_R : RemoteCompensationPatch A) (lam r : ℝ) : ℝ :=
  WeightedArea lam C.representative -
    WeightedArea lam (A.extensionCompetitor r)
def correctionScale (lam r : ℝ) : ℝ :=
  R.patch.prescribedAreaScale lam (R.extensionAreaDefect lam r)

/-- The exact-area family: first perform the contact extension, then toggle the
old and corrected remote graph ribbons on that same carrier. -/
def exactAreaExtension (lam r : ℝ) : Set PlanePoint :=
  replaceBySymmDiff (A.extensionCompetitor r) R.patch.carrier
    (R.patch.variedCarrier R.patch.compensationBump (R.correctionScale lam r))

/-- Away from the contact window, the extension still has the unchanged
representative's membership label. -/
theorem extensionCompetitor_local_eq_patch_of_disjoint {r : ℝ}
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube)) :
    ∀ p ∈ R.patch.graphTube R.tube,
      (p ∈ A.extensionCompetitor r ↔ p ∈ R.patch.carrier) := by
  intro p hpTube
  have hpClosed := R.patch.graphTube_subset_closedGraphTube R.tube hpTube
  have hpNotWindow : p ∉ A.window r := fun hpWindow =>
    Set.disjoint_left.1 hdisjoint hpWindow hpClosed
  have hdiff := localizedCompetitor_symmDiff_subset_window
    C.representative_isOpen (A.isOpen_extensionLocalModel r)
      (A.isClosed_window r)
  have hsame : p ∈ A.extensionCompetitor r ↔ p ∈ C.representative := by
    by_contra hne
    have hpDiff : p ∈ A.extensionCompetitor r ∆ C.representative := by
      simp only [Set.mem_symmDiff]
      tauto
    exact hpNotWindow (hdiff hpDiff)
  exact hsame.trans (R.representative_local p hpTube)

/-- At every feasible separated scale, the compensated family has exactly the
unchanged representative's literal weighted area. -/
theorem exactAreaExtension_weightedArea
    {lam r : ℝ} (hlam : 1 < lam)
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| < R.tube.radius) :
    WeightedArea lam (R.exactAreaExtension lam r) =
      WeightedArea lam C.representative := by
  have hvalid := R.patch.validAt_of_pointwise_mul_lt R.tube hshift
  have hchange :
      R.patch.carrier ∆
          R.patch.variedCarrier R.patch.compensationBump (R.correctionScale lam r) ⊆
        R.patch.graphTube R.tube := by
    rw [symmDiff_comm]
    exact R.patch.variedCarrier_symmDiff_subset_graphTube R.tube hshift
  have hsub := weightedArea_replaceBySymmDiff_sub
    (lam := lam)
    (A.isOpen_extensionCompetitor r).measurableSet
    R.patch.measurableSet_carrier
    (R.patch.measurableSet_variedCarrier
      R.patch.compensationBump_contDiff.continuous.measurable
      (R.correctionScale lam r))
    (A.isBounded_extensionCompetitor r)
    (by
      simpa only [R.patch.variedCarrier_zero] using
        R.patch.isBounded_variedCarrier
          (R.patch.validAt_zero R.patch.compensationBump))
    (R.patch.isBounded_variedCarrier hvalid)
    hchange (R.extensionCompetitor_local_eq_patch_of_disjoint hdisjoint)
  have hpatch := R.patch.weightedArea_variedCarrier_prescribedAreaScale_sub
    hlam hvalid
  change WeightedArea lam (R.exactAreaExtension lam r) -
      WeightedArea lam (A.extensionCompetitor r) = _ at hsub
  change WeightedArea lam
      (R.patch.variedCarrier R.patch.compensationBump (R.correctionScale lam r)) -
        WeightedArea lam R.patch.carrier = R.extensionAreaDefect lam r at hpatch
  rw [hpatch] at hsub
  unfold extensionAreaDefect at hsub
  linarith

/-- The forced compensation scale inherits the extension's quadratic area
bound, with the actual local density price in the denominator. -/
theorem abs_correctionScale_le {lam r : ℝ} (hlam : 1 < lam)
    (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    |R.correctionScale lam r| ≤
      (4 * lam * (4 * A.coordinateBound) ^ 2 * r ^ 2) /
        R.patch.zone.weight lam := by
  have hweight : 0 < R.patch.zone.weight lam :=
    DensityZone.weight_pos hlam
  have hsign : |R.patch.side.areaSign| = (1 : ℝ) := by
    cases R.patch.side <;> simp [OccupiedSide.areaSign]
  have hdef :
      |R.extensionAreaDefect lam r| ≤
        4 * lam * (4 * A.coordinateBound) ^ 2 * r ^ 2 := by
    simpa only [extensionAreaDefect, abs_sub_comm] using
      A.extensionCompetitor_weightedArea_defect_le hlam.le hr hlocal
  rw [correctionScale, GraphPatch.prescribedAreaScale, abs_div, abs_mul,
    hsign, one_mul, abs_of_pos hweight]
  exact div_le_div_of_nonneg_right hdef hweight.le

/-- The exact correction amplitude tends to zero on positive contact scales;
this is derived from the actual quadratic area estimate. -/
theorem tendsto_correctionScale_zero {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (fun r => R.correctionScale lam r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K := 4 * lam * (4 * A.coordinateBound) ^ 2
  let w := R.patch.zone.weight lam
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hw : 0 < w := DensityZone.weight_pos hlam
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < A.localRadius :=
    ((eventually_lt_nhds (half_pos A.localRadius_pos)).filter_mono
      inf_le_left).mono (fun _ hr => by linarith)
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |R.correctionScale lam r| ≤ K * r ^ 2 / w := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrLocal
    simpa only [K, w, mul_assoc] using
      R.abs_correctionScale_le hlam hr hrLocal
  have hupper : Tendsto (fun r : ℝ => K * r ^ 2 / w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hKc : Tendsto (fun _ : ℝ => K) (𝓝 (0 : ℝ)) (𝓝 K) :=
      tendsto_const_nhds
    have hid : Tendsto (fun r : ℝ => r) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    have hfull : Tendsto (fun r : ℝ => K * r ^ 2 / w)
        (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div] using
        ((hKc.mul (hid.pow 2)).div_const w)
    exact hfull.mono_left nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero'
      (Filter.Eventually.of_forall fun r => abs_nonneg (R.correctionScale lam r))
      hbound hupper

/-- The two alteration neighborhoods and all compensation feasibility
conditions hold simultaneously at every sufficiently small positive scale.
The output includes measurability, boundedness, exact area, and literal
symmetric-difference localization of both stages. -/
theorem eventually_exactAreaExtension_feasible {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      2 * r < A.localRadius ∧
      Disjoint (A.window r) (R.patch.closedGraphTube R.tube) ∧
      (∀ x ∈ Ioc R.patch.a R.patch.b,
        |R.correctionScale lam r * R.patch.compensationBump x| <
          R.tube.radius) ∧
      R.patch.ValidAt R.patch.compensationBump (R.correctionScale lam r) ∧
      MeasurableSet (R.exactAreaExtension lam r) ∧
      Bornology.IsBounded (R.exactAreaExtension lam r) ∧
      WeightedArea lam (R.exactAreaExtension lam r) =
        WeightedArea lam C.representative ∧
      A.extensionCompetitor r ∆ C.representative ⊆ A.window r ∧
      R.exactAreaExtension lam r ∆ A.extensionCompetitor r ⊆
        R.patch.closedGraphTube R.tube := by
  obtain ⟨rho, hrho, hremote⟩ := R.exists_disjoint_window_radius
  obtain ⟨M, hM, hMbound⟩ := R.patch.exists_compensationBump_bound
  have hscale := R.tendsto_correctionScale_zero hlam
  have hscaleSmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |R.correctionScale lam r| < R.tube.radius / M := by
    have heps : 0 < R.tube.radius / M := div_pos R.tube.radius_pos hM
    have hball := hscale.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
    filter_upwards [hball] with r hr
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hr
  have hrhoEventually : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < rho :=
    (eventually_lt_nhds hrho).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hrhoEventually, hscaleSmall] with
      r hr hrSmall hscaleBound
  rcases hremote r hr hrSmall with ⟨hlocal, hdisjoint⟩
  have hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| < R.tube.radius := by
    intro x _hx
    rw [abs_mul]
    calc
      |R.correctionScale lam r| * |R.patch.compensationBump x| ≤
          |R.correctionScale lam r| * M :=
        mul_le_mul_of_nonneg_left (hMbound x)
          (abs_nonneg (R.correctionScale lam r))
      _ < (R.tube.radius / M) * M :=
        mul_lt_mul_of_pos_right hscaleBound hM
      _ = R.tube.radius := by field_simp [ne_of_gt hM]
  have hvalid := R.patch.validAt_of_pointwise_mul_lt R.tube hshift
  have hchange :
      R.patch.carrier ∆
          R.patch.variedCarrier R.patch.compensationBump (R.correctionScale lam r) ⊆
        R.patch.closedGraphTube R.tube := by
    rw [symmDiff_comm]
    exact R.patch.variedCarrier_symmDiff_subset_closedGraphTube R.tube hshift
  have hmeas : MeasurableSet (R.exactAreaExtension lam r) :=
    measurableSet_replaceBySymmDiff
      (A.isOpen_extensionCompetitor r).measurableSet
      R.patch.measurableSet_carrier
      (R.patch.measurableSet_variedCarrier
        R.patch.compensationBump_contDiff.continuous.measurable
        (R.correctionScale lam r))
  have holdBounded : Bornology.IsBounded R.patch.carrier := by
    simpa only [R.patch.variedCarrier_zero] using
      R.patch.isBounded_variedCarrier
        (R.patch.validAt_zero R.patch.compensationBump)
  have hnewBounded : Bornology.IsBounded
      (R.patch.variedCarrier R.patch.compensationBump (R.correctionScale lam r)) :=
    R.patch.isBounded_variedCarrier hvalid
  have hbounded : Bornology.IsBounded (R.exactAreaExtension lam r) :=
    isBounded_replaceBySymmDiff
      (A.isBounded_extensionCompetitor r) holdBounded hnewBounded
  have hcontact :
      A.extensionCompetitor r ∆ C.representative ⊆ A.window r :=
    localizedCompetitor_symmDiff_subset_window
      C.representative_isOpen (A.isOpen_extensionLocalModel r)
        (A.isClosed_window r)
  have hcomp :
      R.exactAreaExtension lam r ∆ A.extensionCompetitor r ⊆
        R.patch.closedGraphTube R.tube := by
    rw [exactAreaExtension, replaceBySymmDiff_symmDiff_ambient]
    exact hchange
  exact ⟨hlocal, hdisjoint, hshift, hvalid, hmeas, hbounded,
    R.exactAreaExtension_weightedArea hlam hdisjoint hshift,
    hcontact, hcomp⟩

/-- The remote compensation's literal weighted graph-length change is
quadratic in the contact scale.  The finite coefficient is constructed from
the actual density price, the fixed patch width, the bump derivative bound,
and the extension's signed-area bound. -/
theorem eventually_compensationWeightedGraphLength_sub_le_quadratic
    {lam : ℝ} (hlam : 1 < lam) :
    ∃ Q ≥ 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |weightedGraphLength lam R.patch R.patch.compensationBump
          (R.correctionScale lam r) -
        weightedGraphLength lam R.patch R.patch.compensationBump 0| ≤
          Q * r ^ 2 := by
  obtain ⟨D, hD, hDbound⟩ := R.patch.exists_compensationBump_deriv_bound
  let w := R.patch.zone.weight lam
  let K := 4 * lam * (4 * A.coordinateBound) ^ 2
  let L := w * D * (R.patch.b - R.patch.a)
  let Q := L * K / w
  have hw : 0 < w := DensityZone.weight_pos hlam
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L, w]
    exact mul_nonneg
      (mul_nonneg (DensityZone.weight_pos hlam).le hD)
      (sub_nonneg.mpr R.patch.a_lt_b.le)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact div_nonneg (mul_nonneg hL hK) hw.le
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    R.eventually_exactAreaExtension_feasible hlam] with r hr hfeasible
  rcases hfeasible with
    ⟨hlocal, _hdisjoint, hshift, _hvalid, _hmeas, _hbounded,
      _harea, _hcontact, _hcomp⟩
  have hlength :=
    R.patch.abs_weightedGraphLength_compensationBump_sub_le
      R.tube hlam hD hDbound hshift
  have hscale := R.abs_correctionScale_le hlam hr hlocal
  calc
    |weightedGraphLength lam R.patch R.patch.compensationBump
          (R.correctionScale lam r) -
        weightedGraphLength lam R.patch R.patch.compensationBump 0| ≤
        L * |R.correctionScale lam r| := by
      simpa only [L, w] using hlength
    _ ≤ L * (K * r ^ 2 / w) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [K, w, mul_assoc] using hscale) hL
    _ = Q * r ^ 2 := by
      dsimp [Q]
      field_simp [ne_of_gt hw]

end RemoteCompensationPatch

end CMVRelaxation.RegularTraceCornerComparison
