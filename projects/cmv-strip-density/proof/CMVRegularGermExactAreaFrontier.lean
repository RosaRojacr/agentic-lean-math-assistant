import CMVRegularGermExactAreaCompensation

/-!
# Complete-frontier assembly for exact-area regular-germ extensions

The normalized compensation bump has compact horizontal support.  A graph-shear
window enclosing that support has its complete cutting frontier inside the
original protected graph tube.  On a derived collar, the unchanged carrier and
the varied occupied graph side agree.  This identifies the literal
symmetric-difference correction with a collar-compatible splice and gives an
exact complete-frontier cost decomposition.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

open CMVTwoPatchGraphVariation

namespace CMVTwoPatchGraphVariation.GraphPatch

/-- Left endpoint of the closed support interval of the canonical bump. -/
def compensationSupportLeft (P : GraphPatch) : ℝ :=
  (3 * P.a + P.b) / 4

/-- Right endpoint of the closed support interval of the canonical bump. -/
def compensationSupportRight (P : GraphPatch) : ℝ :=
  (P.a + 3 * P.b) / 4

/-- Left edge of the wider compensation splice window. -/
def compensationWindowLeft (P : GraphPatch) : ℝ :=
  (7 * P.a + P.b) / 8

/-- Right edge of the wider compensation splice window. -/
def compensationWindowRight (P : GraphPatch) : ℝ :=
  (P.a + 7 * P.b) / 8

lemma compensation_horizontal_order (P : GraphPatch) :
    P.a < P.compensationWindowLeft ∧
      P.compensationWindowLeft < P.compensationSupportLeft ∧
      P.compensationSupportLeft < P.compensationSupportRight ∧
      P.compensationSupportRight < P.compensationWindowRight ∧
      P.compensationWindowRight < P.b := by
  unfold compensationWindowLeft compensationSupportLeft
    compensationSupportRight compensationWindowRight
  constructor
  · linarith [P.a_lt_b]
  constructor
  · linarith [P.a_lt_b]
  constructor
  · linarith [P.a_lt_b]
  constructor <;> linarith [P.a_lt_b]

/-- The canonical bump vanishes outside its explicit closed support core. -/
theorem compensationBump_eq_zero_of_not_mem_supportCore
    (P : GraphPatch) {x : ℝ}
    (hx : x ∉ Icc P.compensationSupportLeft P.compensationSupportRight) :
    P.compensationBump x = 0 := by
  by_contra hne
  apply hx
  have hts : x ∈ tsupport P.compensationBump :=
    subset_tsupport P.compensationBump hne
  rw [compensationBump, P.compensationKernel.tsupport_normed_eq] at hts
  rw [mem_closedBall, Real.dist_eq, abs_le] at hts
  dsimp [compensationKernel] at hts
  change P.compensationSupportLeft ≤ x ∧
    x ≤ P.compensationSupportRight
  unfold compensationSupportLeft compensationSupportRight
  constructor <;> linarith [hts.1, hts.2]

/-- Triangular graph shear sending the horizontal axis to the old graph. -/
def compensationGraphShear (P : GraphPatch) : PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1, P.graph q.1 + q.2)
  invFun p := (p.1, p.2 - P.graph p.1)
  left_inv q := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    exact continuous_fst.prodMk
      ((P.graph_contDiff.continuous.comp continuous_fst).add continuous_snd)
  continuous_invFun := by
    exact continuous_fst.prodMk
      (continuous_snd.sub (P.graph_contDiff.continuous.comp continuous_fst))

@[simp] theorem compensationGraphShear_apply (P : GraphPatch) (q : PlanePoint) :
    P.compensationGraphShear q = (q.1, P.graph q.1 + q.2) := rfl

/-- Closed graph-shear window enclosing the complete bump support. -/
def compensationWindow (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  P.compensationGraphShear ''
    CMVRelaxation.closedCutRectangle P.compensationWindowLeft
      P.compensationWindowRight (-T.radius / 2) (T.radius / 2)

/-- Open collar around the compensation-window frontier.  On its vertical
parts the bump is identically zero; on its horizontal parts both old and new
occupied-side labels are forced to agree. -/
def compensationCollar (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  P.openGraphTube T ∩
    ({p | p.1 ∉ Icc P.compensationSupportLeft P.compensationSupportRight} ∪
      {p | T.radius / 4 < |p.2 - P.graph p.1|})

lemma isClosed_compensationWindow (P : GraphPatch) (T : P.Tube) :
    IsClosed (P.compensationWindow T) := by
  exact P.compensationGraphShear.isClosedMap _
    (isClosed_Icc.prod isClosed_Icc)

lemma isBounded_compensationWindow (P : GraphPatch) (T : P.Tube) :
    Bornology.IsBounded (P.compensationWindow T) := by
  exact ((isCompact_Icc.prod isCompact_Icc).image
    P.compensationGraphShear.continuous).isBounded

lemma closure_interior_compensationWindow (P : GraphPatch) (T : P.Tube) :
    closure (interior (P.compensationWindow T)) = P.compensationWindow T := by
  have hhorizontal :
      P.compensationWindowLeft < P.compensationWindowRight :=
    P.compensation_horizontal_order.2.1.trans <|
      P.compensation_horizontal_order.2.2.1.trans
        P.compensation_horizontal_order.2.2.2.1
  rw [compensationWindow, ← P.compensationGraphShear.image_interior,
    ← P.compensationGraphShear.image_closure]
  exact congrArg (fun S => P.compensationGraphShear '' S)
    (CMVRelaxation.closure_interior_closedCutRectangle hhorizontal
      (by linarith [T.radius_pos]))

lemma compensationWindow_subset_openGraphTube (P : GraphPatch) (T : P.Tube) :
    P.compensationWindow T ⊆ P.openGraphTube T := by
  rintro _ ⟨q, hq, rfl⟩
  rcases hq with ⟨hx, hy⟩
  change q.1 ∈ Ioo P.a P.b ∧
    |P.graph q.1 + q.2 - P.graph q.1| < T.radius
  have hord := P.compensation_horizontal_order
  constructor
  · exact ⟨hord.1.trans_le hx.1,
      hx.2.trans_lt hord.2.2.2.2⟩
  · rw [add_sub_cancel_left, abs_lt]
    constructor <;> linarith [hy.1, hy.2, T.radius_pos]

lemma isOpen_compensationCollar (P : GraphPatch) (T : P.Tube) :
    IsOpen (P.compensationCollar T) := by
  apply P.isOpen_openGraphTube T |>.inter
  apply (isClosed_Icc.preimage continuous_fst).isOpen_compl.union
  exact isOpen_lt continuous_const
    ((continuous_snd.sub
      (P.graph_contDiff.continuous.comp continuous_fst)).abs)

/-- The whole cutting frontier lies in the derived agreement collar. -/
theorem frontier_compensationWindow_subset_collar
    (P : GraphPatch) (T : P.Tube) :
    frontier (P.compensationWindow T) ⊆ P.compensationCollar T := by
  rw [compensationWindow, ← P.compensationGraphShear.image_frontier]
  rintro _ ⟨q, hq, rfl⟩
  have hqClosed : q ∈
      CMVRelaxation.closedCutRectangle P.compensationWindowLeft
        P.compensationWindowRight (-T.radius / 2) (T.radius / 2) :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset hq
  have hopen := P.compensationWindow_subset_openGraphTube T
    ⟨q, hqClosed, rfl⟩
  refine ⟨hopen, ?_⟩
  have hhorizontal :
      P.compensationWindowLeft < P.compensationWindowRight :=
    P.compensation_horizontal_order.2.1.trans <|
      P.compensation_horizontal_order.2.2.1.trans
        P.compensation_horizontal_order.2.2.2.1
  have hfaces := CMVRelaxation.frontier_closedCutRectangle_subset_lines
    hhorizontal (by linarith [T.radius_pos]) hq
  rcases hfaces with ((hleft | hright) | hlower) | hupper
  · left
    change q.1 = P.compensationWindowLeft at hleft
    change q.1 ∉ Icc P.compensationSupportLeft
      P.compensationSupportRight
    rw [hleft]
    have hord := P.compensation_horizontal_order
    exact fun h => (not_le_of_gt hord.2.1) h.1
  · left
    change q.1 = P.compensationWindowRight at hright
    change q.1 ∉ Icc P.compensationSupportLeft
      P.compensationSupportRight
    rw [hright]
    have hord := P.compensation_horizontal_order
    exact fun h => (not_le_of_gt hord.2.2.2.1) h.2
  · right
    change q.2 = -T.radius / 2 at hlower
    change T.radius / 4 <
      |P.graph q.1 + q.2 - P.graph q.1|
    rw [hlower]
    simp only [add_sub_cancel_left, abs_neg, abs_div, abs_of_pos T.radius_pos]
    linarith [T.radius_pos]
  · right
    change q.2 = T.radius / 2 at hupper
    change T.radius / 4 <
      |P.graph q.1 + q.2 - P.graph q.1|
    rw [hupper]
    simp only [add_sub_cancel_left, abs_div, abs_of_pos T.radius_pos]
    linarith [T.radius_pos]

/-- Every changed point of a sufficiently small normalized bump lies in the
strictly wider graph-shear compensation window. -/
theorem carrier_symmDiff_varied_subset_compensationWindow
    (P : GraphPatch) (T : P.Tube) {t : ℝ}
    (hshift : ∀ x ∈ Ioc P.a P.b,
      |t * P.compensationBump x| < T.radius / 4) :
    P.carrier ∆ P.variedCarrier P.compensationBump t ⊆
      P.compensationWindow T := by
  intro p hp
  have hbump : P.compensationBump p.1 ≠ 0 := by
    intro hbump
    have hgraph : P.variedGraph P.compensationBump t p.1 = P.graph p.1 := by
      simp [GraphPatch.variedGraph, hbump]
    cases hside : P.side with
    | below =>
        simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside,
          Set.mem_symmDiff, regionBetween, Set.mem_ofPred_eq, mem_Ioo] at hp
        simp only [hgraph] at hp
        rcases hp with hp | hp
        · exact hp.2 ⟨hp.1.1, hp.1.2.1, hp.1.2.2⟩
        · exact hp.2 ⟨hp.1.1, hp.1.2.1, hp.1.2.2⟩
    | above =>
        simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside,
          Set.mem_symmDiff, regionBetween, Set.mem_ofPred_eq, mem_Ioo] at hp
        simp only [hgraph] at hp
        rcases hp with hp | hp
        · exact hp.2 ⟨hp.1.1, hp.1.2.1, hp.1.2.2⟩
        · exact hp.2 ⟨hp.1.1, hp.1.2.1, hp.1.2.2⟩
  have hcore : p.1 ∈ Icc P.compensationSupportLeft
      P.compensationSupportRight := by
    by_contra hout
    exact hbump (P.compensationBump_eq_zero_of_not_mem_supportCore hout)
  have hxPatch : p.1 ∈ Ioc P.a P.b := by
    have hord := P.compensation_horizontal_order
    exact ⟨hord.1.trans_le (hord.2.1.le.trans hcore.1),
      hcore.2.trans (hord.2.2.2.1.trans hord.2.2.2.2).le⟩
  let d := t * P.compensationBump p.1
  have hdabs : |d| < T.radius / 4 := hshift p.1 hxPatch
  have hzabs : |p.2 - P.graph p.1| ≤ |d| := by
    cases hside : P.side with
    | below =>
        simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside,
          Set.mem_symmDiff, regionBetween, Set.mem_ofPred_eq, mem_Ioo,
          GraphPatch.variedGraph] at hp
        rcases hp with hold | hnew
        · have hnewle : P.graph p.1 + d ≤ p.2 := by
            apply le_of_not_gt
            intro hlt
            exact hold.2 ⟨hold.1.1, hold.1.2.1, hlt⟩
          rw [abs_of_nonpos (sub_nonpos.mpr hold.1.2.2.le)]
          nlinarith [neg_le_abs d]
        · have holdle : P.graph p.1 ≤ p.2 := by
            apply le_of_not_gt
            intro hlt
            exact hnew.2 ⟨hnew.1.1, hnew.1.2.1, hlt⟩
          rw [abs_of_nonneg (sub_nonneg.mpr holdle)]
          nlinarith [le_abs_self d]
    | above =>
        simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside,
          Set.mem_symmDiff, regionBetween, Set.mem_ofPred_eq, mem_Ioo,
          GraphPatch.variedGraph] at hp
        rcases hp with hold | hnew
        · have hnewle : p.2 ≤ P.graph p.1 + d := by
            apply le_of_not_gt
            intro hlt
            exact hold.2 ⟨hold.1.1, hlt, hold.1.2.2⟩
          rw [abs_of_nonneg (sub_nonneg.mpr hold.1.2.1.le)]
          nlinarith [le_abs_self d]
        · have holdle : p.2 ≤ P.graph p.1 := by
            apply le_of_not_gt
            intro hlt
            exact hnew.2 ⟨hnew.1.1, hlt, hnew.1.2.2⟩
          rw [abs_of_nonpos (sub_nonpos.mpr holdle)]
          nlinarith [neg_le_abs d]
  refine ⟨(p.1, p.2 - P.graph p.1), ?_, ?_⟩
  · constructor
    · have hord := P.compensation_horizontal_order
      exact ⟨hord.2.1.le.trans hcore.1,
        hcore.2.trans hord.2.2.2.1.le⟩
    · change -T.radius / 2 ≤ p.2 - P.graph p.1 ∧
        p.2 - P.graph p.1 ≤ T.radius / 2
      have hzrange := abs_le.mp hzabs
      constructor <;> nlinarith [hzrange.1, hzrange.2, hdabs, T.radius_pos]
  · ext <;> simp

theorem frontier_occupiedGraphDomain_inter_compensationWindow
    (P : GraphPatch) (T : P.Tube) {v : ℝ → ℝ} {t : ℝ}
    (hg : Continuous (P.variedGraph v t))
    (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius / 4) :
    frontier (P.occupiedGraphDomain (P.variedGraph v t)) ∩
        interior (P.compensationWindow T) =
      (fun x : ℝ => (x, P.variedGraph v t x)) ''
        Ioo P.compensationWindowLeft P.compensationWindowRight := by
  rw [P.frontier_occupiedGraphDomain hg]
  ext p
  constructor
  · rintro ⟨⟨x, _hx, rfl⟩, hpW⟩
    rw [compensationWindow, ← P.compensationGraphShear.image_interior] at hpW
    rcases hpW with ⟨q, hq, hqeq⟩
    have hq' :
        q ∈ Ioo P.compensationWindowLeft P.compensationWindowRight ×ˢ
          Ioo (-T.radius / 2) (T.radius / 2) := by
      simpa only [CMVRelaxation.closedCutRectangle, interior_prod_eq,
        interior_Icc] using hq
    have hqx : q.1 = x := by
      simpa only [compensationGraphShear_apply] using congrArg Prod.fst hqeq
    exact ⟨x, by simpa only [← hqx] using hq'.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact ⟨x, mem_univ x, rfl⟩
    · rw [compensationWindow, ← P.compensationGraphShear.image_interior]
      refine ⟨(x, t * v x), ?_, ?_⟩
      · have hord := P.compensation_horizontal_order
        have hxab : x ∈ Ioc P.a P.b :=
          ⟨hord.1.trans hx.1, hx.2.le.trans hord.2.2.2.2.le⟩
        have hs := hshift x hxab
        have hs' : -T.radius / 2 < t * v x ∧ t * v x < T.radius / 2 := by
          have hsides := abs_lt.mp hs
          constructor <;> linarith [T.radius_pos]
        simpa only [CMVRelaxation.closedCutRectangle, interior_prod_eq,
          interior_Icc, mem_prod] using ⟨hx, hs'⟩
      · ext <;> simp [GraphPatch.variedGraph]


/-- Weighted graph arclength over the compensation window's horizontal span. -/
def compensationWindowWeightedGraphLength
    (lam : ℝ) (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  P.zone.weight lam *
    ∫ x in P.compensationWindowLeft..P.compensationWindowRight,
      Real.sqrt (1 + (deriv (P.variedGraph v t) x) ^ 2)

theorem smoothCostOn_occupiedGraphDomain_compensationWindow
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hg : ContDiff ℝ 1 (P.variedGraph v t))
    (hzone : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph v t x))
    (hshift : ∀ x ∈ Ioc P.a P.b, |t * v x| < T.radius / 4) :
    CMVRelaxation.smoothCostOn lam
        (P.occupiedGraphDomain (P.variedGraph v t))
        (interior (P.compensationWindow T)) =
      ENNReal.ofReal (P.compensationWindowWeightedGraphLength lam v t) := by
  rw [CMVRelaxation.smoothCostOn_eq_weightedTraceCost_frontier_inter
    lam _ measurableSet_interior]
  rw [P.frontier_occupiedGraphDomain_inter_compensationWindow T
    hg.continuous hshift]
  rw [CMVRelaxation.weightedTraceCost_graph_image_eq_const_mul_setLIntegral
    lam (P.zone.weight lam) hg measurableSet_Ioo]
  · unfold compensationWindowWeightedGraphLength
    have hspeed : Continuous (fun x : ℝ =>
        Real.sqrt (1 + (deriv (P.variedGraph v t) x) ^ 2)) :=
      (continuous_const.add ((hg.continuous_deriv (by norm_num)).pow 2)).sqrt
    have hint : Integrable (fun x : ℝ =>
        Real.sqrt (1 + (deriv (P.variedGraph v t) x) ^ 2))
        (volume.restrict
          (Ioo P.compensationWindowLeft P.compensationWindowRight)) :=
      (hspeed.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)]
    rw [← ENNReal.ofReal_mul (DensityZone.weight_pos hlam).le]
    congr 1
    rw [intervalIntegral.integral_of_le
      (P.compensation_horizontal_order.2.1.trans
        (P.compensation_horizontal_order.2.2.1.trans
          P.compensation_horizontal_order.2.2.2.1)).le]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  · rintro _ ⟨x, hx, rfl⟩
    apply DensityZone.stripDensity_eq_weight
    apply hzone x
    have hord := P.compensation_horizontal_order
    exact ⟨hord.1.trans hx.1, hx.2.le.trans hord.2.2.2.2.le⟩


lemma deriv_compensation_variedGraph_eq_left
    (P : GraphPatch) (t x : ℝ) (hx : x ≤ P.compensationWindowLeft) :
    deriv (P.variedGraph P.compensationBump t) x = deriv P.graph x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [
    Iio_mem_nhds (hx.trans_lt P.compensation_horizontal_order.2.1)] with y hy
  rw [GraphPatch.variedGraph,
    P.compensationBump_eq_zero_of_not_mem_supportCore
      (fun h => (not_le_of_gt hy) h.1), mul_zero, add_zero]

lemma deriv_compensation_variedGraph_eq_right
    (P : GraphPatch) (t x : ℝ) (hx : P.compensationWindowRight ≤ x) :
    deriv (P.variedGraph P.compensationBump t) x = deriv P.graph x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [
    Ioi_mem_nhds (P.compensation_horizontal_order.2.2.2.1.trans_le hx)] with y hy
  rw [GraphPatch.variedGraph,
    P.compensationBump_eq_zero_of_not_mem_supportCore
      (fun h => (not_le_of_gt hy) h.2), mul_zero, add_zero]

theorem compensationWindowWeightedGraphLength_sub_eq_weightedGraphLength_sub
    {lam : ℝ} (P : GraphPatch) (T : P.Tube) {t : ℝ}
    (hshift : ∀ x ∈ Ioc P.a P.b,
      |t * P.compensationBump x| < T.radius / 4) :
    P.compensationWindowWeightedGraphLength lam P.compensationBump t -
        P.compensationWindowWeightedGraphLength lam P.compensationBump 0 =
      weightedGraphLength lam P P.compensationBump t -
        weightedGraphLength lam P P.compensationBump 0 := by
  have hzoneT := P.variedGraph_in_zone_of_pointwise_mul_lt T
    (fun x hx => (hshift x hx).trans (by linarith [T.radius_pos]))
  have hzoneZero := P.variedGraph_in_zone_of_pointwise_mul_lt T
    (v := P.compensationBump) (t := 0) (fun _ _ => by simp [T.radius_pos])
  rw [weightedGraphLength_eq_weight lam P hzoneT,
    weightedGraphLength_eq_weight lam P hzoneZero]
  unfold compensationWindowWeightedGraphLength
  let Ft : ℝ → ℝ := fun x =>
    Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2)
  let F0 : ℝ → ℝ := fun x =>
    Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump 0) x) ^ 2)
  have hgt : ContDiff ℝ 1 (P.variedGraph P.compensationBump t) := by
    change ContDiff ℝ 1 (fun x => P.graph x + t * P.compensationBump x)
    exact (P.graph_contDiff.of_le (by norm_num)).add
      (contDiff_const.mul (P.compensationBump_contDiff.of_le (by norm_num)))
  have hzeroGraph : P.variedGraph P.compensationBump 0 = P.graph := by
    funext x
    simp [GraphPatch.variedGraph]
  have hg0 : ContDiff ℝ 1 (P.variedGraph P.compensationBump 0) := by
    rw [hzeroGraph]
    exact P.graph_contDiff.of_le (by norm_num)
  have hFt : Continuous Ft :=
    (continuous_const.add ((hgt.continuous_deriv (by norm_num)).pow 2)).sqrt
  have hF0 : Continuous F0 :=
    (continuous_const.add ((hg0.continuous_deriv (by norm_num)).pow 2)).sqrt
  have hleft : ∫ x in P.a..P.compensationWindowLeft, Ft x =
      ∫ x in P.a..P.compensationWindowLeft, F0 x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have horder := P.compensation_horizontal_order.1
    rw [uIcc_of_le horder.le] at hx
    dsimp [Ft, F0]
    rw [P.deriv_compensation_variedGraph_eq_left t x hx.2,
      P.deriv_compensation_variedGraph_eq_left 0 x hx.2]
  have hright : ∫ x in P.compensationWindowRight..P.b, Ft x =
      ∫ x in P.compensationWindowRight..P.b, F0 x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have horder := P.compensation_horizontal_order.2.2.2.2
    rw [uIcc_of_le horder.le] at hx
    dsimp [Ft, F0]
    rw [P.deriv_compensation_variedGraph_eq_right t x hx.1,
      P.deriv_compensation_variedGraph_eq_right 0 x hx.1]
  have hFtA : IntervalIntegrable Ft volume P.a P.compensationWindowLeft :=
    hFt.intervalIntegrable _ _
  have hFtW : IntervalIntegrable Ft volume P.compensationWindowLeft
      P.compensationWindowRight := hFt.intervalIntegrable _ _
  have hFtB : IntervalIntegrable Ft volume P.compensationWindowRight P.b :=
    hFt.intervalIntegrable _ _
  have hF0A : IntervalIntegrable F0 volume P.a P.compensationWindowLeft :=
    hF0.intervalIntegrable _ _
  have hF0W : IntervalIntegrable F0 volume P.compensationWindowLeft
      P.compensationWindowRight := hF0.intervalIntegrable _ _
  have hF0B : IntervalIntegrable F0 volume P.compensationWindowRight P.b :=
    hF0.intervalIntegrable _ _
  have hFtAW := intervalIntegral.integral_add_adjacent_intervals hFtA hFtW
  have hFtAll := intervalIntegral.integral_add_adjacent_intervals
    (hFtA.trans hFtW) hFtB
  have hF0AW := intervalIntegral.integral_add_adjacent_intervals hF0A hF0W
  have hF0All := intervalIntegral.integral_add_adjacent_intervals
    (hF0A.trans hF0W) hF0B
  dsimp [Ft, F0] at hleft hright hFtAW hFtAll hF0AW hF0All ⊢
  rw [hzeroGraph] at *
  have hlength :
      (∫ x in P.compensationWindowLeft..P.compensationWindowRight,
          Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2)) -
        (∫ x in P.compensationWindowLeft..P.compensationWindowRight,
          Real.sqrt (1 + (deriv P.graph x) ^ 2)) =
      (∫ x in P.a..P.b,
          Real.sqrt (1 + (deriv (P.variedGraph P.compensationBump t) x) ^ 2)) -
        (∫ x in P.a..P.b, Real.sqrt (1 + (deriv P.graph x) ^ 2)) := by
    linarith [hleft, hright, hFtAW, hFtAll, hF0AW, hF0All]
  linear_combination (P.zone.weight lam) * hlength

lemma compensationWindowWeightedGraphLength_nonneg
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ) :
    0 ≤ P.compensationWindowWeightedGraphLength lam v t := by
  unfold compensationWindowWeightedGraphLength
  apply mul_nonneg (DensityZone.weight_pos hlam).le
  apply intervalIntegral.integral_nonneg
    (P.compensation_horizontal_order.2.1.trans
      (P.compensation_horizontal_order.2.2.1.trans
        P.compensation_horizontal_order.2.2.2.1)).le
  intro x _hx
  exact Real.sqrt_nonneg _
end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation.RegularTraceCornerComparison

open CMVTwoPatchGraphVariation
open RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

namespace RemoteCompensationPatch

variable (R : RemoteCompensationPatch A)

/-- On the compensation collar, the actual contact extension and the varied
occupied graph side agree.  This is derived from the unchanged representative,
disjointness of the two alteration neighborhoods, compact bump support, and
the strict displacement bound. -/
theorem extensionCompetitor_inter_compensationCollar_eq
    {r t : ℝ}
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |t * R.patch.compensationBump x| < R.tube.radius / 4) :
    A.extensionCompetitor r ∩ R.patch.compensationCollar R.tube =
      R.patch.occupiedGraphDomain
          (R.patch.variedGraph R.patch.compensationBump t) ∩
        R.patch.compensationCollar R.tube := by
  ext p
  by_cases hp : p ∈ R.patch.compensationCollar R.tube
  · simp only [mem_inter_iff, hp, and_true]
    rcases hp with ⟨hpTube, hpSector⟩
    have hpGraphTube := R.patch.openGraphTube_subset_graphTube R.tube hpTube
    have hambient := R.extensionCompetitor_local_eq_patch_of_disjoint
      hdisjoint p hpGraphTube
    have hold := R.patch.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
      R.tube hpGraphTube
    rw [hambient, hold]
    rcases hpSector with hout | hfar
    · change p.1 ∉ Icc R.patch.compensationSupportLeft
        R.patch.compensationSupportRight at hout
      have hzero :=
        R.patch.compensationBump_eq_zero_of_not_mem_supportCore hout
      cases hside : R.patch.side <;>
        simp [GraphPatch.occupiedGraphDomain, hside,
          GraphPatch.variedGraph, hzero]
    · change R.tube.radius / 4 < |p.2 - R.patch.graph p.1| at hfar
      have hx : p.1 ∈ Ioc R.patch.a R.patch.b :=
        ⟨hpTube.1.1, hpTube.1.2.le⟩
      have hsmall := abs_lt.mp (hshift p.1 hx)
      have hfar' := lt_abs.mp hfar
      cases hside : R.patch.side with
      | below =>
          simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq,
            GraphPatch.variedGraph]
          rcases hfar' with hneg | hpos <;> constructor <;> intro h <;> linarith
      | above =>
          simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq,
            GraphPatch.variedGraph]
          rcases hfar' with hneg | hpos <;> constructor <;> intro h <;> linarith
  · simp [hp]

/-- Under the same small-shift condition, the literal symmetric-difference
correction is exactly a collar-compatible splice through the graph-shear
window. -/
theorem exactAreaExtension_eq_spliceIn
    {lam r : ℝ}
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4) :
    R.exactAreaExtension lam r =
      spliceIn (A.extensionCompetitor r)
        (R.patch.occupiedGraphDomain
          (R.patch.variedGraph R.patch.compensationBump
            (R.correctionScale lam r)))
        (R.patch.compensationWindow R.tube) := by
  have hWTube :
      R.patch.compensationWindow R.tube ⊆ R.patch.graphTube R.tube :=
    (R.patch.compensationWindow_subset_openGraphTube R.tube).trans
      (R.patch.openGraphTube_subset_graphTube R.tube)
  have hchange : R.patch.carrier ∆
      R.patch.variedCarrier R.patch.compensationBump
        (R.correctionScale lam r) ⊆
      R.patch.compensationWindow R.tube :=
    R.patch.carrier_symmDiff_varied_subset_compensationWindow R.tube hshift
  ext p
  by_cases hpW : p ∈ R.patch.compensationWindow R.tube
  · have hpTube := hWTube hpW
    have hUold :
        p ∈ A.extensionCompetitor r ↔ p ∈ R.patch.carrier :=
      R.extensionCompetitor_local_eq_patch_of_disjoint hdisjoint p hpTube
    have hnewG :
        p ∈ R.patch.variedCarrier R.patch.compensationBump
            (R.correctionScale lam r) ↔
          p ∈ R.patch.occupiedGraphDomain
            (R.patch.variedGraph R.patch.compensationBump
              (R.correctionScale lam r)) :=
      R.patch.mem_variedCarrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        R.tube R.patch.compensationBump (R.correctionScale lam r) hpTube
    simp only [exactAreaExtension, replaceBySymmDiff, spliceIn,
      Set.mem_symmDiff, mem_union, Set.mem_sdiff, mem_inter_iff]
    simp only [hpW, not_true, and_false, and_true]
    rw [hUold, ← hnewG]
    tauto
  · have hsame : p ∈ R.patch.carrier ↔
        p ∈ R.patch.variedCarrier R.patch.compensationBump
          (R.correctionScale lam r) := by
      by_contra hne
      have hdiff : p ∈ R.patch.carrier ∆
          R.patch.variedCarrier R.patch.compensationBump
            (R.correctionScale lam r) := by
        simp only [Set.mem_symmDiff]
        tauto
      exact hpW (hchange hdiff)
    simp only [exactAreaExtension, replaceBySymmDiff, spliceIn,
      Set.mem_symmDiff, mem_union, Set.mem_sdiff, mem_inter_iff]
    simp only [hpW, and_false, or_false]
    rw [hsame]
    tauto

/-- The collar-compatible representation makes every sufficiently small
fixed-scale exact-area correction an actual open competitor. -/
theorem isOpen_exactAreaExtension
    {lam r : ℝ}
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4) :
    IsOpen (R.exactAreaExtension lam r) := by
  rw [R.exactAreaExtension_eq_spliceIn hdisjoint hshift,
    spliceIn_eq_open_union_of_agree_near_frontier
      (R.patch.frontier_compensationWindow_subset_collar R.tube)
      (R.extensionCompetitor_inter_compensationCollar_eq hdisjoint hshift)]
  have hgraph : Continuous
      (R.patch.variedGraph R.patch.compensationBump
        (R.correctionScale lam r)) := by
    change Continuous (fun x =>
      R.patch.graph x +
        R.correctionScale lam r * R.patch.compensationBump x)
    exact R.patch.graph_contDiff.continuous.add
      (continuous_const.mul R.patch.compensationBump_contDiff.continuous)
  have hG := R.patch.isOpen_occupiedGraphDomain hgraph
  have hW : IsOpen (interior (R.patch.compensationWindow R.tube)) :=
    isOpen_interior
  have hWc : IsOpen (interior (R.patch.compensationWindow R.tube)ᶜ) :=
    isOpen_interior
  exact (((hG.inter hW).union
    ((A.isOpen_extensionCompetitor r).inter hWc))).union
      ((A.isOpen_extensionCompetitor r).inter
        (R.patch.isOpen_compensationCollar R.tube))

/-- Exact complete-frontier assembly for the two-site exact-area family.  The
contact extension pays outside the compensation-window interior, while the
actual varied occupied graph domain pays inside.  The entire cutting frontier
is assigned through the derived common collar, so no localization trace is
omitted or added by assumption. -/
theorem exactAreaExtension_complete_cost
    {lam r : ℝ}
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4) :
    smoothCost lam (R.exactAreaExtension lam r) =
      smoothCostOn lam
          (R.patch.occupiedGraphDomain
            (R.patch.variedGraph R.patch.compensationBump
              (R.correctionScale lam r)))
          (interior (R.patch.compensationWindow R.tube)) +
        smoothCostOn lam (A.extensionCompetitor r)
          (interior (R.patch.compensationWindow R.tube))ᶜ := by
  rw [R.exactAreaExtension_eq_spliceIn hdisjoint hshift]
  exact smoothCost_spliceIn_eq_inside_add_outside lam
    (R.patch.isClosed_compensationWindow R.tube)
    (R.patch.isOpen_compensationCollar R.tube)
    (R.patch.frontier_compensationWindow_subset_collar R.tube)
    (R.extensionCompetitor_inter_compensationCollar_eq hdisjoint hshift)

/-- Exact complete-cost balance: the compensation changes the contact
competitor's cost by precisely the weighted graph-length change inside the
derived window. -/
theorem exactAreaExtension_complete_cost_balance
    {lam r : ℝ} (hlam : 1 < lam)
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4) :
    smoothCost lam (R.exactAreaExtension lam r) +
        ENNReal.ofReal
          (R.patch.compensationWindowWeightedGraphLength lam
            R.patch.compensationBump 0) =
      smoothCost lam (A.extensionCompetitor r) +
        ENNReal.ofReal
          (R.patch.compensationWindowWeightedGraphLength lam
            R.patch.compensationBump (R.correctionScale lam r)) := by
  have hgraphNew : ContDiff ℝ 1
      (R.patch.variedGraph R.patch.compensationBump
        (R.correctionScale lam r)) := by
    change ContDiff ℝ 1 (fun x =>
      R.patch.graph x +
        R.correctionScale lam r * R.patch.compensationBump x)
    exact (R.patch.graph_contDiff.of_le (by norm_num)).add
      (contDiff_const.mul
        (R.patch.compensationBump_contDiff.of_le (by norm_num)))
  have hzoneNew := R.patch.variedGraph_in_zone_of_pointwise_mul_lt R.tube
    (fun x hx => (hshift x hx).trans (by linarith [R.tube.radius_pos]))
  have hnew := R.patch.smoothCostOn_occupiedGraphDomain_compensationWindow
    hlam R.tube hgraphNew hzoneNew hshift
  have hshiftZero : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |(0 : ℝ) * R.patch.compensationBump x| < R.tube.radius / 4 := by
    intro x hx
    simp only [zero_mul, abs_zero]
    linarith [R.tube.radius_pos]
  have hzoneOld := R.patch.variedGraph_in_zone_of_pointwise_mul_lt R.tube
    (v := R.patch.compensationBump) (t := 0)
    (fun x hx => (hshiftZero x hx).trans (by linarith [R.tube.radius_pos]))
  have holdVaried :=
    R.patch.smoothCostOn_occupiedGraphDomain_compensationWindow
      hlam R.tube
        (show ContDiff ℝ 1
            (R.patch.variedGraph R.patch.compensationBump 0) by
          change ContDiff ℝ 1 (fun x =>
            R.patch.graph x + 0 * R.patch.compensationBump x)
          simpa using R.patch.graph_contDiff.of_le (by norm_num))
        hzoneOld hshiftZero
  have hold : smoothCostOn lam
        (R.patch.occupiedGraphDomain R.patch.graph)
        (interior (R.patch.compensationWindow R.tube)) =
      ENNReal.ofReal
        (R.patch.compensationWindowWeightedGraphLength lam
          R.patch.compensationBump 0) := by
    have hzeroGraph :
        R.patch.variedGraph R.patch.compensationBump 0 = R.patch.graph := by
      funext x
      simp [GraphPatch.variedGraph]
    rw [hzeroGraph] at holdVaried
    exact holdVaried
  have hcontactLocal : smoothCostOn lam (A.extensionCompetitor r)
        (interior (R.patch.compensationWindow R.tube)) =
      smoothCostOn lam (R.patch.occupiedGraphDomain R.patch.graph)
        (interior (R.patch.compensationWindow R.tube)) := by
    apply smoothCostOn_eq_of_inter_open_eq lam isOpen_interior
    ext p
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hp, hpW⟩
      have hpTube : p ∈ R.patch.graphTube R.tube :=
        R.patch.openGraphTube_subset_graphTube R.tube
          (R.patch.compensationWindow_subset_openGraphTube R.tube
            (interior_subset hpW))
      exact ⟨
        (R.patch.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
          R.tube hpTube).mp
          ((R.extensionCompetitor_local_eq_patch_of_disjoint
            hdisjoint p hpTube).mp hp), hpW⟩
    · rintro ⟨hp, hpW⟩
      have hpTube : p ∈ R.patch.graphTube R.tube :=
        R.patch.openGraphTube_subset_graphTube R.tube
          (R.patch.compensationWindow_subset_openGraphTube R.tube
            (interior_subset hpW))
      exact ⟨
        (R.extensionCompetitor_local_eq_patch_of_disjoint
          hdisjoint p hpTube).mpr
          ((R.patch.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
            R.tube hpTube).mpr hp), hpW⟩
  have hpartition := smoothCostOn_add_compl lam (A.extensionCompetitor r)
    (W := interior (R.patch.compensationWindow R.tube))
    measurableSet_interior
  rw [hcontactLocal, hold] at hpartition
  rw [R.exactAreaExtension_complete_cost hdisjoint hshift, hnew,
    ← hpartition]
  ac_rfl

/-- A real bound on the graph-length change gives the same complete-cost
overhead bound for the exact-area correction. -/
theorem exactAreaExtension_complete_cost_le_add
    (R : RemoteCompensationPatch A) {lam r ε : ℝ} (hlam : 1 < lam)
    (hε : 0 ≤ ε)
    (hdisjoint : Disjoint (A.window r) (R.patch.closedGraphTube R.tube))
    (hshift : ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4)
    (hlength : |weightedGraphLength lam R.patch R.patch.compensationBump
          (R.correctionScale lam r) -
        weightedGraphLength lam R.patch R.patch.compensationBump 0| ≤ ε) :
    smoothCost lam (R.exactAreaExtension lam r) ≤
      smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal ε := by
  let newLength := R.patch.compensationWindowWeightedGraphLength lam
    R.patch.compensationBump (R.correctionScale lam r)
  let oldLength := R.patch.compensationWindowWeightedGraphLength lam
    R.patch.compensationBump 0
  have hdiff :=
    R.patch.compensationWindowWeightedGraphLength_sub_eq_weightedGraphLength_sub
      (lam := lam) R.tube hshift
  have hreal : newLength ≤ oldLength + ε := by
    dsimp [newLength, oldLength]
    linarith [hdiff, le_abs_self
      (weightedGraphLength lam R.patch R.patch.compensationBump
          (R.correctionScale lam r) -
        weightedGraphLength lam R.patch R.patch.compensationBump 0)]
  have holdNonneg : 0 ≤ oldLength := by
    exact R.patch.compensationWindowWeightedGraphLength_nonneg hlam
      R.patch.compensationBump 0
  have hofReal : ENNReal.ofReal newLength ≤
      ENNReal.ofReal oldLength + ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add holdNonneg hε]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbalance := R.exactAreaExtension_complete_cost_balance
    hlam hdisjoint hshift
  change smoothCost lam (R.exactAreaExtension lam r) +
      ENNReal.ofReal oldLength =
    smoothCost lam (A.extensionCompetitor r) +
      ENNReal.ofReal newLength at hbalance
  apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
  rw [hbalance]
  calc
    smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal newLength ≤
        smoothCost lam (A.extensionCompetitor r) +
          (ENNReal.ofReal oldLength + ENNReal.ofReal ε) :=
      add_le_add_right hofReal _
    _ = (smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal ε) +
        ENNReal.ofReal oldLength := by ac_rfl

/-- The exact area correction displaces the remote graph by less than one
quarter of the protected tube radius at every sufficiently small positive
contact scale. -/
theorem eventually_correctionShift_lt_quarter
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ x ∈ Ioc R.patch.a R.patch.b,
      |R.correctionScale lam r * R.patch.compensationBump x| <
        R.tube.radius / 4 := by
  obtain ⟨M, hM, hMbound⟩ := R.patch.exists_compensationBump_bound
  have hscale := R.tendsto_correctionScale_zero hlam
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |R.correctionScale lam r| < R.tube.radius / (4 * M) := by
    have heps : 0 < R.tube.radius / (4 * M) :=
      div_pos R.tube.radius_pos (mul_pos (by norm_num) hM)
    have hball := hscale.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
    filter_upwards [hball] with r hr
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hr
  filter_upwards [hsmall] with r hscaleSmall
  intro x _hx
  rw [abs_mul]
  calc
    |R.correctionScale lam r| * |R.patch.compensationBump x| ≤
        |R.correctionScale lam r| * M :=
      mul_le_mul_of_nonneg_left (hMbound x)
        (abs_nonneg (R.correctionScale lam r))
    _ < (R.tube.radius / (4 * M)) * M :=
      mul_lt_mul_of_pos_right hscaleSmall hM
    _ = R.tube.radius / 4 := by field_simp [ne_of_gt hM]

/-- The exact-area correction has at most quadratic complete-cost overhead
relative to the unchecked-area contact extension. -/
theorem eventually_exactAreaExtension_complete_cost_le_add_quadratic
    {lam : ℝ} (hlam : 1 < lam) :
    ∃ Q ≥ 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost lam (R.exactAreaExtension lam r) ≤
        smoothCost lam (A.extensionCompetitor r) +
          ENNReal.ofReal (Q * r ^ 2) := by
  obtain ⟨Q, hQ, hlength⟩ :=
    R.eventually_compensationWeightedGraphLength_sub_le_quadratic hlam
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [R.eventually_exactAreaExtension_feasible hlam,
    R.eventually_correctionShift_lt_quarter hlam, hlength] with
      r hfeasible hshift hlength
  exact R.exactAreaExtension_complete_cost_le_add hlam
    (mul_nonneg hQ (sq_nonneg r)) hfeasible.2.1 hshift hlength

/-- The complete-frontier decomposition holds at every sufficiently small
positive contact scale.  The stronger quarter-tube displacement follows from
the actual quadratic area correction tending to zero, not from a supplied
frontier or comparison hypothesis. -/
theorem eventually_exactAreaExtension_complete_cost
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost lam (R.exactAreaExtension lam r) =
        smoothCostOn lam
            (R.patch.occupiedGraphDomain
              (R.patch.variedGraph R.patch.compensationBump
                (R.correctionScale lam r)))
            (interior (R.patch.compensationWindow R.tube)) +
          smoothCostOn lam (A.extensionCompetitor r)
            (interior (R.patch.compensationWindow R.tube))ᶜ := by
  filter_upwards [R.eventually_exactAreaExtension_feasible hlam,
    R.eventually_correctionShift_lt_quarter hlam] with
      r hfeasible hshiftQuarter
  exact R.exactAreaExtension_complete_cost hfeasible.2.1 hshiftQuarter

end RemoteCompensationPatch

/-- A strict conormal violation plus one disjoint remote regular graph patch
rules out complete-frontier minimality: the exact-area correction is open and
bounded, while its quadratic cost is absorbed by the linear contact gain. -/
theorem not_completeFrontierMinimizing_of_conormal_lt
    (M : A.MetricApplicability)
    (S : A.SignedInterfaceApplicability)
    (P : A.SignedIncidentPhaseApplicability)
    (lam : ℝ) (hlam : 1 < lam) (hphase : P.phase = .exterior)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / lam) :
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C lam
    let A' := A.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos hlam hc)
    ∀ _R : RemoteCompensationPatch A',
      smoothCost lam C.representative < ⊤ →
      ¬ (∀ U : Set PlanePoint, IsOpen U → Bornology.IsBounded U →
        WeightedArea lam U = WeightedArea lam C.representative →
        smoothCost lam C.representative ≤ smoothCost lam U) := by
  dsimp only
  intro _R hcost hmin
  obtain ⟨k, hk, hcontact⟩ :=
    A.eventually_normalizedExtension_complete_cost_add_linear_le_of_conormal_lt
      M S P lam hlam hphase hc
  obtain ⟨Q, hQ, hoverhead⟩ :=
    _R.eventually_exactAreaExtension_complete_cost_le_add_quadratic hlam
  have hden : 0 < Q + 1 := by linarith
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < k / (Q + 1) :=
    (eventually_lt_nhds (div_pos hk hden)).filter_mono inf_le_left
  have hcontra : ∀ᶠ r in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [self_mem_nhdsWithin, hcontact, hoverhead, hsmall,
      _R.eventually_exactAreaExtension_feasible hlam,
      _R.eventually_correctionShift_lt_quarter hlam] with
        r hr hcontact hoverhead hrSmall hfeasible hshift
    have hdenMul : (Q + 1) * r < k := by
      calc
        (Q + 1) * r < (Q + 1) * (k / (Q + 1)) :=
          mul_lt_mul_of_pos_left hrSmall hden
        _ = k := by field_simp [ne_of_gt hden]
    have hquad : Q * r ^ 2 < k * r := by
      nlinarith [mul_pos hr hden]
    have hofReal : ENNReal.ofReal (Q * r ^ 2) < ENNReal.ofReal (k * r) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos hk hr)).2 hquad
    have hcontactNeTop : smoothCost lam
        ((A.positiveDiagonalReparam
          (normalizedExtensionIncidentScale C)
          (normalizedExtensionInterfaceScale C lam)
          normalizedExtensionIncidentScale_pos
          (normalizedExtensionInterfaceScale_pos hlam hc)).extensionCompetitor r) ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hcontact
      exact (not_le_of_gt hcost) hcontact
    have hstrict := hoverhead.trans_lt <|
      (ENNReal.add_lt_add_left hcontactNeTop hofReal).trans_le hcontact
    rcases hfeasible with
      ⟨_hlocal, hdisjoint, _hshift, _hvalid, _hmeasurable, hbounded,
        harea, _hcontact, _hcompensation⟩
    exact (not_le_of_gt hstrict) <|
      hmin _ (_R.isOpen_exactAreaExtension hdisjoint hshift) hbounded harea
  obtain ⟨r, hr⟩ := Filter.Eventually.exists hcontra
  exact hr

/-- Unilateral contact law derived from complete-frontier minimality whenever
a disjoint remote regular compensation patch is available under a putative
strict violation.  The law is a conclusion, not an input comparison axiom. -/
theorem conormal_inner_ge_neg_inv_of_completeFrontier_minimality
    (M : A.MetricApplicability)
    (S : A.SignedInterfaceApplicability)
    (P : A.SignedIncidentPhaseApplicability)
    (lam : ℝ) (hlam : 1 < lam) (hphase : P.phase = .exterior)
    (hremote : ∀ hc :
      planeInner C.incidentConormal C.interfaceConormal < -1 / lam,
      RemoteCompensationPatch
        (A.positiveDiagonalReparam
          (normalizedExtensionIncidentScale C)
          (normalizedExtensionInterfaceScale C lam)
          normalizedExtensionIncidentScale_pos
          (normalizedExtensionInterfaceScale_pos hlam hc)))
    (hcost : smoothCost lam C.representative < ⊤)
    (hmin : ∀ U : Set PlanePoint, IsOpen U → Bornology.IsBounded U →
      WeightedArea lam U = WeightedArea lam C.representative →
      smoothCost lam C.representative ≤ smoothCost lam U) :
    -1 / lam ≤ planeInner C.incidentConormal C.interfaceConormal := by
  by_contra hn
  have hc :
      planeInner C.incidentConormal C.interfaceConormal < -1 / lam :=
    lt_of_not_ge hn
  exact
    (not_completeFrontierMinimizing_of_conormal_lt M S P lam hlam hphase
      hc (hremote hc) hcost) hmin

end CMVRelaxation.RegularTraceCornerComparison
