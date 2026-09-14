import CMVRegularGermExactAreaFrontier
import CMVInterfaceExtensionGenericSpecimen

/-!
# Exact-area compensation for the affine extension specimen

A fixed upper-boundary patch of the literal finite-band representative supplies
the remote normalized bump.  All data below are derived from that representative.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal symmDiff

noncomputable section

namespace CMVRelaxation.InterfaceExtensionExactAreaSpecimen

open FiniteBandRearrangement
open RegularTraceCornerComparison
open CMVTwoPatchGraphVariation

abbrev A := InterfaceExtensionGenericSpecimen.normalizedApplicability

/-- A horizontal patch on the unchanged top edge of the specimen. -/
def topPatch : GraphPatch where
  a := -1 / 4
  b := 1 / 4
  base := 3 / 2
  graph := fun _ => 9 / 5
  lowerBound := 7 / 5
  upperBound := 2
  zone := .exterior
  side := .below
  a_lt_b := by norm_num
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := by norm_num
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    rintro p ⟨_hx, hyLower, _hyUpper⟩
    change 1 < |p.2|
    rw [abs_of_pos (by linarith)]
    linarith

/-- A fixed tube around the top edge, entirely in the upper exterior phase. -/
def topTube : topPatch.Tube where
  radius := 1 / 20
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [topPatch]
  graph_lower_clearance := by intros; norm_num [topPatch]
  graph_upper_clearance := by intros; norm_num [topPatch]
  closed_tube_in_zone := by
    intro x _hx y hy
    change 1 < |y|
    change |y - 9 / 5| ≤ 1 / 20 at hy
    rw [abs_le] at hy
    rw [abs_of_pos (by linarith)]
    linarith

private lemma oldOpen_height_lt_top {p : PlanePoint}
    (hp : p ∈ InterfaceExtensionSpecimen.oldOpen) : p.2 < 9 / 5 := by
  have hpNhd : InterfaceExtensionSpecimen.oldRegion.carrier ∈ 𝓝 p :=
    mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
  rcases Metric.mem_nhds_iff.mp hpNhd with ⟨eps, heps, hball⟩
  let z : PlanePoint := (p.1, p.2 + eps / 2)
  have hzball : z ∈ Metric.ball p eps := by
    change dist z p < eps
    rw [Prod.dist_eq, dist_self, max_eq_right]
    · dsimp [z]
      rw [Real.dist_eq]
      simp only [add_sub_cancel_left, abs_div, abs_of_pos heps]
      linarith
    · exact dist_nonneg
  have hz := hball hzball
  rw [Region.carrier, mem_iUnion] at hz
  rcases hz with ⟨i, hz⟩
  rw [Region.bandCarrier, mem_iUnion] at hz
  rcases hz with ⟨j, hz⟩
  rw [InterfaceExtensionSpecimen.oldRegion.mem_componentCarrier_iff] at hz
  fin_cases i
  fin_cases j
  have hzUpper := hz.1.2
  change z.2 ≤ 9 / 5 at hzUpper
  dsimp [z] at hzUpper
  linarith



/-- On the open graph tube, the unchanged specimen is exactly the portion
below its top graph. -/
theorem representative_local_topPatch :
    ∀ p ∈ topPatch.graphTube topTube,
      (p ∈ InterfaceExtensionSpecimen.oldOpen ↔ p ∈ topPatch.carrier) := by
  intro p hpTube
  rcases hpTube with ⟨hx, hyTube⟩
  change p.1 ∈ Ioc (-1 / 4 : ℝ) (1 / 4) at hx
  change |p.2 - 9 / 5| < 1 / 20 at hyTube
  rw [abs_lt] at hyTube
  constructor
  · intro hp
    have hyTop := oldOpen_height_lt_top hp
    change p.1 ∈ Ioc (-1 / 4 : ℝ) (1 / 4) ∧
      p.2 ∈ Ioo (3 / 2 : ℝ) (9 / 5)
    exact ⟨hx, by constructor <;> linarith⟩
  · intro hp
    change p.1 ∈ Ioc (-1 / 4 : ℝ) (1 / 4) ∧
      p.2 ∈ Ioo (3 / 2 : ℝ) (9 / 5) at hp
    let i : Fin InterfaceExtensionSpecimen.oldRegion.bandCount :=
      ⟨0, by simp [InterfaceExtensionSpecimen.oldRegion]⟩
    let j : Fin (InterfaceExtensionSpecimen.oldRegion.componentCount i) :=
      ⟨0, by simp [i, InterfaceExtensionSpecimen.oldRegion]⟩
    apply interior_mono (show
      InterfaceExtensionSpecimen.oldRegion.componentCarrier i j ⊆
        InterfaceExtensionSpecimen.oldRegion.carrier by
      intro q hq
      rw [Region.carrier, mem_iUnion]
      refine ⟨i, ?_⟩
      rw [Region.bandCarrier, mem_iUnion]
      exact ⟨j, hq⟩)
    apply InterfaceExtensionSpecimen.oldRegion.mem_interior_componentCarrier_of_strict
    · change 1 < p.2 ∧ p.2 < 9 / 5
      exact ⟨by linarith [hp.2.1], hp.2.2⟩
    · change InterfaceExtensionSpecimen.oldLeft p.2 < p.1 ∧
        p.1 < InterfaceExtensionSpecimen.oldRight p.2
      unfold InterfaceExtensionSpecimen.oldLeft InterfaceExtensionSpecimen.oldRight
      constructor <;> nlinarith [hx.1, hx.2, hp.2.1, hp.2.2]

/-- The top graph is a literal open subarc of the specimen frontier. -/
theorem topPatch_graph_frontier :
    ∀ x ∈ Ioo topPatch.a topPatch.b,
      (x, topPatch.graph x) ∈ frontier InterfaceExtensionSpecimen.oldOpen := by
  intro x hx
  rw [InterfaceExtensionSpecimen.frontier_oldOpen_eq_namedPieces]
  refine Or.inr (Or.inr ?_)
  change (x, (9 : ℝ) / 5) ∈ InterfaceExtensionSpecimen.topSegment
  exact ⟨x, ⟨by
    change (-1 / 4 : ℝ) < x ∧ x < 1 / 4 at hx
    constructor <;> linarith, by rfl⟩⟩

/-- A fully concrete remote compensation patch for the affine specimen. -/
def remoteCompensation : RemoteCompensationPatch A where
  patch := topPatch
  tube := topTube
  junction_not_mem_tube := by
    intro h
    rcases h with ⟨_hx, hy⟩
    change |(1 : ℝ) - 9 / 5| ≤ 1 / 20 at hy
    norm_num at hy
  representative_local := representative_local_topPatch
  graph_frontier := topPatch_graph_frontier

/-- At density contrast two, the concrete two-site family is eventually
measurable, bounded, exactly area-preserving, and localized in disjoint contact
and compensation tubes. -/
theorem eventually_exactAreaExtension_two :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      MeasurableSet (remoteCompensation.exactAreaExtension 2 r) ∧
      Bornology.IsBounded (remoteCompensation.exactAreaExtension 2 r) ∧
      WeightedArea 2 (remoteCompensation.exactAreaExtension 2 r) =
        WeightedArea 2 InterfaceExtensionSpecimen.oldOpen ∧
      Disjoint (A.window r) (topPatch.closedGraphTube topTube) := by
  filter_upwards [
    remoteCompensation.eventually_exactAreaExtension_feasible
      (lam := 2) (by norm_num)] with r hr
  rcases hr with
    ⟨_hlocal, hdisjoint, _hshift, _hvalid, hmeas, hbounded,
      harea, _hcontact, _hcomp⟩
  exact ⟨hmeas, hbounded, harea, hdisjoint⟩

/-- The concrete compensation graph has finite quadratic weighted-length
overhead. -/
theorem compensationWeightedGraphLength_two_quadratic :
    ∃ Q ≥ 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |weightedGraphLength 2 topPatch topPatch.compensationBump
          (remoteCompensation.correctionScale 2 r) -
        weightedGraphLength 2 topPatch topPatch.compensationBump 0| ≤
          Q * r ^ 2 :=
  remoteCompensation.eventually_compensationWeightedGraphLength_sub_le_quadratic
    (by norm_num)

/-- The compensation is attached to the same endpoint-normalized contact
family whose complete frontier cost has the checked strict descent. -/
theorem eventually_normalizedContact_complete_cost_lt :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost 2 (A.extensionCompetitor r) <
        smoothCost 2 InterfaceExtensionSpecimen.oldOpen := by
  simpa [A, InterfaceExtensionGenericSpecimen.normalizedApplicability,
    InterfaceExtensionSpecimen.actualCorner] using
      InterfaceExtensionGenericSpecimen.eventually_normalizedExtension_complete_cost_lt

/-- At all sufficiently small positive scales, the concrete normalized
two-site family simultaneously has exact source area and the derived complete
frontier decomposition through the remote graph window. -/
theorem eventually_exactAreaExtension_frontier_two :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      WeightedArea 2 (remoteCompensation.exactAreaExtension 2 r) =
          WeightedArea 2 InterfaceExtensionSpecimen.oldOpen ∧
        smoothCost 2 (remoteCompensation.exactAreaExtension 2 r) =
          smoothCostOn 2
              (topPatch.occupiedGraphDomain
                (topPatch.variedGraph topPatch.compensationBump
                  (remoteCompensation.correctionScale 2 r)))
              (interior (topPatch.compensationWindow topTube)) +
            smoothCostOn 2 (A.extensionCompetitor r)
              (interior (topPatch.compensationWindow topTube))ᶜ := by
  filter_upwards [
    remoteCompensation.eventually_exactAreaExtension_feasible
      (lam := 2) (by norm_num),
    remoteCompensation.eventually_exactAreaExtension_complete_cost
      (lam := 2) (by norm_num)] with r hfeasible hcost
  exact ⟨hfeasible.2.2.2.2.2.2.1, hcost⟩

/-- The actual two-site competitor preserves source area exactly and strictly
lowers the complete frontier cost: the linear contact gain absorbs the
quadratic remote compensation overhead. -/
theorem eventually_exactAreaExtension_complete_cost_lt :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost 2 (remoteCompensation.exactAreaExtension 2 r) <
        smoothCost 2 InterfaceExtensionSpecimen.oldOpen := by
  obtain ⟨k, hk, hcontact⟩ :=
    InterfaceExtensionGenericSpecimen.eventually_normalizedExtension_complete_cost_add_linear_le
  obtain ⟨Q, hQ, hoverhead⟩ :=
    remoteCompensation.eventually_exactAreaExtension_complete_cost_le_add_quadratic
      (lam := 2) (by norm_num)
  have hden : 0 < Q + 1 := by linarith
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < k / (Q + 1) :=
    (eventually_lt_nhds (div_pos hk hden)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hcontact, hoverhead, hsmall] with
      r hr hcontact hoverhead hrSmall
  have hdenMul : (Q + 1) * r < k := by
    calc
      (Q + 1) * r < (Q + 1) * (k / (Q + 1)) :=
        mul_lt_mul_of_pos_left hrSmall hden
      _ = k := by field_simp [ne_of_gt hden]
  have hquad : Q * r ^ 2 < k * r := by
    nlinarith [mul_pos hr hden]
  have hofReal : ENNReal.ofReal (Q * r ^ 2) < ENNReal.ofReal (k * r) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos hk hr)).2 hquad
  have holdTop : smoothCost 2 InterfaceExtensionSpecimen.oldOpen < ⊤ := by
    change smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative < ⊤
    rw [InterfaceExtensionGenericSpecimen.actualCorner_smoothCost_eq]
    simp
  have hcontactNeTop : smoothCost 2 (A.extensionCompetitor r) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hcontact
    exact (not_le_of_gt holdTop) hcontact
  exact hoverhead.trans_lt <|
    (ENNReal.add_lt_add_left hcontactNeTop hofReal).trans_le hcontact

/-- Eventually the concrete exact-area competitor is open, bounded, exactly
area-preserving, and strictly cheaper in complete-frontier cost. -/
theorem eventually_exactAreaExtension_open_bounded_area_cost :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      IsOpen (remoteCompensation.exactAreaExtension 2 r) ∧
        Bornology.IsBounded (remoteCompensation.exactAreaExtension 2 r) ∧
        WeightedArea 2 (remoteCompensation.exactAreaExtension 2 r) =
          WeightedArea 2 InterfaceExtensionSpecimen.oldOpen ∧
        smoothCost 2 (remoteCompensation.exactAreaExtension 2 r) <
          smoothCost 2 InterfaceExtensionSpecimen.oldOpen := by
  filter_upwards [
    remoteCompensation.eventually_exactAreaExtension_feasible
      (lam := 2) (by norm_num),
    remoteCompensation.eventually_correctionShift_lt_quarter
      (lam := 2) (by norm_num),
    eventually_exactAreaExtension_complete_cost_lt] with
      r hfeasible hshift hcost
  rcases hfeasible with
    ⟨_hlocal, hdisjoint, _hshift, _hvalid, _hmeasurable, hbounded,
      harea, _hcontact, _hcompensation⟩
  exact ⟨remoteCompensation.isOpen_exactAreaExtension hdisjoint hshift,
    hbounded, harea, hcost⟩

/-- The specimen cannot minimize complete-frontier cost among open bounded
competitors with the same weighted area.  The contradiction is consumed from
the actual exact-area two-site family, not from an assumed comparison law. -/
theorem not_completeFrontierMinimizing :
    ¬ (∀ U : Set PlanePoint, IsOpen U → Bornology.IsBounded U →
      WeightedArea 2 U = WeightedArea 2 InterfaceExtensionSpecimen.oldOpen →
      smoothCost 2 InterfaceExtensionSpecimen.oldOpen ≤ smoothCost 2 U) := by
  intro hmin
  obtain ⟨r, hopen, hbounded, harea, hcost⟩ :=
    Filter.Eventually.exists eventually_exactAreaExtension_open_bounded_area_cost
  exact (not_le_of_gt hcost) (hmin _ hopen hbounded harea)


end CMVRelaxation.InterfaceExtensionExactAreaSpecimen
