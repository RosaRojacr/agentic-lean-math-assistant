/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVMixedChartSupportContinuation
import CMVSourceFiniteSlabArcInventory
import FrontierPerimeter

/-!
# Maximal exterior arcs from branch-neutral continuation

This module begins the global arc-inventory step after mixed-coordinate support
continuation.  The reach record names actual points of one continuation
component, not a circle, line, finite arc list, endpoint order beyond the two
actual interface contacts, or a selected CMV configuration.
-/

open Set Function Filter Real MeasureTheory Metric Bornology
open scoped Topology ContDiff
noncomputable section

namespace CMVExteriorMaximalArc

open CMVTwoPatchGraphVariation
open CMVSourceBoundaryContinuation
open CMVSourceFiniteSlabArcInventory
open CMVSourceBoundaryContinuation.MixedGraphAtlas
open CMVSourceClassification
open CMVFigureFour

/-! ## Detached full-support exclusion -/

/-- Two transverse points of a full locally one-sided circle force its center
into an open bounded order-connected horizontal section. -/
theorem center_mem_of_equator_locallyOneSided
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U)
    (hsections : ∀ y : ℝ, (horizontalSection U y).OrdConnected)
    {center : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hleft : LocallyOneSided U center radius
      (center.1 - radius, center.2))
    (hright : LocallyOneSided U center radius
      (center.1 + radius, center.2)) :
    center ∈ U := by
  have hleftCircle :
      circleValue center radius (center.1 - radius, center.2) = 0 := by
    unfold circleValue
    dsimp only
    ring
  have hrightCircle :
      circleValue center radius (center.1 + radius, center.2) = 0 := by
    unfold circleValue
    dsimp only
    ring
  have hleftFrontier : center.1 - radius ∈
      frontier (horizontalSection U center.2) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hleftCircle (by linarith) hleft
  have hrightFrontier : center.1 + radius ∈
      frontier (horizontalSection U center.2) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hrightCircle (by linarith) hright
  let S : Set ℝ := horizontalSection U center.2
  have hSne : S.Nonempty := by
    by_contra hnone
    have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hnone
    rw [show horizontalSection U center.2 = ∅ from hSempty,
      frontier_empty] at hleftFrontier
    exact hleftFrontier
  have hSopen : IsOpen S := isOpen_horizontalSection hUopen center.2
  have hSbounded : Bornology.IsBounded S :=
    isBounded_horizontalSection hUbounded center.2
  have hSeq : S = Ioo (sInf S) (sSup S) :=
    CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hSne hSbounded (hsections center.2)
  have hendpoints := openInterval_endpoints_of_ordered_frontier
    (le_of_lt (show sInf S < sSup S by
      obtain ⟨x, hx⟩ := hSne
      have hx' : x ∈ Ioo (sInf S) (sSup S) := hSeq ▸ hx
      exact hx'.1.trans hx'.2)) hSeq hleftFrontier hrightFrontier (by linarith)
  change center.1 ∈ horizontalSection U center.2
  rw [show horizontalSection U center.2 = S from rfl, hSeq,
    hendpoints.1, hendpoints.2]
  exact ⟨by linarith, by linarith⟩

/-- If a connected open set contains the circle center and the full circle is
in its frontier, then the set stays strictly inside the circle. -/
theorem circleValue_neg_of_center_mem_of_circle_subset_frontier
    {U : Set PlanePoint} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    {center : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hcircleFrontier :
      {p : PlanePoint | circleValue center radius p = 0} ⊆ frontier U)
    (hcenter : center ∈ U) :
    ∀ p ∈ U, circleValue center radius p < 0 := by
  intro p hp
  have hcenterNeg : circleValue center radius center < 0 := by
    unfold circleValue
    nlinarith
  have hzeroNotMem : ∀ q ∈ U, circleValue center radius q ≠ 0 := by
    intro q hq hqzero
    have hqFrontier : q ∈ frontier U := hcircleFrontier hqzero
    have hqInter : q ∈ U ∩ frontier U := ⟨hq, hqFrontier⟩
    rw [hUopen.inter_frontier_eq] at hqInter
    exact hqInter
  rcases lt_or_gt_of_ne (hzeroNotMem p hp) with hpneg | hppos
  · exact hpneg
  · have hzeroImage : 0 ∈ circleValue center radius '' U := by
      apply hUconnected.isPreconnected.intermediate_value hcenter hp
        (by unfold circleValue; fun_prop)
      exact ⟨hcenterNeg.le, hppos.le⟩
    rcases hzeroImage with ⟨q, hqU, hqzero⟩
    exact (hzeroNotMem q hqU hqzero).elim

/-- A detached complete supporting circle is impossible once the bounded,
connected interval-section representative reaches the nonnegative side of that
circle.  No source minimality or component count is used. -/
theorem not_full_circle_frontier_of_interval_sections_and_reach
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U) (hUconnected : IsConnected U)
    (hsections : ∀ y : ℝ, (horizontalSection U y).OrdConnected)
    {center : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hcircleFrontier :
      {p : PlanePoint | circleValue center radius p = 0} ⊆ frontier U)
    (hleft : LocallyOneSided U center radius
      (center.1 - radius, center.2))
    (hright : LocallyOneSided U center radius
      (center.1 + radius, center.2))
    (reach : ∃ q ∈ U, 0 ≤ circleValue center radius q) : False := by
  have hcenter : center ∈ U :=
    center_mem_of_equator_locallyOneSided hUopen hUbounded hsections
      hradius hleft hright
  obtain ⟨q, hqU, hqvalue⟩ := reach
  have hqneg := circleValue_neg_of_center_mem_of_circle_subset_frontier
    hUopen hUconnected hradius hcircleFrontier hcenter q hqU
  linarith

/-- A nonzero atlas support is the zero locus of `circleValue`, with positive
geometric radius `|1 / K|`; no sign of `K` is assumed. -/
theorem supportAt_eq_circleValue_zero
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) :
    A.supportAt p =
      {q : PlanePoint |
        circleValue ((A.chart p).patch.supportingCenter K p.1.1)
          |1 / K| q = 0} := by
  rw [BranchNeutralGraphAtlas.supportAt, if_neg hK]
  have hradii :
      (1 / ((A.chart p).patch.side.areaSign * K)) ^ 2 =
        (1 / K) ^ 2 := by
    field_simp [hK, (A.chart p).patch.side.areaSign_ne_zero]
    nlinarith [(A.chart p).patch.side.areaSign_mul_self]
  ext q
  simp only [GraphPatch.supportingCircle, Set.mem_ofPred_eq, circleValue]
  rw [sq_abs, sub_eq_zero, hradii]

/-- A truthful vertical graph germ on a nonzero constant-curvature support is
locally one side of its literal supporting circle.  The circle side is derived
from the graph-side label and the local support branch. -/
theorem locallyOneSided_of_vertical_regularChart
    {carrier : Set PlanePoint} (C : ActualRegularGraphChart carrier)
    {K x : ℝ} (hK : K ≠ 0)
    (hx : x ∈ Ioo C.patch.a C.patch.b)
    (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
      C.patch.orientedGraphCurvature z = K)
    (hoccupied : ∀ᶠ q in 𝓝 (C.patch.graphTrace x),
      (q ∈ carrier ↔
        q ∈ C.patch.occupiedGraphDomain C.patch.graph)) :
    LocallyOneSided carrier (C.patch.supportingCenter K x) |1 / K|
      (C.patch.graphTrace x) := by
  let center := C.patch.supportingCenter K x
  let d := C.patch.graph x - center.2
  have hd : d ≠ 0 := by
    dsimp only [d, center]
    unfold GraphPatch.supportingCenter
      CMVCurvatureIntegration.centerInvariant
      CMVCurvatureIntegration.normalizedTangent
    simp only [GraphPatch.graphTrace, GraphPatch.graphVelocity,
      C.patch.euclideanSpeed_graphVelocity]
    have hsqrt : √(1 + deriv C.patch.graph x ^ 2) ≠ 0 := by
      positivity
    have hterm : 1 / √(1 + deriv C.patch.graph x ^ 2) /
        (C.patch.side.areaSign * K) ≠ 0 :=
      div_ne_zero (one_div_ne_zero hsqrt)
        (mul_ne_zero C.patch.side.areaSign_ne_zero hK)
    intro hzero
    apply hterm
    linarith
  have hradii :
      (1 / (C.patch.side.areaSign * K)) ^ 2 = |1 / K| ^ 2 := by
    rw [sq_abs]
    field_simp [hK, C.patch.side.areaSign_ne_zero]
    nlinarith [C.patch.side.areaSign_mul_self]
  have hparameter :
      ∀ᶠ q in 𝓝 (C.patch.graphTrace x),
        q.1 ∈ Ioo C.patch.a C.patch.b :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds hx
  let branchFactor : PlanePoint → ℝ := fun q =>
    (q.2 + C.patch.graph q.1 - 2 * center.2) * d
  have hbranchFactorContinuous : Continuous branchFactor := by
    dsimp only [branchFactor]
    exact ((continuous_snd.add
      (C.patch.graph_contDiff.continuous.comp continuous_fst)).sub
        continuous_const).mul continuous_const
  have hbranchFactorBase :
      0 < branchFactor (C.patch.graphTrace x) := by
    dsimp only [branchFactor, GraphPatch.graphTrace]
    nlinarith [mul_self_pos.mpr hd]
  have hbranchFactor :
      ∀ᶠ q in 𝓝 (C.patch.graphTrace x), 0 < branchFactor q :=
    (isOpen_lt continuous_const hbranchFactorContinuous).mem_nhds
      hbranchFactorBase
  have hcircleFactor (q : PlanePoint)
      (hq : q.1 ∈ Ioo C.patch.a C.patch.b) :
      circleValue center |1 / K| q =
        (q.2 - C.patch.graph q.1) *
          (q.2 + C.patch.graph q.1 - 2 * center.2) := by
    have hgraphSupport :=
      C.patch.closed_graph_circle_identity hcurv hK
        ⟨hx.1.le, hx.2.le⟩ ⟨hq.1.le, hq.2.le⟩
    simp only [GraphPatch.graphTrace] at hgraphSupport
    change (q.1 - center.1) ^ 2 +
      (C.patch.graph q.1 - center.2) ^ 2 =
        (1 / (C.patch.side.areaSign * K)) ^ 2 at hgraphSupport
    unfold circleValue
    rw [← hradii]
    nlinarith [hgraphSupport]
  have finish (side : CircleSide)
      (hlocal : ∀ᶠ q in 𝓝 (C.patch.graphTrace x),
        (q ∈ carrier ↔
          side.sign * circleValue center |1 / K| q < 0)) :
      LocallyOneSided carrier center |1 / K| (C.patch.graphTrace x) := by
    rcases _root_.mem_nhds_iff.mp hlocal with
      ⟨V, hVsub, hVopen, hpV⟩
    refine ⟨side, V, hVopen, hpV, ?_⟩
    ext q
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      exact ⟨hqV, (hVsub hqV).mp hqCarrier⟩
    · rintro ⟨hqV, hqSide⟩
      exact ⟨(hVsub hqV).mpr hqSide, hqV⟩
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · cases hside : C.patch.side with
    | below =>
        apply finish .outside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumNeg :
            q.2 + C.patch.graph q.1 - 2 * center.2 < 0 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact (hdneg.not_gt hpos.2).elim
          · exact hneg.1
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign, GraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq]
        constructor
        · intro hbelow
          have hpositive := mul_pos_of_neg_of_neg
            (sub_neg.mpr hbelow) hsumNeg
          linarith
        · intro hnegative
          by_contra hnotBelow
          have hdiff : 0 ≤ q.2 - C.patch.graph q.1 := by
            linarith
          have hproduct := mul_nonpos_of_nonneg_of_nonpos
            hdiff hsumNeg.le
          linarith
    | above =>
        apply finish .inside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumNeg :
            q.2 + C.patch.graph q.1 - 2 * center.2 < 0 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact (hdneg.not_gt hpos.2).elim
          · exact hneg.1
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign, GraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq, one_mul]
        constructor
        · intro habove
          exact mul_neg_of_pos_of_neg (sub_pos.mpr habove) hsumNeg
        · intro hnegative
          by_contra hnotAbove
          have hdiff : q.2 - C.patch.graph q.1 ≤ 0 := by
            linarith
          have hproduct := mul_nonneg_of_nonpos_of_nonpos
            hdiff hsumNeg.le
          linarith
  · cases hside : C.patch.side with
    | below =>
        apply finish .inside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumPos :
            0 < q.2 + C.patch.graph q.1 - 2 * center.2 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact hpos.1
          · exact (not_lt_of_ge hdpos.le hneg.2).elim
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign, GraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq, one_mul]
        constructor
        · intro hbelow
          exact mul_neg_of_neg_of_pos (sub_neg.mpr hbelow) hsumPos
        · intro hnegative
          by_contra hnotBelow
          have hdiff : 0 ≤ q.2 - C.patch.graph q.1 := by
            linarith
          have hproduct := mul_nonneg hdiff hsumPos.le
          linarith
    | above =>
        apply finish .outside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumPos :
            0 < q.2 + C.patch.graph q.1 - 2 * center.2 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact hpos.1
          · exact (not_lt_of_ge hdpos.le hneg.2).elim
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign, GraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq]
        constructor
        · intro habove
          have hpositive := mul_pos (sub_pos.mpr habove) hsumPos
          linarith
        · intro hnegative
          by_contra hnotAbove
          have hdiff : q.2 - C.patch.graph q.1 ≤ 0 := by
            linarith
          have hproduct := mul_nonpos_of_nonpos_of_nonneg
            hdiff hsumPos.le
          linarith

/-- Horizontal-coordinate counterpart of
`locallyOneSided_of_vertical_regularChart`. -/
theorem locallyOneSided_of_horizontal_regularChart
    {carrier : Set PlanePoint}
    (C : ActualRegularHorizontalGraphChart carrier)
    {K y : ℝ} (hK : K ≠ 0)
    (hy : y ∈ Ioo C.patch.a C.patch.b)
    (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
      C.patch.orientedGraphCurvature z = K)
    (hoccupied : ∀ᶠ q in 𝓝 (C.patch.graphTrace y),
      (q ∈ carrier ↔ q ∈ C.patch.occupiedGraphDomain)) :
    LocallyOneSided carrier (C.patch.supportingCenter K y) |1 / K|
      (C.patch.graphTrace y) := by
  let center := C.patch.supportingCenter K y
  let d := C.patch.graph y - center.1
  have hd : d ≠ 0 := by
    dsimp only [d, center]
    unfold CMVTransverseContactVariation.HorizontalGraphPatch.supportingCenter
      CMVCurvatureIntegration.centerInvariant
      CMVCurvatureIntegration.normalizedTangent
    simp only [CMVTransverseContactVariation.HorizontalGraphPatch.graphTrace,
      CMVTransverseContactVariation.HorizontalGraphPatch.graphVelocity,
      C.patch.euclideanSpeed_graphVelocity]
    have hsqrt : √(1 + deriv C.patch.graph y ^ 2) ≠ 0 := by
      positivity
    have hterm : 1 / √(1 + deriv C.patch.graph y ^ 2) /
        (-(C.patch.side.areaSign * K)) ≠ 0 :=
      div_ne_zero (one_div_ne_zero hsqrt)
        (neg_ne_zero.mpr
          (mul_ne_zero C.patch.side.areaSign_ne_zero hK))
    intro hzero
    apply hterm
    linarith
  have hradii :
      (1 / (-(C.patch.side.areaSign * K))) ^ 2 = |1 / K| ^ 2 := by
    rw [sq_abs]
    field_simp [hK, C.patch.side.areaSign_ne_zero]
    nlinarith [C.patch.side.areaSign_mul_self]
  have hparameter :
      ∀ᶠ q in 𝓝 (C.patch.graphTrace y),
        q.2 ∈ Ioo C.patch.a C.patch.b :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hy
  let branchFactor : PlanePoint → ℝ := fun q =>
    (q.1 + C.patch.graph q.2 - 2 * center.1) * d
  have hbranchFactorContinuous : Continuous branchFactor := by
    dsimp only [branchFactor]
    exact ((continuous_fst.add
      (C.patch.graph_contDiff.continuous.comp continuous_snd)).sub
        continuous_const).mul continuous_const
  have hbranchFactorBase :
      0 < branchFactor (C.patch.graphTrace y) := by
    dsimp only [branchFactor,
      CMVTransverseContactVariation.HorizontalGraphPatch.graphTrace]
    nlinarith [mul_self_pos.mpr hd]
  have hbranchFactor :
      ∀ᶠ q in 𝓝 (C.patch.graphTrace y), 0 < branchFactor q :=
    (isOpen_lt continuous_const hbranchFactorContinuous).mem_nhds
      hbranchFactorBase
  have hcircleFactor (q : PlanePoint)
      (hq : q.2 ∈ Ioo C.patch.a C.patch.b) :
      circleValue center |1 / K| q =
        (q.1 - C.patch.graph q.2) *
          (q.1 + C.patch.graph q.2 - 2 * center.1) := by
    have hgraphSupport :=
      C.patch.closed_graph_circle_identity hcurv hK
        ⟨hy.1.le, hy.2.le⟩ ⟨hq.1.le, hq.2.le⟩
    unfold CMVTransverseContactVariation.HorizontalGraphPatch.supportingCircle
      at hgraphSupport
    simp only [CMVTransverseContactVariation.HorizontalGraphPatch.graphTrace]
      at hgraphSupport
    change (C.patch.graph q.2 - center.1) ^ 2 +
      (q.2 - center.2) ^ 2 =
        (1 / (-(C.patch.side.areaSign * K))) ^ 2 at hgraphSupport
    unfold circleValue
    rw [← hradii]
    nlinarith [hgraphSupport]
  have finish (side : CircleSide)
      (hlocal : ∀ᶠ q in 𝓝 (C.patch.graphTrace y),
        (q ∈ carrier ↔
          side.sign * circleValue center |1 / K| q < 0)) :
      LocallyOneSided carrier center |1 / K| (C.patch.graphTrace y) := by
    rcases _root_.mem_nhds_iff.mp hlocal with
      ⟨V, hVsub, hVopen, hpV⟩
    refine ⟨side, V, hVopen, hpV, ?_⟩
    ext q
    simp only [mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hqCarrier, hqV⟩
      exact ⟨hqV, (hVsub hqV).mp hqCarrier⟩
    · rintro ⟨hqV, hqSide⟩
      exact ⟨(hVsub hqV).mpr hqSide, hqV⟩
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · cases hside : C.patch.side with
    | below =>
        apply finish .outside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumNeg :
            q.1 + C.patch.graph q.2 - 2 * center.1 < 0 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact (hdneg.not_gt hpos.2).elim
          · exact hneg.1
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign,
          CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq]
        constructor
        · intro hleft
          have hpositive := mul_pos_of_neg_of_neg
            (sub_neg.mpr hleft) hsumNeg
          linarith
        · intro hnegative
          by_contra hnotLeft
          have hdiff : 0 ≤ q.1 - C.patch.graph q.2 := by
            linarith
          have hproduct := mul_nonpos_of_nonneg_of_nonpos
            hdiff hsumNeg.le
          linarith
    | above =>
        apply finish .inside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumNeg :
            q.1 + C.patch.graph q.2 - 2 * center.1 < 0 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact (hdneg.not_gt hpos.2).elim
          · exact hneg.1
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign,
          CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq, one_mul]
        constructor
        · intro hright
          exact mul_neg_of_pos_of_neg (sub_pos.mpr hright) hsumNeg
        · intro hnegative
          by_contra hnotRight
          have hdiff : q.1 - C.patch.graph q.2 ≤ 0 := by
            linarith
          have hproduct := mul_nonneg_of_nonpos_of_nonpos
            hdiff hsumNeg.le
          linarith
  · cases hside : C.patch.side with
    | below =>
        apply finish .inside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumPos :
            0 < q.1 + C.patch.graph q.2 - 2 * center.1 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact hpos.1
          · exact (not_lt_of_ge hdpos.le hneg.2).elim
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign,
          CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq, one_mul]
        constructor
        · intro hleft
          exact mul_neg_of_neg_of_pos (sub_neg.mpr hleft) hsumPos
        · intro hnegative
          by_contra hnotLeft
          have hdiff : 0 ≤ q.1 - C.patch.graph q.2 := by
            linarith
          have hproduct := mul_nonneg hdiff hsumPos.le
          linarith
    | above =>
        apply finish .outside
        filter_upwards [hoccupied, hparameter, hbranchFactor] with
            q hqOccupied hqParameter hqBranch
        have hsumPos :
            0 < q.1 + C.patch.graph q.2 - 2 * center.1 := by
          rcases (mul_pos_iff.mp hqBranch) with hpos | hneg
          · exact hpos.1
          · exact (not_lt_of_ge hdpos.le hneg.2).elim
        rw [hqOccupied, hcircleFactor q hqParameter]
        simp only [CircleSide.sign,
          CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
          hside, Set.mem_ofPred_eq]
        constructor
        · intro hright
          have hpositive := mul_pos (sub_pos.mpr hright) hsumPos
          linarith
        · intro hnegative
          by_contra hnotRight
          have hdiff : q.1 - C.patch.graph q.2 ≤ 0 := by
            linarith
          have hproduct := mul_nonpos_of_nonpos_of_nonneg
            hdiff hsumPos.le
          linarith

/-- Every nonzero-curvature base of a truthful mixed atlas has an actual local
one-sided germ for its derived supporting circle.  No orientation or graph axis
is supplied by the caller. -/
theorem mixedAtlas_locallyOneSided_supportingCircle
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p : locus) (hK : K ≠ 0) :
    LocallyOneSided carrier (A.supportingCenterAt p) |1 / K| p.1 := by
  have hbase := A.base_eq p
  have hinterior := A.base_interior p
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      rw [hchart] at hbase hinterior
      simp only [RegularChart.parameter, RegularChart.parameterInterval,
        RegularChart.trace] at hbase hinterior
      have hgerm := locallyOneSided_of_vertical_regularChart C hK hinterior
        hcurv (hoccupied p.1.1 hinterior)
      unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
      rw [hchart]
      simpa only [hbase] using hgerm
  | horizontal C hcurv hoccupied =>
      rw [hchart] at hbase hinterior
      simp only [RegularChart.parameter, RegularChart.parameterInterval,
        RegularChart.trace] at hbase hinterior
      have hgerm := locallyOneSided_of_horizontal_regularChart C hK hinterior
        hcurv (hoccupied p.1.2 hinterior)
      unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
      rw [hchart]
      simpa only [hbase] using hgerm

/-- Selected-representative specialization of the detached-circle exclusion. -/
theorem not_full_circle_frontier_aeOpenRepresentative
    {E U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U) (hUconnected : IsConnected U)
    (hEU : E =ᵐ[volume] U)
    (hsections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    {center : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hcircleFrontier :
      {p : PlanePoint | circleValue center radius p = 0} ⊆
        frontier (CMVRelaxation.aeOpenRepresentative E))
    (hleft : LocallyOneSided
      (CMVRelaxation.aeOpenRepresentative E) center radius
        (center.1 - radius, center.2))
    (hright : LocallyOneSided
      (CMVRelaxation.aeOpenRepresentative E) center radius
        (center.1 + radius, center.2))
    (reach : ∃ q ∈ CMVRelaxation.aeOpenRepresentative E,
      0 ≤ circleValue center radius q) : False := by
  apply not_full_circle_frontier_of_interval_sections_and_reach
    (CMVRelaxation.isOpen_aeOpenRepresentative E)
    (CMVRelaxation.isBounded_aeOpenRepresentative_of_ae hEU hUbounded)
    (CMVRelaxation.isConnected_aeOpenRepresentative_of_open_ae
      hUopen hEU hUconnected)
    (CMVRelaxation.ordConnected_horizontalSection_aeOpenRepresentative
      hUopen hEU hsections)
    hradius hcircleFrontier hleft hright reach

/-- A maximal nonzero-curvature atlas component cannot be the whole supporting
circle under the branch-neutral representative hypotheses and geometric reach. -/
theorem connectedComponentIn_ne_supportAt_of_interval_sections_and_reach
    {U locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas U locus K) (p : locus)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hUconnected : IsConnected U)
    (hsections : ∀ y : ℝ, (horizontalSection U y).OrdConnected)
    (hK : K ≠ 0)
    (hleft : LocallyOneSided U
      ((A.chart p).patch.supportingCenter K p.1.1) |1 / K|
      (((A.chart p).patch.supportingCenter K p.1.1).1 - |1 / K|,
        ((A.chart p).patch.supportingCenter K p.1.1).2))
    (hright : LocallyOneSided U
      ((A.chart p).patch.supportingCenter K p.1.1) |1 / K|
      (((A.chart p).patch.supportingCenter K p.1.1).1 + |1 / K|,
        ((A.chart p).patch.supportingCenter K p.1.1).2))
    (reach : ∃ q ∈ U, 0 ≤ circleValue
      ((A.chart p).patch.supportingCenter K p.1.1) |1 / K| q) :
    connectedComponentIn locus p.1 ≠ A.supportAt p := by
  intro hfull
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hcircleFrontier :
      {q : PlanePoint | circleValue
        ((A.chart p).patch.supportingCenter K p.1.1) |1 / K| q = 0} ⊆
          frontier U := by
    rw [← supportAt_eq_circleValue_zero A p hK, ← hfull]
    exact (connectedComponentIn_subset locus p.1).trans A.locus_subset_frontier
  exact not_full_circle_frontier_of_interval_sections_and_reach
    hUopen hUbounded hUconnected hsections hradius hcircleFrontier
      hleft hright reach

/-! ## Closed/open saturation of actual support components -/

/-- If `F` is ambiently closed, an actual connected component of `F ∩ H`,
viewed inside `H`, is closed.  This is the relative-closedness input used for
exterior loci; it does not assert that the generally open locus `F ∩ H` is
closed in the plane. -/
theorem inclusion_image_connectedComponent_isClosed
    {α : Type*} [TopologicalSpace α] {F H : Set α} (hFclosed : IsClosed F)
    (p : (F ∩ H : Set α)) :
    IsClosed
      (Set.inclusion (show F ∩ H ⊆ H from inter_subset_right) ''
        connectedComponent p) := by
  have hrelative : IsClosed {q : H | q.1 ∈ F ∩ H} := by
    have heq : {q : H | q.1 ∈ F ∩ H} =
        ((↑) : H → α) ⁻¹' F := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_left q.2
    rw [heq]
    exact hFclosed.preimage continuous_subtype_val
  exact (Topology.IsClosedEmbedding.inclusion inter_subset_right hrelative
    ).isClosedMap _ isClosed_connectedComponent

/-- Clopen continuation principle for an actual locus `F ∩ H`.  A component
that is locally saturated in a preconnected support portion and is contained in
that portion equals it.  Ambient closedness of `F` supplies relative
closedness in `H`; no compactness of the open locus is used. -/
theorem connectedComponentIn_eq_supportPortion_of_local_saturation
    {α : Type*} [TopologicalSpace α] {F H S : Set α} {p : α}
    (hFclosed : IsClosed F) (hpLocus : p ∈ F ∩ H)
    (hSH : S ⊆ H) (hpS : p ∈ S)
    (hcomponentSubset : connectedComponentIn (F ∩ H) p ⊆ S)
    (hlocal : ∀ q ∈ connectedComponentIn (F ∩ H) p,
      ∃ W : Set α, IsOpen W ∧ q ∈ W ∧
        S ∩ W ⊆ connectedComponentIn (F ∩ H) p)
    (hSpreconnected : IsPreconnected S) :
    connectedComponentIn (F ∩ H) p = S := by
  let L : Set α := F ∩ H
  let inclusionLH : L → H := Set.inclusion inter_subset_right
  let closedComponentH : Set H :=
    inclusionLH '' connectedComponent (⟨p, hpLocus⟩ : L)
  have hclosedComponentH : IsClosed closedComponentH := by
    exact inclusion_image_connectedComponent_isClosed hFclosed
      (⟨p, hpLocus⟩ : L)
  have mem_closedComponentH_iff (q : H) :
      q ∈ closedComponentH ↔ q.1 ∈ connectedComponentIn L p := by
    rw [connectedComponentIn_eq_image hpLocus]
    constructor
    · rintro ⟨z, hz, hqz⟩
      exact ⟨z, hz, congrArg Subtype.val hqz⟩
    · rintro ⟨z, hz, hqz⟩
      refine ⟨z, hz, Subtype.ext ?_⟩
      exact hqz
  let inclusionSH : S → H := Set.inclusion hSH
  let liftedComponent : Set S := inclusionSH ⁻¹' closedComponentH
  have hliftedClosed : IsClosed liftedComponent :=
    hclosedComponentH.preimage
      (Topology.IsEmbedding.inclusion hSH).continuous
  have hliftedOpen : IsOpen liftedComponent := by
    rw [isOpen_iff_forall_mem_open]
    intro q hq
    have hqComponent : q.1 ∈ connectedComponentIn L p :=
      (mem_closedComponentH_iff (inclusionSH q)).mp hq
    rcases hlocal q.1 hqComponent with ⟨W, hWopen, hqW, hWsubset⟩
    refine ⟨Subtype.val ⁻¹' W, ?_,
      hWopen.preimage continuous_subtype_val, hqW⟩
    intro r hr
    exact (mem_closedComponentH_iff (inclusionSH r)).mpr
      (hWsubset ⟨r.2, hr⟩)
  have hliftedNonempty : liftedComponent.Nonempty := by
    refine ⟨⟨p, hpS⟩, ?_⟩
    exact (mem_closedComponentH_iff (inclusionSH ⟨p, hpS⟩)).mpr
      (mem_connectedComponentIn hpLocus)
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace hSpreconnected
  have hliftedEq : liftedComponent = Set.univ :=
    IsClopen.eq_univ ⟨hliftedClosed, hliftedOpen⟩ hliftedNonempty
  apply Set.Subset.antisymm hcomponentSubset
  intro q hqS
  have hqLifted : (⟨q, hqS⟩ : S) ∈ liftedComponent := by
    rw [hliftedEq]
    exact mem_univ _
  exact (mem_closedComponentH_iff (inclusionSH ⟨q, hqS⟩)).mp hqLifted


private theorem plane_snd_isLinearMap :
    IsLinearMap ℝ (fun q : PlanePoint => q.2) where
  map_add := by intros; rfl
  map_smul := by intros; rfl

private theorem plane_snd_sub_mul_fst_isLinearMap (m : ℝ) :
    IsLinearMap ℝ (fun q : PlanePoint => q.2 - m * q.1) where
  map_add := by
    intros
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul := by
    intros
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

private theorem plane_fst_sub_mul_snd_isLinearMap (m : ℝ) :
    IsLinearMap ℝ (fun q : PlanePoint => q.1 - m * q.2) where
  map_add := by
    intros
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  map_smul := by
    intros
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

theorem verticalAffineLine_inter_upper_isPreconnected
    (b m s interfaceY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  have heq :
      {q : PlanePoint | q.2 = b + m * (q.1 - s)} =
        {q : PlanePoint | q.2 - m * q.1 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact ((convex_hyperplane (plane_snd_sub_mul_fst_isLinearMap m) _).inter
    (convex_halfSpace_gt plane_snd_isLinearMap interfaceY)).isPreconnected

theorem verticalAffineLine_inter_lower_isPreconnected
    (b m s interfaceY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  have heq :
      {q : PlanePoint | q.2 = b + m * (q.1 - s)} =
        {q : PlanePoint | q.2 - m * q.1 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact ((convex_hyperplane (plane_snd_sub_mul_fst_isLinearMap m) _).inter
    (convex_halfSpace_lt plane_snd_isLinearMap interfaceY)).isPreconnected

theorem horizontalAffineLine_inter_upper_isPreconnected
    (b m s interfaceY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  have heq :
      {q : PlanePoint | q.1 = b + m * (q.2 - s)} =
        {q : PlanePoint | q.1 - m * q.2 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact ((convex_hyperplane (plane_fst_sub_mul_snd_isLinearMap m) _).inter
    (convex_halfSpace_gt plane_snd_isLinearMap interfaceY)).isPreconnected

theorem horizontalAffineLine_inter_lower_isPreconnected
    (b m s interfaceY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  have heq :
      {q : PlanePoint | q.1 = b + m * (q.2 - s)} =
        {q : PlanePoint | q.1 - m * q.2 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact ((convex_hyperplane (plane_fst_sub_mul_snd_isLinearMap m) _).inter
    (convex_halfSpace_lt plane_snd_isLinearMap interfaceY)).isPreconnected


/-- Every nonempty upper-half-plane portion of an affine `y = f(x)` support
is unbounded.  The zero-slope case uses its unbounded horizontal coordinate;
otherwise every sufficiently high ordinate is realized. -/
theorem not_isBounded_verticalAffineLine_inter_upper
    (b m s interfaceY : ℝ) (hbase : interfaceY < b) :
    ¬ Bornology.IsBounded
      ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  intro hbounded
  by_cases hm : m = 0
  · obtain ⟨upper, hupper⟩ := hbounded.image_fst.bddAbove
    let x := upper + 1
    have hxmem : x ∈ Prod.fst ''
        ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
          {q : PlanePoint | interfaceY < q.2}) := by
      refine ⟨(x, b), ?_, rfl⟩
      exact ⟨by simp [hm], hbase⟩
    have hxle := hupper hxmem
    dsimp only [x] at hxle
    linarith
  · obtain ⟨upper, hupper⟩ := hbounded.image_snd.bddAbove
    let y := max interfaceY upper + 1
    have hyInterface : interfaceY < y := by
      dsimp only [y]
      linarith [le_max_left interfaceY upper]
    have hyUpper : upper < y := by
      dsimp only [y]
      linarith [le_max_right interfaceY upper]
    have hymem : y ∈ Prod.snd ''
        ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
          {q : PlanePoint | interfaceY < q.2}) := by
      refine ⟨(s + (y - b) / m, y), ?_, rfl⟩
      constructor
      · change y = b + m * (s + (y - b) / m - s)
        field_simp [hm]
        ring
      · exact hyInterface
    exact (not_lt_of_ge (hupper hymem)) hyUpper

/-- Lower-half-plane counterpart of
`not_isBounded_verticalAffineLine_inter_upper`. -/
theorem not_isBounded_verticalAffineLine_inter_lower
    (b m s interfaceY : ℝ) (hbase : b < interfaceY) :
    ¬ Bornology.IsBounded
      ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  intro hbounded
  by_cases hm : m = 0
  · obtain ⟨lower, hlower⟩ := hbounded.image_fst.bddBelow
    let x := lower - 1
    have hxmem : x ∈ Prod.fst ''
        ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
          {q : PlanePoint | q.2 < interfaceY}) := by
      refine ⟨(x, b), ?_, rfl⟩
      exact ⟨by simp [hm], hbase⟩
    have hxge := hlower hxmem
    dsimp only [x] at hxge
    linarith
  · obtain ⟨lower, hlower⟩ := hbounded.image_snd.bddBelow
    let y := min interfaceY lower - 1
    have hyInterface : y < interfaceY := by
      dsimp only [y]
      linarith [min_le_left interfaceY lower]
    have hyLower : y < lower := by
      dsimp only [y]
      linarith [min_le_right interfaceY lower]
    have hymem : y ∈ Prod.snd ''
        ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
          {q : PlanePoint | q.2 < interfaceY}) := by
      refine ⟨(s + (y - b) / m, y), ?_, rfl⟩
      constructor
      · change y = b + m * (s + (y - b) / m - s)
        field_simp [hm]
        ring
      · exact hyInterface
    exact (not_lt_of_ge (hlower hymem)) hyLower

/-- An affine `x = g(y)` support realizes every ordinate, so either exterior
half-plane portion is unbounded independently of its slope. -/
theorem not_isBounded_horizontalAffineLine_inter_upper
    (b m s interfaceY : ℝ) :
    ¬ Bornology.IsBounded
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  intro hbounded
  obtain ⟨upper, hupper⟩ := hbounded.image_snd.bddAbove
  let y := max interfaceY upper + 1
  have hyInterface : interfaceY < y := by
    dsimp only [y]
    linarith [le_max_left interfaceY upper]
  have hyUpper : upper < y := by
    dsimp only [y]
    linarith [le_max_right interfaceY upper]
  have hymem : y ∈ Prod.snd ''
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
    exact ⟨(b + m * (y - s), y), ⟨rfl, hyInterface⟩, rfl⟩
  exact (not_lt_of_ge (hupper hymem)) hyUpper

theorem not_isBounded_horizontalAffineLine_inter_lower
    (b m s interfaceY : ℝ) :
    ¬ Bornology.IsBounded
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  intro hbounded
  obtain ⟨lower, hlower⟩ := hbounded.image_snd.bddBelow
  let y := min interfaceY lower - 1
  have hyInterface : y < interfaceY := by
    dsimp only [y]
    linarith [min_le_left interfaceY lower]
  have hyLower : y < lower := by
    dsimp only [y]
    linarith [min_le_right interfaceY lower]
  have hymem : y ∈ Prod.snd ''
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
    exact ⟨(b + m * (y - s), y), ⟨rfl, hyInterface⟩, rfl⟩
  exact (not_lt_of_ge (hlower hymem)) hyLower

theorem supportAt_inter_upper_isPreconnected_of_eq_zero
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K = 0) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2}) := by
  unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
    RegularChart.supportAtParameter
  rw [if_pos hK]
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      exact verticalAffineLine_inter_upper_isPreconnected
        (C.patch.graph p.1.1) (deriv C.patch.graph p.1.1) p.1.1 interfaceY
  | horizontal C hcurv hoccupied =>
      exact horizontalAffineLine_inter_upper_isPreconnected
        (C.patch.graph p.1.2) (deriv C.patch.graph p.1.2) p.1.2 interfaceY

theorem supportAt_inter_lower_isPreconnected_of_eq_zero
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K = 0) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY}) := by
  unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
    RegularChart.supportAtParameter
  rw [if_pos hK]
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      exact verticalAffineLine_inter_lower_isPreconnected
        (C.patch.graph p.1.1) (deriv C.patch.graph p.1.1) p.1.1 interfaceY
  | horizontal C hcurv hoccupied =>
      exact horizontalAffineLine_inter_lower_isPreconnected
        (C.patch.graph p.1.2) (deriv C.patch.graph p.1.2) p.1.2 interfaceY


/-- Real and imaginary coordinates identify the Euclidean complex plane with
the project's plane-point carrier. -/
def complexToPlane (z : ℂ) : PlanePoint := (z.re, z.im)

theorem continuous_complexToPlane : Continuous complexToPlane := by
  exact Complex.continuous_re.prodMk Complex.continuous_im

/-- A positive-radius Euclidean circle is preconnected. -/
theorem circleValue_zero_isPreconnected
    (center : PlanePoint) {radius : ℝ} (hradius : 0 < radius) :
    IsPreconnected {q : PlanePoint | circleValue center radius q = 0} := by
  let complexCenter : ℂ := ⟨center.1, center.2⟩
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hsphere : IsPreconnected (Metric.sphere complexCenter radius) :=
    isPreconnected_sphere hrank complexCenter radius
  have himage :
      complexToPlane '' Metric.sphere complexCenter radius =
        {q : PlanePoint | circleValue center radius q = 0} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Metric.mem_sphere, Complex.dist_eq] at hz
      have hsq := congrArg (fun x : ℝ => x ^ 2) hz
      rw [Complex.sq_norm, Complex.normSq_apply] at hsq
      unfold complexToPlane circleValue
      unfold complexCenter at hsq
      simp only [Complex.sub_re, Complex.sub_im] at hsq
      change
        (z.re - center.1) ^ 2 + (z.im - center.2) ^ 2 -
          radius ^ 2 = 0
      nlinarith
    · intro hq
      refine ⟨⟨q.1, q.2⟩, ?_, rfl⟩
      rw [Metric.mem_sphere, Complex.dist_eq]
      apply (sq_eq_sq₀ (norm_nonneg _) hradius.le).mp
      rw [Complex.sq_norm, Complex.normSq_apply]
      change circleValue center radius q = 0 at hq
      unfold circleValue at hq
      unfold complexCenter
      simp only [Complex.sub_re, Complex.sub_im]
      nlinarith
  rw [← himage]
  exact hsphere.image _ continuous_complexToPlane.continuousOn

/-- Every point of a positive-radius circle lies between its lower and upper
poles. -/
theorem circleValue_zero_snd_bounds
    {center q : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hq : circleValue center radius q = 0) :
    center.2 - radius ≤ q.2 ∧ q.2 ≤ center.2 + radius := by
  have hsq : (q.2 - center.2) ^ 2 ≤ radius ^ 2 := by
    unfold circleValue at hq
    nlinarith [sq_nonneg (q.1 - center.1)]
  have habs : |q.2 - center.2| ≤ radius := by
    apply (sq_le_sq₀ (abs_nonneg _) hradius.le).mp
    rw [sq_abs]
    exact hsq
  exact ⟨by linarith [(abs_le.mp habs).1],
    by linarith [(abs_le.mp habs).2]⟩

/-- The two algebraic circle points at a horizontal height, before either is
identified with an actual source interface endpoint. -/
def leftCirclePointAtHeight
    (center : PlanePoint) (radius y : ℝ) : PlanePoint :=
  (center.1 - √(radius ^ 2 - (y - center.2) ^ 2), y)

def rightCirclePointAtHeight
    (center : PlanePoint) (radius y : ℝ) : PlanePoint :=
  (center.1 + √(radius ^ 2 - (y - center.2) ^ 2), y)

/-- At every height strictly between the poles, the complete circle has
exactly two ordered points.  This handles minor and major arc heights without
choosing an angle branch. -/
theorem circleValue_zero_and_snd_eq_pair_of_between_poles
    {center : PlanePoint} {radius y : ℝ} (_hradius : 0 < radius)
    (hbottom : center.2 - radius < y)
    (htop : y < center.2 + radius) :
    {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} =
        {leftCirclePointAtHeight center radius y,
          rightCirclePointAtHeight center radius y} ∧
      (leftCirclePointAtHeight center radius y).1 <
        (rightCirclePointAtHeight center radius y).1 := by
  let D := radius ^ 2 - (y - center.2) ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    have hleft : 0 < radius - (y - center.2) := by linarith
    have hright : 0 < radius + (y - center.2) := by linarith
    nlinarith [mul_pos hleft hright]
  have hsqrtPos : 0 < √D := Real.sqrt_pos.2 hD
  have hsqrtSq : (√D) ^ 2 = D := Real.sq_sqrt hD.le
  constructor
  · ext q
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hqCircle, hqy⟩
      have hxSq : (q.1 - center.1) ^ 2 = D := by
        unfold circleValue at hqCircle
        rw [hqy] at hqCircle
        dsimp only [D]
        linarith
      have hxSq' :
          (q.1 - center.1) ^ 2 = (√D) ^ 2 := hxSq.trans hsqrtSq.symm
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hxSq' with hx | hx
      · right
        apply Prod.ext
        · unfold rightCirclePointAtHeight
          dsimp only
          change q.1 = center.1 + √D
          linarith
        · exact hqy
      · left
        apply Prod.ext
        · unfold leftCirclePointAtHeight
          dsimp only
          change q.1 = center.1 - √D
          linarith
        · exact hqy
    · rintro (rfl | rfl)
      · constructor
        · unfold leftCirclePointAtHeight circleValue
          dsimp only
          rw [show radius ^ 2 - (y - center.2) ^ 2 = D from rfl]
          nlinarith [hsqrtSq]
        · rfl
      · constructor
        · unfold rightCirclePointAtHeight circleValue
          dsimp only
          rw [show radius ^ 2 - (y - center.2) ^ 2 = D from rfl]
          nlinarith [hsqrtSq]
        · rfl
  · unfold leftCirclePointAtHeight rightCirclePointAtHeight
    dsimp only
    change center.1 - √D < center.1 + √D
    linarith

/-- At a lower tangency height, the circle/interface contact is the lower pole
and no second endpoint is silently introduced. -/
theorem circleValue_zero_and_snd_eq_singleton_of_lower_tangent
    {center : PlanePoint} {radius y : ℝ}
    (hy : y = center.2 - radius) :
    {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} =
      {(center.1, center.2 - radius)} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hqCircle, hqy⟩
    apply Prod.ext
    · unfold circleValue at hqCircle
      rw [hqy, hy] at hqCircle
      nlinarith [sq_nonneg (q.1 - center.1)]
    · rw [hqy, hy]
  · rintro rfl
    constructor
    · unfold circleValue
      ring
    · exact hy.symm

/-- Upper tangency counterpart. -/
theorem circleValue_zero_and_snd_eq_singleton_of_upper_tangent
    {center : PlanePoint} {radius y : ℝ}
    (hy : y = center.2 + radius) :
    {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} =
      {(center.1, center.2 + radius)} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hqCircle, hqy⟩
    apply Prod.ext
    · unfold circleValue at hqCircle
      rw [hqy, hy] at hqCircle
      nlinarith [sq_nonneg (q.1 - center.1)]
    · rw [hqy, hy]
  · rintro rfl
    constructor
    · unfold circleValue
      ring
    · exact hy.symm

/-- A horizontal line strictly below the lower pole has no circle contact. -/
theorem circleValue_zero_and_snd_eq_empty_of_below_lowerPole
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hy : y < center.2 - radius) :
    {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} = ∅ := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hqCircle, hqy⟩
  have hbound := (circleValue_zero_snd_bounds hradius hqCircle).1
  rw [hqy] at hbound
  linarith

/-- A horizontal line strictly above the upper pole has no circle contact. -/
theorem circleValue_zero_and_snd_eq_empty_of_above_upperPole
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hy : center.2 + radius < y) :
    {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} = ∅ := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hqCircle, hqy⟩
  have hbound := (circleValue_zero_snd_bounds hradius hqCircle).2
  rw [hqy] at hbound
  linarith

/-- Every secant contact, and the coincident lower-pole contact in the tangent
case, is reached from the strict upper circle clip. -/
theorem leftCirclePointAtHeight_mem_closure_upperClip
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hbottom : center.2 - radius ≤ y)
    (htop : y < center.2 + radius) :
    leftCirclePointAtHeight center radius y ∈
      closure ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | y < q.2}) := by
  let gap : ℝ := center.2 + radius - y
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let yseq : ℕ → ℝ := fun n => y + gap / 2 * u n
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaled :
      Tendsto (fun n => gap / 2 * u n) atTop (𝓝 (gap / 2 * 0)) :=
    tendsto_const_nhds.mul hu
  have hyseq : Tendsto yseq atTop (𝓝 y) := by
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) :=
      tendsto_const_nhds
    have hsum := hconst.add hscaled
    simpa only [yseq, mul_zero, add_zero] using hsum
  have hradicand :
      Tendsto
        (fun n => radius ^ 2 - (yseq n - center.2) ^ 2)
        atTop (𝓝 (radius ^ 2 - (y - center.2) ^ 2)) :=
    tendsto_const_nhds.sub
      ((hyseq.sub tendsto_const_nhds).pow 2)
  have hsqrt :
      Tendsto
        (fun n => √(radius ^ 2 - (yseq n - center.2) ^ 2))
        atTop (𝓝 (√(radius ^ 2 - (y - center.2) ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hradicand
  have hpoints :
      Tendsto (fun n => leftCirclePointAtHeight center radius (yseq n))
        atTop (𝓝 (leftCirclePointAtHeight center radius y)) := by
    exact (tendsto_const_nhds.sub hsqrt).prodMk_nhds hyseq
  apply mem_closure_of_tendsto hpoints
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have huPos : 0 < u n := by
    dsimp only [u]
    exact one_div_pos.mpr hn
  have huLe : u n ≤ 1 := by
    dsimp only [u]
    exact (div_le_one hn).2 (by norm_num)
  have hscaledPos : 0 < gap / 2 * u n :=
    mul_pos (by positivity) huPos
  have hscaledLe : gap / 2 * u n ≤ gap / 2 := by
    have hprod : 0 ≤ gap / 2 * (1 - u n) :=
      mul_nonneg (by linarith [hgap]) (sub_nonneg.mpr huLe)
    nlinarith
  have hyStrict : y < yseq n := by
    dsimp only [yseq]
    linarith
  have hyTop : yseq n < center.2 + radius := by
    dsimp only [yseq, gap] at hscaledLe ⊢
    linarith
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius (lt_of_le_of_lt hbottom hyStrict) hyTop
  have hmem :
      leftCirclePointAtHeight center radius (yseq n) ∈
        ({leftCirclePointAtHeight center radius (yseq n),
          rightCirclePointAtHeight center radius (yseq n)} : Set PlanePoint) := by
    exact Set.mem_insert _ _
  rw [← hpair.1] at hmem
  exact ⟨hmem.1, hyStrict⟩

/-- The right contact has the same closure property. -/
theorem rightCirclePointAtHeight_mem_closure_upperClip
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hbottom : center.2 - radius ≤ y)
    (htop : y < center.2 + radius) :
    rightCirclePointAtHeight center radius y ∈
      closure ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | y < q.2}) := by
  let gap : ℝ := center.2 + radius - y
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let yseq : ℕ → ℝ := fun n => y + gap / 2 * u n
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaled :
      Tendsto (fun n => gap / 2 * u n) atTop (𝓝 (gap / 2 * 0)) :=
    tendsto_const_nhds.mul hu
  have hyseq : Tendsto yseq atTop (𝓝 y) := by
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) :=
      tendsto_const_nhds
    have hsum := hconst.add hscaled
    simpa only [yseq, mul_zero, add_zero] using hsum
  have hradicand :
      Tendsto
        (fun n => radius ^ 2 - (yseq n - center.2) ^ 2)
        atTop (𝓝 (radius ^ 2 - (y - center.2) ^ 2)) :=
    tendsto_const_nhds.sub
      ((hyseq.sub tendsto_const_nhds).pow 2)
  have hsqrt :
      Tendsto
        (fun n => √(radius ^ 2 - (yseq n - center.2) ^ 2))
        atTop (𝓝 (√(radius ^ 2 - (y - center.2) ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hradicand
  have hpoints :
      Tendsto (fun n => rightCirclePointAtHeight center radius (yseq n))
        atTop (𝓝 (rightCirclePointAtHeight center radius y)) := by
    exact (tendsto_const_nhds.add hsqrt).prodMk_nhds hyseq
  apply mem_closure_of_tendsto hpoints
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have huPos : 0 < u n := by
    dsimp only [u]
    exact one_div_pos.mpr hn
  have huLe : u n ≤ 1 := by
    dsimp only [u]
    exact (div_le_one hn).2 (by norm_num)
  have hscaledPos : 0 < gap / 2 * u n :=
    mul_pos (by positivity) huPos
  have hscaledLe : gap / 2 * u n ≤ gap / 2 := by
    have hprod : 0 ≤ gap / 2 * (1 - u n) :=
      mul_nonneg (by linarith [hgap]) (sub_nonneg.mpr huLe)
    nlinarith
  have hyStrict : y < yseq n := by
    dsimp only [yseq]
    linarith
  have hyTop : yseq n < center.2 + radius := by
    dsimp only [yseq, gap] at hscaledLe ⊢
    linarith
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius (lt_of_le_of_lt hbottom hyStrict) hyTop
  have hmem :
      rightCirclePointAtHeight center radius (yseq n) ∈
        ({leftCirclePointAtHeight center radius (yseq n),
          rightCirclePointAtHeight center radius (yseq n)} : Set PlanePoint) := by
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  rw [← hpair.1] at hmem
  exact ⟨hmem.1, hyStrict⟩

/-- Lower-clip closure counterpart, including an upper-pole tangency. -/
theorem leftCirclePointAtHeight_mem_closure_lowerClip
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hbottom : center.2 - radius < y)
    (htop : y ≤ center.2 + radius) :
    leftCirclePointAtHeight center radius y ∈
      closure ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < y}) := by
  let gap : ℝ := y - (center.2 - radius)
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let yseq : ℕ → ℝ := fun n => y - gap / 2 * u n
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaled :
      Tendsto (fun n => gap / 2 * u n) atTop (𝓝 (gap / 2 * 0)) :=
    tendsto_const_nhds.mul hu
  have hyseq : Tendsto yseq atTop (𝓝 y) := by
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) :=
      tendsto_const_nhds
    have hdiff := hconst.sub hscaled
    simpa only [yseq, mul_zero, sub_zero] using hdiff
  have hradicand :
      Tendsto
        (fun n => radius ^ 2 - (yseq n - center.2) ^ 2)
        atTop (𝓝 (radius ^ 2 - (y - center.2) ^ 2)) :=
    tendsto_const_nhds.sub
      ((hyseq.sub tendsto_const_nhds).pow 2)
  have hsqrt :
      Tendsto
        (fun n => √(radius ^ 2 - (yseq n - center.2) ^ 2))
        atTop (𝓝 (√(radius ^ 2 - (y - center.2) ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hradicand
  have hpoints :
      Tendsto (fun n => leftCirclePointAtHeight center radius (yseq n))
        atTop (𝓝 (leftCirclePointAtHeight center radius y)) := by
    exact (tendsto_const_nhds.sub hsqrt).prodMk_nhds hyseq
  apply mem_closure_of_tendsto hpoints
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have huPos : 0 < u n := by
    dsimp only [u]
    exact one_div_pos.mpr hn
  have huLe : u n ≤ 1 := by
    dsimp only [u]
    exact (div_le_one hn).2 (by norm_num)
  have hscaledPos : 0 < gap / 2 * u n :=
    mul_pos (by positivity) huPos
  have hscaledLe : gap / 2 * u n ≤ gap / 2 := by
    have hprod : 0 ≤ gap / 2 * (1 - u n) :=
      mul_nonneg (by linarith [hgap]) (sub_nonneg.mpr huLe)
    nlinarith
  have hyStrict : yseq n < y := by
    dsimp only [yseq]
    linarith
  have hyBottom : center.2 - radius < yseq n := by
    dsimp only [yseq, gap] at hscaledLe ⊢
    linarith
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius hyBottom (lt_of_lt_of_le hyStrict htop)
  have hmem :
      leftCirclePointAtHeight center radius (yseq n) ∈
        ({leftCirclePointAtHeight center radius (yseq n),
          rightCirclePointAtHeight center radius (yseq n)} : Set PlanePoint) := by
    exact Set.mem_insert _ _
  rw [← hpair.1] at hmem
  exact ⟨hmem.1, hyStrict⟩

theorem rightCirclePointAtHeight_mem_closure_lowerClip
    {center : PlanePoint} {radius y : ℝ} (hradius : 0 < radius)
    (hbottom : center.2 - radius < y)
    (htop : y ≤ center.2 + radius) :
    rightCirclePointAtHeight center radius y ∈
      closure ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < y}) := by
  let gap : ℝ := y - (center.2 - radius)
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let yseq : ℕ → ℝ := fun n => y - gap / 2 * u n
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaled :
      Tendsto (fun n => gap / 2 * u n) atTop (𝓝 (gap / 2 * 0)) :=
    tendsto_const_nhds.mul hu
  have hyseq : Tendsto yseq atTop (𝓝 y) := by
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 y) :=
      tendsto_const_nhds
    have hdiff := hconst.sub hscaled
    simpa only [yseq, mul_zero, sub_zero] using hdiff
  have hradicand :
      Tendsto
        (fun n => radius ^ 2 - (yseq n - center.2) ^ 2)
        atTop (𝓝 (radius ^ 2 - (y - center.2) ^ 2)) :=
    tendsto_const_nhds.sub
      ((hyseq.sub tendsto_const_nhds).pow 2)
  have hsqrt :
      Tendsto
        (fun n => √(radius ^ 2 - (yseq n - center.2) ^ 2))
        atTop (𝓝 (√(radius ^ 2 - (y - center.2) ^ 2))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hradicand
  have hpoints :
      Tendsto (fun n => rightCirclePointAtHeight center radius (yseq n))
        atTop (𝓝 (rightCirclePointAtHeight center radius y)) := by
    exact (tendsto_const_nhds.add hsqrt).prodMk_nhds hyseq
  apply mem_closure_of_tendsto hpoints
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have huPos : 0 < u n := by
    dsimp only [u]
    exact one_div_pos.mpr hn
  have huLe : u n ≤ 1 := by
    dsimp only [u]
    exact (div_le_one hn).2 (by norm_num)
  have hscaledPos : 0 < gap / 2 * u n :=
    mul_pos (by positivity) huPos
  have hscaledLe : gap / 2 * u n ≤ gap / 2 := by
    have hprod : 0 ≤ gap / 2 * (1 - u n) :=
      mul_nonneg (by linarith [hgap]) (sub_nonneg.mpr huLe)
    nlinarith
  have hyStrict : yseq n < y := by
    dsimp only [yseq]
    linarith
  have hyBottom : center.2 - radius < yseq n := by
    dsimp only [yseq, gap] at hscaledLe ⊢
    linarith
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius hyBottom (lt_of_lt_of_le hyStrict htop)
  have hmem :
      rightCirclePointAtHeight center radius (yseq n) ∈
        ({leftCirclePointAtHeight center radius (yseq n),
          rightCirclePointAtHeight center radius (yseq n)} : Set PlanePoint) := by
    exact Set.mem_insert_iff.mpr (Or.inr rfl)
  rw [← hpair.1] at hmem
  exact ⟨hmem.1, hyStrict⟩



/-- Equal positive-radius circle zero sets have the same center.  Four literal
axis points make the center recovery independent of any arc parameterization. -/
theorem circleValue_zero_set_center_injective
    {center₁ center₂ : PlanePoint} {radius : ℝ} (hradius : 0 < radius)
    (hcircles :
      {q : PlanePoint | circleValue center₁ radius q = 0} =
        {q : PlanePoint | circleValue center₂ radius q = 0}) :
    center₁ = center₂ := by
  have hright₁ :
      circleValue center₁ radius (center₁.1 + radius, center₁.2) = 0 := by
    unfold circleValue
    ring
  have hleft₁ :
      circleValue center₁ radius (center₁.1 - radius, center₁.2) = 0 := by
    unfold circleValue
    ring
  have hup₁ :
      circleValue center₁ radius (center₁.1, center₁.2 + radius) = 0 := by
    unfold circleValue
    ring
  have hdown₁ :
      circleValue center₁ radius (center₁.1, center₁.2 - radius) = 0 := by
    unfold circleValue
    ring
  have hright₂ :
      circleValue center₂ radius (center₁.1 + radius, center₁.2) = 0 := by
    change (center₁.1 + radius, center₁.2) ∈
      {q : PlanePoint | circleValue center₂ radius q = 0}
    rw [← hcircles]
    exact hright₁
  have hleft₂ :
      circleValue center₂ radius (center₁.1 - radius, center₁.2) = 0 := by
    change (center₁.1 - radius, center₁.2) ∈
      {q : PlanePoint | circleValue center₂ radius q = 0}
    rw [← hcircles]
    exact hleft₁
  have hup₂ :
      circleValue center₂ radius (center₁.1, center₁.2 + radius) = 0 := by
    change (center₁.1, center₁.2 + radius) ∈
      {q : PlanePoint | circleValue center₂ radius q = 0}
    rw [← hcircles]
    exact hup₁
  have hdown₂ :
      circleValue center₂ radius (center₁.1, center₁.2 - radius) = 0 := by
    change (center₁.1, center₁.2 - radius) ∈
      {q : PlanePoint | circleValue center₂ radius q = 0}
    rw [← hcircles]
    exact hdown₁
  unfold circleValue at hright₂ hleft₂ hup₂ hdown₂
  apply Prod.ext
  · nlinarith
  · nlinarith

/-- A one-variable sublevel `{t | c*t² < d}` is preconnected whenever the
quadratic coefficient is nonnegative.  Empty, all-line, and bounded-interval
cases are kept separate. -/
theorem quadratic_lt_isPreconnected {c d : ℝ} (hc : 0 ≤ c) :
    IsPreconnected {t : ℝ | c * t ^ 2 < d} := by
  by_cases hc0 : c = 0
  · subst c
    by_cases hd : 0 < d
    · have heq : {t : ℝ | 0 * t ^ 2 < d} = Set.univ := by
        ext t
        simp only [zero_mul, Set.mem_ofPred_eq, Set.mem_univ]
        exact iff_true_intro hd
      rw [heq]
      exact isPreconnected_univ
    · have heq : {t : ℝ | 0 * t ^ 2 < d} = ∅ := by
        ext t
        simp only [zero_mul, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        exact not_lt.mpr (le_of_not_gt hd)
      rw [heq]
      exact isPreconnected_empty
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    by_cases hd : 0 < d
    · have hratio : 0 < d / c := div_pos hd hcpos
      have hsqrt : 0 < √(d / c) := Real.sqrt_pos.2 hratio
      have hsqrtSq : (√(d / c)) ^ 2 = d / c := Real.sq_sqrt hratio.le
      have heq : {t : ℝ | c * t ^ 2 < d} =
          Ioo (-√(d / c)) (√(d / c)) := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
        constructor
        · intro ht
          have htSq : t ^ 2 < (√(d / c)) ^ 2 := by
            rw [hsqrtSq]
            exact (lt_div_iff₀ hcpos).2 (by nlinarith [ht])
          constructor <;> nlinarith [sq_nonneg (t + √(d / c)),
            sq_nonneg (t - √(d / c))]
        · intro ht
          have htSq : t ^ 2 < (√(d / c)) ^ 2 := by nlinarith
          rw [hsqrtSq] at htSq
          simpa only [mul_comm] using (lt_div_iff₀ hcpos).mp htSq
      rw [heq]
      exact isPreconnected_Ioo
    · have hdnonpos : d ≤ 0 := le_of_not_gt hd
      have heq : {t : ℝ | c * t ^ 2 < d} = ∅ := by
        ext t
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_lt.mpr
          (hdnonpos.trans (mul_nonneg hc (sq_nonneg t)))
      rw [heq]
      exact isPreconnected_empty

/-- Rational parametrization of a circle with the lower pole omitted. -/
def upperCircleRationalParam (center : PlanePoint) (radius t : ℝ) :
    PlanePoint :=
  (center.1 + 2 * radius * t / (1 + t ^ 2),
    center.2 + radius * (1 - t ^ 2) / (1 + t ^ 2))

theorem continuous_upperCircleRationalParam (center : PlanePoint)
    (radius : ℝ) :
    Continuous (upperCircleRationalParam center radius) := by
  apply Continuous.prodMk
  · exact continuous_const.add
      ((continuous_const.mul continuous_id).div
        (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))
  · exact continuous_const.add
      ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).div
        (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))

theorem upperCircleRationalParam_height_iff
    {center : PlanePoint} {radius interfaceY t : ℝ} :
    interfaceY < (upperCircleRationalParam center radius t).2 ↔
      (interfaceY - center.2 + radius) * t ^ 2 <
        center.2 + radius - interfaceY := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  unfold upperCircleRationalParam
  dsimp only
  constructor <;> intro h
  · have h' :
        interfaceY - center.2 < radius * (1 - t ^ 2) / (1 + t ^ 2) := by
      linarith
    have hcleared := (lt_div_iff₀ hden).mp h'
    nlinarith
  · have hcleared :
        (interfaceY - center.2) * (1 + t ^ 2) <
          radius * (1 - t ^ 2) := by
      nlinarith
    have h' := (lt_div_iff₀ hden).mpr hcleared
    linarith

theorem upperCircleRationalParam_mem_circle
    (center : PlanePoint) (radius t : ℝ) :
    circleValue center radius (upperCircleRationalParam center radius t) = 0 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold circleValue upperCircleRationalParam
  dsimp only
  field_simp [hden]
  ring

theorem upperCircleRationalParam_surjective_of_above_bottom
    {center q : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) (hbottom : center.2 - radius ≤ interfaceY)
    (hqCircle : circleValue center radius q = 0)
    (hqAbove : interfaceY < q.2) :
    ∃ t : ℝ, upperCircleRationalParam center radius t = q := by
  let X := q.1 - center.1
  let Y := q.2 - center.2
  let D := radius + Y
  have hD : 0 < D := by
    dsimp only [D, Y]
    linarith
  have hcircle : X ^ 2 + Y ^ 2 = radius ^ 2 := by
    unfold circleValue at hqCircle
    dsimp only [X, Y]
    linarith
  have hdenIdentity :
      1 + (X / D) ^ 2 = 2 * radius / D := by
    field_simp [ne_of_gt hD]
    nlinarith [hcircle]
  have hnumIdentity :
      1 - (X / D) ^ 2 = 2 * Y / D := by
    field_simp [ne_of_gt hD]
    nlinarith [hcircle]
  let t := X / D
  refine ⟨t, ?_⟩
  apply Prod.ext
  · change center.1 + 2 * radius * (X / D) /
      (1 + (X / D) ^ 2) = q.1
    rw [hdenIdentity]
    field_simp [ne_of_gt hD, ne_of_gt hradius]
    dsimp only [X]
    ring
  · change center.2 + radius * (1 - (X / D) ^ 2) /
      (1 + (X / D) ^ 2) = q.2
    rw [hdenIdentity, hnumIdentity]
    field_simp [ne_of_gt hD, ne_of_gt hradius]
    dsimp only [Y]
    ring

/-- A non-detached upper circular support portion is preconnected.  One
rational chart covers the circle minus its lower pole, which the strict
half-plane excludes.  The theorem includes secant and tangent clips and both
minor and major arcs. -/
theorem circleValue_zero_inter_upper_isPreconnected_of_bottom_le
    {center : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) (hbottom : center.2 - radius ≤ interfaceY) :
    IsPreconnected
      ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  let parameters : Set ℝ :=
    {t | (interfaceY - center.2 + radius) * t ^ 2 <
      center.2 + radius - interfaceY}
  have hcoefficient : 0 ≤ interfaceY - center.2 + radius := by linarith
  have hparameters : IsPreconnected parameters :=
    quadratic_lt_isPreconnected hcoefficient
  have himage :
      upperCircleRationalParam center radius '' parameters =
        {q : PlanePoint | circleValue center radius q = 0} ∩
          {q : PlanePoint | interfaceY < q.2} := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨upperCircleRationalParam_mem_circle center radius t,
        upperCircleRationalParam_height_iff.mpr ht⟩
    · intro hq
      obtain ⟨t, htq⟩ :=
        upperCircleRationalParam_surjective_of_above_bottom hradius hbottom
          hq.1 hq.2
      refine ⟨t, ?_, htq⟩
      apply upperCircleRationalParam_height_iff.mp
      rw [htq]
      exact hq.2
  rw [← himage]
  exact hparameters.image _
    (continuous_upperCircleRationalParam _ _).continuousOn

/-- Rational parametrization of a circle with the upper pole omitted. -/
def lowerCircleRationalParam (center : PlanePoint) (radius t : ℝ) :
    PlanePoint :=
  (center.1 + 2 * radius * t / (1 + t ^ 2),
    center.2 - radius * (1 - t ^ 2) / (1 + t ^ 2))

theorem continuous_lowerCircleRationalParam (center : PlanePoint)
    (radius : ℝ) :
    Continuous (lowerCircleRationalParam center radius) := by
  apply Continuous.prodMk
  · exact continuous_const.add
      ((continuous_const.mul continuous_id).div
        (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))
  · exact continuous_const.sub
      ((continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).div
        (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))

theorem lowerCircleRationalParam_height_iff
    {center : PlanePoint} {radius interfaceY t : ℝ} :
    (lowerCircleRationalParam center radius t).2 < interfaceY ↔
      (center.2 - interfaceY + radius) * t ^ 2 <
        interfaceY - center.2 + radius := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  unfold lowerCircleRationalParam
  dsimp only
  constructor <;> intro h
  · have h' :
        center.2 - interfaceY < radius * (1 - t ^ 2) / (1 + t ^ 2) := by
      linarith
    have hcleared := (lt_div_iff₀ hden).mp h'
    nlinarith
  · have hcleared :
        (center.2 - interfaceY) * (1 + t ^ 2) <
          radius * (1 - t ^ 2) := by
      nlinarith
    have h' := (lt_div_iff₀ hden).mpr hcleared
    linarith

theorem lowerCircleRationalParam_mem_circle
    (center : PlanePoint) (radius t : ℝ) :
    circleValue center radius (lowerCircleRationalParam center radius t) = 0 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold circleValue lowerCircleRationalParam
  dsimp only
  field_simp [hden]
  ring

theorem lowerCircleRationalParam_surjective_of_below_top
    {center q : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) (htop : interfaceY ≤ center.2 + radius)
    (hqCircle : circleValue center radius q = 0)
    (hqBelow : q.2 < interfaceY) :
    ∃ t : ℝ, lowerCircleRationalParam center radius t = q := by
  have hreflectedCircle :
      circleValue (center.1, -center.2) radius (q.1, -q.2) = 0 := by
    unfold circleValue at hqCircle ⊢
    dsimp only
    nlinarith
  obtain ⟨t, ht⟩ :=
    upperCircleRationalParam_surjective_of_above_bottom
      (center := (center.1, -center.2)) (q := (q.1, -q.2))
      (interfaceY := -interfaceY) hradius (by dsimp only; linarith)
      hreflectedCircle (by dsimp only; linarith)
  refine ⟨t, ?_⟩
  apply Prod.ext
  · simpa only [upperCircleRationalParam, lowerCircleRationalParam,
      Prod.fst] using congrArg Prod.fst ht
  · have hy := congrArg Prod.snd ht
    dsimp only [upperCircleRationalParam, lowerCircleRationalParam,
      Prod.snd] at hy ⊢
    linarith

/-- Lower circular support clip, including minor, major, secant, and tangent
cases, is preconnected whenever the interface is no higher than the upper
pole. -/
theorem circleValue_zero_inter_lower_isPreconnected_of_le_top
    {center : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) (htop : interfaceY ≤ center.2 + radius) :
    IsPreconnected
      ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  let parameters : Set ℝ :=
    {t | (center.2 - interfaceY + radius) * t ^ 2 <
      interfaceY - center.2 + radius}
  have hcoefficient : 0 ≤ center.2 - interfaceY + radius := by linarith
  have hparameters : IsPreconnected parameters :=
    quadratic_lt_isPreconnected hcoefficient
  have himage :
      lowerCircleRationalParam center radius '' parameters =
        {q : PlanePoint | circleValue center radius q = 0} ∩
          {q : PlanePoint | q.2 < interfaceY} := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨lowerCircleRationalParam_mem_circle center radius t,
        lowerCircleRationalParam_height_iff.mpr ht⟩
    · intro hq
      obtain ⟨t, htq⟩ :=
        lowerCircleRationalParam_surjective_of_below_top hradius htop
          hq.1 hq.2
      refine ⟨t, ?_, htq⟩
      apply lowerCircleRationalParam_height_iff.mp
      rw [htq]
      exact hq.2
  rw [← himage]
  exact hparameters.image _
    (continuous_lowerCircleRationalParam _ _).continuousOn

/-- Every upper open-half-plane clip of a positive-radius circle is
preconnected.  If the interface misses below the circle, the clip is the full
circle; otherwise the rational chart excludes the lower pole. -/
theorem circleValue_zero_inter_upper_isPreconnected
    {center : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) :
    IsPreconnected
      ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | interfaceY < q.2}) := by
  by_cases hbottom : center.2 - radius ≤ interfaceY
  · exact circleValue_zero_inter_upper_isPreconnected_of_bottom_le
      hradius hbottom
  · rw [inter_eq_left.mpr]
    · exact circleValue_zero_isPreconnected center hradius
    · intro q hq
      exact (lt_of_not_ge hbottom).trans_le
        (circleValue_zero_snd_bounds hradius hq).1

/-- Every lower open-half-plane clip of a positive-radius circle is
preconnected, including the full-circle detached case. -/
theorem circleValue_zero_inter_lower_isPreconnected
    {center : PlanePoint} {radius interfaceY : ℝ}
    (hradius : 0 < radius) :
    IsPreconnected
      ({q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < interfaceY}) := by
  by_cases htop : interfaceY ≤ center.2 + radius
  · exact circleValue_zero_inter_lower_isPreconnected_of_le_top hradius htop
  · rw [inter_eq_left.mpr]
    · exact circleValue_zero_isPreconnected center hradius
    · intro q hq
      exact (circleValue_zero_snd_bounds hradius hq).2.trans_lt
        (lt_of_not_ge htop)
/-- Exact saturation of one derived support portion in an actual locus
`frontier carrier ∩ H`.  Local mixed-chart equations prove relative openness;
closedness comes from `frontier carrier`, and connectedness of the geometric
support portion is the only remaining shape-specific input. -/
theorem connectedComponentIn_eq_supportAt_inter_of_isPreconnected
    {carrier H : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier (frontier carrier ∩ H) K)
    (p : (frontier carrier ∩ H : Set PlanePoint))
    (hpreconnected : IsPreconnected (A.supportAt p ∩ H)) :
    connectedComponentIn (frontier carrier ∩ H) p.1 =
      A.supportAt p ∩ H := by
  apply connectedComponentIn_eq_supportPortion_of_local_saturation
    isClosed_frontier p.2 inter_subset_right
    ⟨A.base_mem_supportAt p, p.2.2⟩
  · intro q hq
    refine ⟨A.connectedComponentIn_subset_supportAt p hq, ?_⟩
    exact (connectedComponentIn_subset (frontier carrier ∩ H) p.1 hq).2
  · intro q hq
    have hqAmbient := hq
    rw [connectedComponentIn_eq_image p.2] at hq
    rcases hq with ⟨q', hqComponent, rfl⟩
    have hsupportEq : A.supportAt q' = A.supportAt p :=
      A.supportAt_eq_of_mem_connectedComponent p q' hqComponent
    rcases A.exists_open_supportAt_inter_subset_connectedComponentIn q' with
      ⟨W, hWopen, hqW, hWsubset⟩
    refine ⟨W, hWopen, hqW, ?_⟩
    intro z hz
    have hzSupportQ : z ∈ A.supportAt q' := by
      rw [hsupportEq]
      exact hz.1.1
    have hzComponentQ := hWsubset ⟨hzSupportQ, hz.2⟩
    have hcomponentEq :
        connectedComponentIn (frontier carrier ∩ H) p.1 =
          connectedComponentIn (frontier carrier ∩ H) q'.1 :=
      connectedComponentIn_eq hqAmbient
    rw [hcomponentEq]
    exact hzComponentQ
  · exact hpreconnected


/-- Curved upper support clips are preconnected once the interface is not
strictly below the support's lower pole. -/
theorem supportAt_inter_upper_isPreconnected_of_ne_zero_of_bottom_le
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0)
    (hbottom : (A.supportingCenterAt p).2 - |1 / K| ≤ interfaceY) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2}) := by
  rw [A.supportAt_eq_circleValue_zero p hK]
  exact circleValue_zero_inter_upper_isPreconnected_of_bottom_le
    (abs_pos.mpr (one_div_ne_zero hK)) hbottom

/-- Every nonzero-curvature upper support clip is preconnected, including
minor, major, tangent, secant, and detached full-circle alternatives. -/
theorem supportAt_inter_upper_isPreconnected_of_ne_zero
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2}) := by
  rw [A.supportAt_eq_circleValue_zero p hK]
  exact circleValue_zero_inter_upper_isPreconnected
    (abs_pos.mpr (one_div_ne_zero hK))

/-- Exact saturation of the actual upper exterior component in every
nonzero-curvature geometric alternative. -/
theorem upperExterior_connectedComponentIn_eq_supportAt_of_ne_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2} := by
  apply connectedComponentIn_eq_supportAt_inter_of_isPreconnected
  exact supportAt_inter_upper_isPreconnected_of_ne_zero A p hK

/-- Any actual interface contact on a nonzero support proves that the
interface is above its lower pole.  No pole point or curvature sign is
supplied. -/
theorem supportingCenterAt_sub_radius_le_interface_of_contact
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    (A.supportingCenterAt p).2 - |1 / K| ≤ interfaceY := by
  rw [A.supportAt_eq_circleValue_zero p hK] at hcontact
  change circleValue (A.supportingCenterAt p) |1 / K| contact = 0
    at hcontact
  unfold circleValue at hcontact
  rw [hheight] at hcontact
  by_contra hbottom
  have hlt :
      interfaceY < (A.supportingCenterAt p).2 - |1 / K| :=
    lt_of_not_ge hbottom
  have hfirst :
      interfaceY - (A.supportingCenterAt p).2 - |1 / K| < 0 := by
    linarith [abs_nonneg (1 / K)]
  have hsecond :
      interfaceY - (A.supportingCenterAt p).2 + |1 / K| < 0 := by
    linarith
  have hsq :
      |1 / K| ^ 2 <
        (interfaceY - (A.supportingCenterAt p).2) ^ 2 := by
    nlinarith [mul_pos_of_neg_of_neg hfirst hsecond]
  nlinarith [sq_nonneg
    (contact.1 - (A.supportingCenterAt p).1)]

/-- Exact upper exterior-component saturation in the nonzero-curvature branch
from one derived support contact with the interface.  Secant and tangent
contacts are both admitted; no minor/major choice or pole geometry occurs. -/
theorem upperExterior_connectedComponentIn_eq_supportAt_of_circle_contact
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2} := by
  apply connectedComponentIn_eq_supportAt_inter_of_isPreconnected
  exact supportAt_inter_upper_isPreconnected_of_ne_zero_of_bottom_le
    A p hK
      (supportingCenterAt_sub_radius_le_interface_of_contact
        A p hK hcontact hheight)

/-- Literal-circle form of upper component saturation. -/
theorem upperExterior_connectedComponentIn_eq_circle_of_contact
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
        {q : PlanePoint | interfaceY < q.2} := by
  rw [upperExterior_connectedComponentIn_eq_supportAt_of_circle_contact
    A p hK hcontact hheight, A.supportAt_eq_circleValue_zero p hK]
/-- Upper-exterior specialization.  Contacts on `y = interfaceY` are excluded
from the open locus and remain available only through component closure. -/
theorem upperExterior_connectedComponentIn_eq_supportAt_of_isPreconnected
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hpreconnected : IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2})) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2} :=
  connectedComponentIn_eq_supportAt_inter_of_isPreconnected A p hpreconnected

/-- Lower-exterior counterpart of exact support saturation. -/
theorem lowerExterior_connectedComponentIn_eq_supportAt_of_isPreconnected
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hpreconnected : IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY})) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY} :=
  connectedComponentIn_eq_supportAt_inter_of_isPreconnected A p hpreconnected

/-- Exact upper exterior-component saturation in the flat-line branch. -/
theorem upperExterior_connectedComponentIn_eq_supportAt_of_eq_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K = 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2} := by
  apply upperExterior_connectedComponentIn_eq_supportAt_of_isPreconnected
  exact supportAt_inter_upper_isPreconnected_of_eq_zero A p hK

/-- Exact lower exterior-component saturation in the flat-line branch. -/
theorem lowerExterior_connectedComponentIn_eq_supportAt_of_eq_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K = 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY} := by
  apply lowerExterior_connectedComponentIn_eq_supportAt_of_isPreconnected
  exact supportAt_inter_lower_isPreconnected_of_eq_zero A p hK

/-- Curved lower support clips are preconnected once the interface is not
strictly above the support's upper pole. -/
theorem supportAt_inter_lower_isPreconnected_of_ne_zero_of_le_top
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0)
    (htop : interfaceY ≤ (A.supportingCenterAt p).2 + |1 / K|) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY}) := by
  rw [A.supportAt_eq_circleValue_zero p hK]
  exact circleValue_zero_inter_lower_isPreconnected_of_le_top
    (abs_pos.mpr (one_div_ne_zero hK)) htop

/-- Every nonzero-curvature lower support clip is preconnected, including the
detached full-circle alternative. -/
theorem supportAt_inter_lower_isPreconnected_of_ne_zero
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) :
    IsPreconnected
      (A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY}) := by
  rw [A.supportAt_eq_circleValue_zero p hK]
  exact circleValue_zero_inter_lower_isPreconnected
    (abs_pos.mpr (one_div_ne_zero hK))

/-- Exact saturation of the actual lower exterior component in every
nonzero-curvature geometric alternative. -/
theorem lowerExterior_connectedComponentIn_eq_supportAt_of_ne_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY} := by
  apply connectedComponentIn_eq_supportAt_inter_of_isPreconnected
  exact supportAt_inter_lower_isPreconnected_of_ne_zero A p hK

/-- Unconditional upper exterior-component saturation.  The proof retains the
flat-line and positive-radius circle branches until their separate
preconnectedness results discharge both. -/
theorem upperExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2} := by
  rcases eq_or_ne K 0 with hK | hK
  · exact upperExterior_connectedComponentIn_eq_supportAt_of_eq_zero A p hK
  · exact upperExterior_connectedComponentIn_eq_supportAt_of_ne_zero A p hK

/-- Unconditional lower exterior-component saturation, with the same explicit
line/circle cutover. -/
theorem lowerExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY} := by
  rcases eq_or_ne K 0 with hK | hK
  · exact lowerExterior_connectedComponentIn_eq_supportAt_of_eq_zero A p hK
  · exact lowerExterior_connectedComponentIn_eq_supportAt_of_ne_zero A p hK

/-- Boundedness of the actual carrier discharges the flat-line alternative on
every nonempty upper exterior component.  The argument uses exact component
saturation; boundedness is never misapplied as compactness of the open locus. -/
theorem commonCurvature_ne_zero_of_bounded_upperExterior
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    K ≠ 0 := by
  intro hK
  have hfrontierBounded : Bornology.IsBounded (frontier carrier) :=
    hcarrierBounded.closure.subset frontier_subset_closure
  have hcomponentBounded : Bornology.IsBounded
      (connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) := by
    apply hfrontierBounded.subset
    exact (connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1
      ).trans inter_subset_left
  rw [upperExterior_connectedComponentIn_eq_supportAt A p] at hcomponentBounded
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      have hsupport :
          A.supportAt p = C.patch.supportingLineAt p.1.1 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK]
        simp only [hchart, RegularChart.parameter]
      rw [hsupport] at hcomponentBounded
      have hbase := A.base_eq p
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace,
        GraphPatch.graphTrace] at hbase
      have hgraph : C.patch.graph p.1.1 = p.1.2 :=
        congrArg Prod.snd hbase
      apply not_isBounded_verticalAffineLine_inter_upper
        (C.patch.graph p.1.1) (deriv C.patch.graph p.1.1) p.1.1 interfaceY
      · rw [hgraph]
        exact p.2.2
      · exact hcomponentBounded
  | horizontal C hcurv hoccupied =>
      have hsupport :
          A.supportAt p = C.patch.supportingLineAt p.1.2 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK]
        simp only [hchart, RegularChart.parameter]
      rw [hsupport] at hcomponentBounded
      exact not_isBounded_horizontalAffineLine_inter_upper
        (C.patch.graph p.1.2) (deriv C.patch.graph p.1.2) p.1.2 interfaceY
          hcomponentBounded

/-- The same boundedness argument discharges zero curvature on every nonempty
lower exterior component. -/
theorem commonCurvature_ne_zero_of_bounded_lowerExterior
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    K ≠ 0 := by
  intro hK
  have hfrontierBounded : Bornology.IsBounded (frontier carrier) :=
    hcarrierBounded.closure.subset frontier_subset_closure
  have hcomponentBounded : Bornology.IsBounded
      (connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) := by
    apply hfrontierBounded.subset
    exact (connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1
      ).trans inter_subset_left
  rw [lowerExterior_connectedComponentIn_eq_supportAt A p] at hcomponentBounded
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      have hsupport :
          A.supportAt p = C.patch.supportingLineAt p.1.1 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK]
        simp only [hchart, RegularChart.parameter]
      rw [hsupport] at hcomponentBounded
      have hbase := A.base_eq p
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace,
        GraphPatch.graphTrace] at hbase
      have hgraph : C.patch.graph p.1.1 = p.1.2 :=
        congrArg Prod.snd hbase
      apply not_isBounded_verticalAffineLine_inter_lower
        (C.patch.graph p.1.1) (deriv C.patch.graph p.1.1) p.1.1 interfaceY
      · rw [hgraph]
        exact p.2.2
      · exact hcomponentBounded
  | horizontal C hcurv hoccupied =>
      have hsupport :
          A.supportAt p = C.patch.supportingLineAt p.1.2 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK]
        simp only [hchart, RegularChart.parameter]
      rw [hsupport] at hcomponentBounded
      exact not_isBounded_horizontalAffineLine_inter_lower
        (C.patch.graph p.1.2) (deriv C.patch.graph p.1.2) p.1.2 interfaceY
          hcomponentBounded


/-- Closing the exact upper component incorporates interface contacts through
the support-portion closure; no chart at a contact is required. -/
theorem closure_upperExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    closure
        (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) =
      closure (A.supportAt p ∩ {q : PlanePoint | interfaceY < q.2}) :=
  congrArg closure (upperExterior_connectedComponentIn_eq_supportAt A p)

/-- Lower interface contacts are likewise recovered only after taking the
component closure, independently of regularity at the interface. -/
theorem closure_lowerExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    closure
        (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) =
      closure (A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY}) :=
  congrArg closure (lowerExterior_connectedComponentIn_eq_supportAt A p)

/-- Literal-circle form of exact upper saturation, with no supplied interface
contacts or minor/major selection. -/
theorem upperExterior_connectedComponentIn_eq_circle_of_ne_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
        {q : PlanePoint | interfaceY < q.2} := by
  rw [upperExterior_connectedComponentIn_eq_supportAt_of_ne_zero A p hK,
    A.supportAt_eq_circleValue_zero p hK]

/-- Literal-circle form of exact lower saturation, again without supplied
interface contacts. -/
theorem lowerExterior_connectedComponentIn_eq_circle_of_ne_zero
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
        {q : PlanePoint | q.2 < interfaceY} := by
  rw [lowerExterior_connectedComponentIn_eq_supportAt_of_ne_zero A p hK,
    A.supportAt_eq_circleValue_zero p hK]

/-- The literal circle center is constant on an actual nonzero-curvature mixed
atlas component.  This is derived from support continuation and circle-center
injectivity, not stored in the atlas. -/
theorem supportingCenterAt_eq_of_mem_connectedComponent
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p q : locus) (hK : K ≠ 0) (hq : q ∈ connectedComponent p) :
    A.supportingCenterAt q = A.supportingCenterAt p := by
  have hsupport := A.supportAt_eq_of_mem_connectedComponent p q hq
  rw [A.supportAt_eq_circleValue_zero q hK,
    A.supportAt_eq_circleValue_zero p hK] at hsupport
  exact circleValue_zero_set_center_injective
    (abs_pos.mpr (one_div_ne_zero hK)) hsupport

/-- Every point of a mixed continuation component inherits the truthful local
one-sided germ for the component's propagated supporting circle. -/
theorem mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p : locus) (hK : K ≠ 0) {q : PlanePoint}
    (hq : q ∈ connectedComponentIn locus p.1) :
    LocallyOneSided carrier (A.supportingCenterAt p) |1 / K| q := by
  have hqImage :
      q ∈ ((↑) : locus → PlanePoint) '' connectedComponent p := by
    rwa [← connectedComponentIn_eq_image p.2]
  rcases hqImage with ⟨q', hq'Connected, hq'Value⟩
  have hgerm :=
    mixedAtlas_locallyOneSided_supportingCircle A q' hK
  have hcenter :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A p q' hK hq'Connected
  rw [hcenter, hq'Value] at hgerm
  exact hgerm


/-- Pole of the literal supporting circle selected by an upper exterior
component.  It is derived from the actual mixed chart rather than supplied as
source geometry. -/
def upperSupportingPole
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    PlanePoint :=
  ((A.supportingCenterAt p).1,
    (A.supportingCenterAt p).2 + |1 / K|)

/-- Lower pole of the same derived support. -/
def lowerSupportingPole
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    PlanePoint :=
  ((A.supportingCenterAt p).1,
    (A.supportingCenterAt p).2 - |1 / K|)

theorem upperSupportingPole_mem_circle
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    circleValue (A.supportingCenterAt p) |1 / K|
      (upperSupportingPole A p) = 0 := by
  unfold upperSupportingPole circleValue
  ring

theorem lowerSupportingPole_mem_circle
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    circleValue (A.supportingCenterAt p) |1 / K|
      (lowerSupportingPole A p) = 0 := by
  unfold lowerSupportingPole circleValue
  ring

/-- The actual upper exterior component contains the upper pole of its derived
circle.  This proves pole continuation through coordinate tangencies without a
pole premise or a compactness argument. -/
theorem upperSupportingPole_mem_upperExterior_component
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    upperSupportingPole A p ∈
      connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have htop :
      interfaceY < (A.supportingCenterAt p).2 + |1 / K| :=
    p.2.2.trans_le (circleValue_zero_snd_bounds hradius hpCircle).2
  rw [upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
  exact ⟨upperSupportingPole_mem_circle A p, htop⟩

/-- Lower-pole counterpart of actual continuation. -/
theorem lowerSupportingPole_mem_lowerExterior_component
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    lowerSupportingPole A p ∈
      connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have hbottom :
      (A.supportingCenterAt p).2 - |1 / K| < interfaceY :=
    (circleValue_zero_snd_bounds hradius hpCircle).1.trans_lt p.2.2
  rw [lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
  exact ⟨lowerSupportingPole_mem_circle A p, hbottom⟩

/-- Every upper secant endpoint, and the coincident point in the tangent case,
lies in the closure of the actual component and hence on the actual frontier.
No regular chart is required at the interface itself. -/
theorem upperExterior_interfaceContacts_mem_closure_and_frontier
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0)
    (hbottom :
      (A.supportingCenterAt p).2 - |1 / K| ≤ interfaceY) :
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1)) ∧
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier) := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have htop :
      interfaceY < (A.supportingCenterAt p).2 + |1 / K| :=
    p.2.2.trans_le (circleValue_zero_snd_bounds hradius hpCircle).2
  have hleftClosure :
      leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) := by
    rw [upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
    exact leftCirclePointAtHeight_mem_closure_upperClip
      hradius hbottom htop
  have hrightClosure :
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) := by
    rw [upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
    exact rightCirclePointAtHeight_mem_closure_upperClip
      hradius hbottom htop
  have hclosureSubset :
      closure (connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) ⊆
          frontier carrier := by
    apply closure_minimal
    · exact (connectedComponentIn_subset
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1
        ).trans inter_subset_left
    · exact isClosed_frontier
  exact ⟨⟨hleftClosure, hrightClosure⟩,
    hclosureSubset hleftClosure, hclosureSubset hrightClosure⟩

/-- Reflected closure-derived interface contacts for a lower component. -/
theorem lowerExterior_interfaceContacts_mem_closure_and_frontier
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0)
    (htop :
      interfaceY ≤ (A.supportingCenterAt p).2 + |1 / K|) :
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1)) ∧
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier) := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have hbottom :
      (A.supportingCenterAt p).2 - |1 / K| < interfaceY :=
    (circleValue_zero_snd_bounds hradius hpCircle).1.trans_lt p.2.2
  have hleftClosure :
      leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) := by
    rw [lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
    exact leftCirclePointAtHeight_mem_closure_lowerClip
      hradius hbottom htop
  have hrightClosure :
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) := by
    rw [lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK]
    exact rightCirclePointAtHeight_mem_closure_lowerClip
      hradius hbottom htop
  have hclosureSubset :
      closure (connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) ⊆
          frontier carrier := by
    apply closure_minimal
    · exact (connectedComponentIn_subset
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1
        ).trans inter_subset_left
    · exact isClosed_frontier
  exact ⟨⟨hleftClosure, hrightClosure⟩,
    hclosureSubset hleftClosure, hclosureSubset hrightClosure⟩


/-- If the interface lies strictly below the lower pole, exact saturation
retains the detached full-circle alternative explicitly. -/
theorem upperExterior_component_eq_fullCircle_of_interface_lt_lowerPole
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0)
    (hdetached :
      interfaceY < (A.supportingCenterAt p).2 - |1 / K|) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0} := by
  rw [upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK,
    inter_eq_left.mpr]
  intro q hq
  exact hdetached.trans_le
    (circleValue_zero_snd_bounds
      (abs_pos.mpr (one_div_ne_zero hK)) hq).1

/-- Reflected detached-circle alternative for a lower exterior component. -/
theorem lowerExterior_component_eq_fullCircle_of_upperPole_lt_interface
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hdetached :
      (A.supportingCenterAt p).2 + |1 / K| < interfaceY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0} := by
  rw [lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK,
    inter_eq_left.mpr]
  intro q hq
  exact (circleValue_zero_snd_bounds
    (abs_pos.mpr (one_div_ne_zero hK)) hq).2.trans_lt hdetached

/-- Truthful mixed-atlas germs supply the equator hypotheses needed to exclude
a full supporting-circle component.  The caller supplies only representative
topology and one global reach point, not ordered contacts or chosen chart
orientations. -/
theorem mixedAtlas_component_ne_fullCircle_of_interval_sections_and_reach
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hK : K ≠ 0)
    (reach : ∃ q ∈ carrier,
      0 ≤ circleValue (A.supportingCenterAt p) |1 / K| q) :
    connectedComponentIn locus p.1 ≠
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0} := by
  intro hfull
  let center := A.supportingCenterAt p
  let radius := |1 / K|
  have hradius : 0 < radius := abs_pos.mpr (one_div_ne_zero hK)
  have hcircleFrontier :
      {q : PlanePoint | circleValue center radius q = 0} ⊆
        frontier carrier := by
    intro q hq
    apply A.locus_subset_frontier
    apply connectedComponentIn_subset locus p.1
    rw [hfull]
    exact hq
  let leftPoint : PlanePoint := (center.1 - radius, center.2)
  let rightPoint : PlanePoint := (center.1 + radius, center.2)
  have hleftCircle : circleValue center radius leftPoint = 0 := by
    dsimp only [leftPoint]
    unfold circleValue
    ring
  have hrightCircle : circleValue center radius rightPoint = 0 := by
    dsimp only [rightPoint]
    unfold circleValue
    ring
  have hleftComponent : leftPoint ∈ connectedComponentIn locus p.1 := by
    rw [hfull]
    exact hleftCircle
  have hrightComponent : rightPoint ∈ connectedComponentIn locus p.1 := by
    rw [hfull]
    exact hrightCircle
  have hleftImage :
      leftPoint ∈ ((↑) : locus → PlanePoint) '' connectedComponent p := by
    rwa [← connectedComponentIn_eq_image p.2]
  have hrightImage :
      rightPoint ∈ ((↑) : locus → PlanePoint) '' connectedComponent p := by
    rwa [← connectedComponentIn_eq_image p.2]
  rcases hleftImage with ⟨left, hleftConnected, hleftValue⟩
  rcases hrightImage with ⟨right, hrightConnected, hrightValue⟩
  have hleftGerm :=
    mixedAtlas_locallyOneSided_supportingCircle A left hK
  have hrightGerm :=
    mixedAtlas_locallyOneSided_supportingCircle A right hK
  have hleftCenter :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A p left hK hleftConnected
  have hrightCenter :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A p right hK hrightConnected
  rw [hleftCenter, hleftValue] at hleftGerm
  rw [hrightCenter, hrightValue] at hrightGerm
  exact not_full_circle_frontier_of_interval_sections_and_reach
    hcarrierOpen hcarrierBounded hcarrierConnected hsections hradius
      hcircleFrontier hleftGerm hrightGerm reach

/-- A connected bounded interval-section representative that reaches the
non-exterior side rules out the detached upper-circle alternative.  The reach
point belongs only to the carrier; no interface contact or component membership
is supplied. -/
theorem upperExterior_lowerPole_le_interface_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, q.2 ≤ interfaceY)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    (A.supportingCenterAt p).2 - |1 / K| ≤ interfaceY := by
  have hK :=
    commonCurvature_ne_zero_of_bounded_upperExterior
      A hcarrierBounded p
  by_contra hnot
  have hdetached :
      interfaceY < (A.supportingCenterAt p).2 - |1 / K| :=
    lt_of_not_ge hnot
  obtain ⟨q, hqCarrier, hqHeight⟩ := hreach
  have hcircleReach :
      0 ≤ circleValue (A.supportingCenterAt p) |1 / K| q := by
    let dy := q.2 - (A.supportingCenterAt p).2
    let radius := |1 / K|
    have hradius : 0 < radius :=
      abs_pos.mpr (one_div_ne_zero hK)
    have hleft : dy - radius < 0 := by
      dsimp only [dy, radius]
      linarith
    have hright : dy + radius < 0 := by
      dsimp only [dy, radius]
      linarith
    have hvertical : radius ^ 2 < dy ^ 2 := by
      have hproduct := mul_pos_of_neg_of_neg hleft hright
      nlinarith
    unfold circleValue
    dsimp only [dy, radius] at hvertical
    nlinarith [sq_nonneg (q.1 - (A.supportingCenterAt p).1)]
  exact mixedAtlas_component_ne_fullCircle_of_interval_sections_and_reach
    A p hcarrierOpen hcarrierBounded hcarrierConnected hsections hK
      ⟨q, hqCarrier, hcircleReach⟩
        (upperExterior_component_eq_fullCircle_of_interface_lt_lowerPole
          A p hK hdetached)

/-- Reflected global-reach exclusion of a detached lower supporting circle. -/
theorem lowerExterior_interface_le_upperPole_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, interfaceY ≤ q.2)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    interfaceY ≤ (A.supportingCenterAt p).2 + |1 / K| := by
  have hK :=
    commonCurvature_ne_zero_of_bounded_lowerExterior
      A hcarrierBounded p
  by_contra hnot
  have hdetached :
      (A.supportingCenterAt p).2 + |1 / K| < interfaceY :=
    lt_of_not_ge hnot
  obtain ⟨q, hqCarrier, hqHeight⟩ := hreach
  have hcircleReach :
      0 ≤ circleValue (A.supportingCenterAt p) |1 / K| q := by
    let dy := q.2 - (A.supportingCenterAt p).2
    let radius := |1 / K|
    have hleft : 0 < dy - radius := by
      dsimp only [dy, radius]
      linarith
    have hright : 0 < dy + radius := by
      have hradius : 0 < radius :=
        abs_pos.mpr (one_div_ne_zero hK)
      linarith
    have hvertical : radius ^ 2 < dy ^ 2 := by
      have hproduct := mul_pos hleft hright
      nlinarith
    unfold circleValue
    dsimp only [dy, radius] at hvertical
    nlinarith [sq_nonneg (q.1 - (A.supportingCenterAt p).1)]
  exact mixedAtlas_component_ne_fullCircle_of_interval_sections_and_reach
    A p hcarrierOpen hcarrierBounded hcarrierConnected hsections hK
      ⟨q, hqCarrier, hcircleReach⟩
        (lowerExterior_component_eq_fullCircle_of_upperPole_lt_interface
          A p hK hdetached)

/-- The global upper reach derives both algebraic interface contacts in the
component closure and on the actual frontier.  In the tangent case the two
formulae coincide, so no separate contact witness is required. -/
theorem upperExterior_interfaceContacts_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, q.2 ≤ interfaceY)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1) ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1)) ∧
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier) := by
  exact upperExterior_interfaceContacts_mem_closure_and_frontier A p
    (commonCurvature_ne_zero_of_bounded_upperExterior A hcarrierBounded p)
    (upperExterior_lowerPole_le_interface_of_global_reach A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hreach p)

/-- Reflected closure/frontier contacts derived from one global upper-side
reach point of the representative. -/
theorem lowerExterior_interfaceContacts_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, interfaceY ≤ q.2)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1) ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1)) ∧
    (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier ∧
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY ∈
        frontier carrier) := by
  exact lowerExterior_interfaceContacts_mem_closure_and_frontier A p
    (commonCurvature_ne_zero_of_bounded_lowerExterior A hcarrierBounded p)
    (lowerExterior_interface_le_upperPole_of_global_reach A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hreach p)


/-- Global representative topology makes the entire upper exterior locus one
continuation component.  Ordered transverse points are derived at a common
interior height from each complete circle clip and then identified with the two
endpoints of the same horizontal section. -/
theorem upperExterior_connectedComponentIn_eq_locus_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, q.2 ≤ interfaceY)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
      frontier carrier ∩ {q : PlanePoint | interfaceY < q.2} := by
  apply Set.Subset.antisymm
  · exact connectedComponentIn_subset _ _
  · intro q hqLocus
    let q' :
        (frontier carrier ∩
          {z : PlanePoint | interfaceY < z.2} : Set PlanePoint) :=
      ⟨q, hqLocus⟩
    have hK :=
      commonCurvature_ne_zero_of_bounded_upperExterior
        A hcarrierBounded p
    let radius := |1 / K|
    have hradius : 0 < radius := abs_pos.mpr (one_div_ne_zero hK)
    have hpCircle :
        circleValue (A.supportingCenterAt p) radius p.1 = 0 := by
      have hpSupport := A.base_mem_supportAt p
      rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
    have hqCircle :
        circleValue (A.supportingCenterAt q') radius q'.1 = 0 := by
      have hqSupport := A.base_mem_supportAt q'
      rwa [A.supportAt_eq_circleValue_zero q' hK] at hqSupport
    have hpTop :
        interfaceY < (A.supportingCenterAt p).2 + radius :=
      p.2.2.trans_le
        (circleValue_zero_snd_bounds hradius hpCircle).2
    have hqTop :
        interfaceY < (A.supportingCenterAt q').2 + radius :=
      q'.2.2.trans_le
        (circleValue_zero_snd_bounds hradius hqCircle).2
    have hpBottom :
        (A.supportingCenterAt p).2 - radius ≤ interfaceY := by
      dsimp only [radius]
      exact upperExterior_lowerPole_le_interface_of_global_reach A
        hcarrierOpen hcarrierBounded hcarrierConnected hsections hreach p
    have hqBottom :
        (A.supportingCenterAt q').2 - radius ≤ interfaceY := by
      dsimp only [radius]
      exact upperExterior_lowerPole_le_interface_of_global_reach A
        hcarrierOpen hcarrierBounded hcarrierConnected hsections hreach q'
    let commonY := (interfaceY + min
      ((A.supportingCenterAt p).2 + radius)
      ((A.supportingCenterAt q').2 + radius)) / 2
    have hinterfaceMin : interfaceY < min
        ((A.supportingCenterAt p).2 + radius)
        ((A.supportingCenterAt q').2 + radius) :=
      lt_min hpTop hqTop
    have hcommonAbove : interfaceY < commonY := by
      dsimp only [commonY]
      linarith
    have hcommonBelowP :
        commonY < (A.supportingCenterAt p).2 + radius := by
      have hminLe := min_le_left
        ((A.supportingCenterAt p).2 + radius)
        ((A.supportingCenterAt q').2 + radius)
      dsimp only [commonY]
      linarith
    have hcommonBelowQ :
        commonY < (A.supportingCenterAt q').2 + radius := by
      have hminLe := min_le_right
        ((A.supportingCenterAt p).2 + radius)
        ((A.supportingCenterAt q').2 + radius)
      dsimp only [commonY]
      linarith
    have hbetweenP :
        (A.supportingCenterAt p).2 - radius < commonY ∧
          commonY < (A.supportingCenterAt p).2 + radius :=
      ⟨hpBottom.trans_lt hcommonAbove, hcommonBelowP⟩
    have hbetweenQ :
        (A.supportingCenterAt q').2 - radius < commonY ∧
          commonY < (A.supportingCenterAt q').2 + radius :=
      ⟨hqBottom.trans_lt hcommonAbove, hcommonBelowQ⟩
    have hpPair :=
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hbetweenP.1 hbetweenP.2
    have hqPair :=
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hbetweenQ.1 hbetweenQ.2
    let leftP := leftCirclePointAtHeight
      (A.supportingCenterAt p) radius commonY
    let rightP := rightCirclePointAtHeight
      (A.supportingCenterAt p) radius commonY
    let leftQ := leftCirclePointAtHeight
      (A.supportingCenterAt q') radius commonY
    let rightQ := rightCirclePointAtHeight
      (A.supportingCenterAt q') radius commonY
    have hleftPCircle :
        circleValue (A.supportingCenterAt p) radius leftP = 0 ∧
          leftP.2 = commonY := by
      change leftP ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt p) radius z = 0 ∧
            z.2 = commonY}
      rw [hpPair.1]
      exact Set.mem_insert _ _
    have hrightPCircle :
        circleValue (A.supportingCenterAt p) radius rightP = 0 ∧
          rightP.2 = commonY := by
      change rightP ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt p) radius z = 0 ∧
            z.2 = commonY}
      rw [hpPair.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hleftQCircle :
        circleValue (A.supportingCenterAt q') radius leftQ = 0 ∧
          leftQ.2 = commonY := by
      change leftQ ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt q') radius z = 0 ∧
            z.2 = commonY}
      rw [hqPair.1]
      exact Set.mem_insert _ _
    have hrightQCircle :
        circleValue (A.supportingCenterAt q') radius rightQ = 0 ∧
          rightQ.2 = commonY := by
      change rightQ ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt q') radius z = 0 ∧
            z.2 = commonY}
      rw [hqPair.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hpComponent :=
      upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK
    have hqComponent :=
      upperExterior_connectedComponentIn_eq_circle_of_ne_zero A q' hK
    have hleftPComponent :
        leftP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) p.1 := by
      rw [hpComponent]
      refine ⟨hleftPCircle.1, ?_⟩
      change interfaceY < leftP.2
      rw [hleftPCircle.2]
      exact hcommonAbove
    have hrightPComponent :
        rightP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) p.1 := by
      rw [hpComponent]
      refine ⟨hrightPCircle.1, ?_⟩
      change interfaceY < rightP.2
      rw [hrightPCircle.2]
      exact hcommonAbove
    have hleftQComponent :
        leftQ ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) q'.1 := by
      rw [hqComponent]
      refine ⟨hleftQCircle.1, ?_⟩
      change interfaceY < leftQ.2
      rw [hleftQCircle.2]
      exact hcommonAbove
    have hrightQComponent :
        rightQ ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) q'.1 := by
      rw [hqComponent]
      refine ⟨hrightQCircle.1, ?_⟩
      change interfaceY < rightQ.2
      rw [hrightQCircle.2]
      exact hcommonAbove
    have hleftPLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A p hK hleftPComponent
    have hrightPLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A p hK hrightPComponent
    have hleftQLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A q' hK hleftQComponent
    have hrightQLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A q' hK hrightQComponent
    have hleftPTransverse :
        leftP.1 ≠ (A.supportingCenterAt p).1 := by
      intro heq
      dsimp only [leftP, rightP, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hpPair
      linarith [hpPair.2]
    have hrightPTransverse :
        rightP.1 ≠ (A.supportingCenterAt p).1 := by
      intro heq
      dsimp only [leftP, rightP, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hpPair
      linarith [hpPair.2]
    have hleftQTransverse :
        leftQ.1 ≠ (A.supportingCenterAt q').1 := by
      intro heq
      dsimp only [leftQ, rightQ, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hqPair
      linarith [hqPair.2]
    have hrightQTransverse :
        rightQ.1 ≠ (A.supportingCenterAt q').1 := by
      intro heq
      dsimp only [leftQ, rightQ, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hqPair
      linarith [hqPair.2]
    let S := horizontalSection carrier commonY
    have hleftSectionFrontier :
        leftP.1 ∈ frontier S := by
      dsimp only [S]
      rw [← hleftPCircle.2]
      exact circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hleftPCircle.1 hleftPTransverse hleftPLocal
    have hSNonempty : S.Nonempty := by
      by_contra hnone
      have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hnone
      rw [hSempty, frontier_empty] at hleftSectionFrontier
      exact hleftSectionFrontier
    have hSopen : IsOpen S := by
      exact isOpen_horizontalSection hcarrierOpen commonY
    have hSbounded : Bornology.IsBounded S :=
      isBounded_horizontalSection hcarrierBounded commonY
    have hsection :
        S = Ioo (sInf S) (sSup S) :=
      CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
        hSopen hSNonempty hSbounded (hsections commonY)
    have hendpointOrder : sInf S ≤ sSup S := by
      obtain ⟨s, hs⟩ := hSNonempty
      have hsInterval : s ∈ Ioo (sInf S) (sSup S) := hsection ▸ hs
      exact hsInterval.1.le.trans hsInterval.2.le
    have hpSection :
        horizontalSection carrier leftP.2 = Ioo (sInf S) (sSup S) := by
      rw [hleftPCircle.2]
      exact hsection
    have hqSection :
        horizontalSection carrier leftQ.2 = Ioo (sInf S) (sSup S) := by
      rw [hleftQCircle.2]
      exact hsection
    have hpEndpoints :=
      ordered_transverse_circle_points_are_interval_endpoints
        hendpointOrder hpSection
        (hrightPCircle.2.trans hleftPCircle.2.symm)
        hleftPCircle.1 hrightPCircle.1
        hleftPTransverse hrightPTransverse
        hleftPLocal hrightPLocal hpPair.2
    have hqEndpoints :=
      ordered_transverse_circle_points_are_interval_endpoints
        hendpointOrder hqSection
        (hrightQCircle.2.trans hleftQCircle.2.symm)
        hleftQCircle.1 hrightQCircle.1
        hleftQTransverse hrightQTransverse
        hleftQLocal hrightQLocal hqPair.2
    have hleftEq : leftP = leftQ := by
      apply Prod.ext
      · exact hpEndpoints.1.symm.trans hqEndpoints.1
      · exact hleftPCircle.2.trans hleftQCircle.2.symm
    have hsharedQ :
        leftP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) q'.1 := by
      rw [hleftEq]
      exact hleftQComponent
    have hcomponentEq :
        connectedComponentIn
            (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) p.1 =
          connectedComponentIn
            (frontier carrier ∩ {z : PlanePoint | interfaceY < z.2}) q'.1 :=
      (connectedComponentIn_eq hleftPComponent).trans
        (connectedComponentIn_eq hsharedQ).symm
    rw [hcomponentEq]
    exact mem_connectedComponentIn q'.2

/-- Reflected global uniqueness of the lower exterior continuation component. -/
theorem lowerExterior_connectedComponentIn_eq_locus_of_global_reach
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hreach : ∃ q ∈ carrier, interfaceY ≤ q.2)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY} := by
  apply Set.Subset.antisymm
  · exact connectedComponentIn_subset _ _
  · intro q hqLocus
    let q' :
        (frontier carrier ∩
          {z : PlanePoint | z.2 < interfaceY} : Set PlanePoint) :=
      ⟨q, hqLocus⟩
    have hK :=
      commonCurvature_ne_zero_of_bounded_lowerExterior
        A hcarrierBounded p
    let radius := |1 / K|
    have hradius : 0 < radius := abs_pos.mpr (one_div_ne_zero hK)
    have hpCircle :
        circleValue (A.supportingCenterAt p) radius p.1 = 0 := by
      have hpSupport := A.base_mem_supportAt p
      rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
    have hqCircle :
        circleValue (A.supportingCenterAt q') radius q'.1 = 0 := by
      have hqSupport := A.base_mem_supportAt q'
      rwa [A.supportAt_eq_circleValue_zero q' hK] at hqSupport
    have hpBottom :
        (A.supportingCenterAt p).2 - radius < interfaceY :=
      (circleValue_zero_snd_bounds hradius hpCircle).1.trans_lt p.2.2
    have hqBottom :
        (A.supportingCenterAt q').2 - radius < interfaceY :=
      (circleValue_zero_snd_bounds hradius hqCircle).1.trans_lt q'.2.2
    have hpTop :
        interfaceY ≤ (A.supportingCenterAt p).2 + radius := by
      dsimp only [radius]
      exact lowerExterior_interface_le_upperPole_of_global_reach A
        hcarrierOpen hcarrierBounded hcarrierConnected hsections hreach p
    have hqTop :
        interfaceY ≤ (A.supportingCenterAt q').2 + radius := by
      dsimp only [radius]
      exact lowerExterior_interface_le_upperPole_of_global_reach A
        hcarrierOpen hcarrierBounded hcarrierConnected hsections hreach q'
    let commonY := (max
      ((A.supportingCenterAt p).2 - radius)
      ((A.supportingCenterAt q').2 - radius) + interfaceY) / 2
    have hmaxInterface : max
        ((A.supportingCenterAt p).2 - radius)
        ((A.supportingCenterAt q').2 - radius) < interfaceY :=
      max_lt hpBottom hqBottom
    have hcommonBelow : commonY < interfaceY := by
      dsimp only [commonY]
      linarith
    have hcommonAboveP :
        (A.supportingCenterAt p).2 - radius < commonY := by
      have hleMax := le_max_left
        ((A.supportingCenterAt p).2 - radius)
        ((A.supportingCenterAt q').2 - radius)
      dsimp only [commonY]
      linarith
    have hcommonAboveQ :
        (A.supportingCenterAt q').2 - radius < commonY := by
      have hleMax := le_max_right
        ((A.supportingCenterAt p).2 - radius)
        ((A.supportingCenterAt q').2 - radius)
      dsimp only [commonY]
      linarith
    have hbetweenP :
        (A.supportingCenterAt p).2 - radius < commonY ∧
          commonY < (A.supportingCenterAt p).2 + radius :=
      ⟨hcommonAboveP, hcommonBelow.trans_le hpTop⟩
    have hbetweenQ :
        (A.supportingCenterAt q').2 - radius < commonY ∧
          commonY < (A.supportingCenterAt q').2 + radius :=
      ⟨hcommonAboveQ, hcommonBelow.trans_le hqTop⟩
    have hpPair :=
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hbetweenP.1 hbetweenP.2
    have hqPair :=
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hbetweenQ.1 hbetweenQ.2
    let leftP := leftCirclePointAtHeight
      (A.supportingCenterAt p) radius commonY
    let rightP := rightCirclePointAtHeight
      (A.supportingCenterAt p) radius commonY
    let leftQ := leftCirclePointAtHeight
      (A.supportingCenterAt q') radius commonY
    let rightQ := rightCirclePointAtHeight
      (A.supportingCenterAt q') radius commonY
    have hleftPCircle :
        circleValue (A.supportingCenterAt p) radius leftP = 0 ∧
          leftP.2 = commonY := by
      change leftP ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt p) radius z = 0 ∧
            z.2 = commonY}
      rw [hpPair.1]
      exact Set.mem_insert _ _
    have hrightPCircle :
        circleValue (A.supportingCenterAt p) radius rightP = 0 ∧
          rightP.2 = commonY := by
      change rightP ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt p) radius z = 0 ∧
            z.2 = commonY}
      rw [hpPair.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hleftQCircle :
        circleValue (A.supportingCenterAt q') radius leftQ = 0 ∧
          leftQ.2 = commonY := by
      change leftQ ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt q') radius z = 0 ∧
            z.2 = commonY}
      rw [hqPair.1]
      exact Set.mem_insert _ _
    have hrightQCircle :
        circleValue (A.supportingCenterAt q') radius rightQ = 0 ∧
          rightQ.2 = commonY := by
      change rightQ ∈
        {z : PlanePoint |
          circleValue (A.supportingCenterAt q') radius z = 0 ∧
            z.2 = commonY}
      rw [hqPair.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    have hpComponent :=
      lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK
    have hqComponent :=
      lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A q' hK
    have hleftPComponent :
        leftP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) p.1 := by
      rw [hpComponent]
      refine ⟨hleftPCircle.1, ?_⟩
      change leftP.2 < interfaceY
      rw [hleftPCircle.2]
      exact hcommonBelow
    have hrightPComponent :
        rightP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) p.1 := by
      rw [hpComponent]
      refine ⟨hrightPCircle.1, ?_⟩
      change rightP.2 < interfaceY
      rw [hrightPCircle.2]
      exact hcommonBelow
    have hleftQComponent :
        leftQ ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) q'.1 := by
      rw [hqComponent]
      refine ⟨hleftQCircle.1, ?_⟩
      change leftQ.2 < interfaceY
      rw [hleftQCircle.2]
      exact hcommonBelow
    have hrightQComponent :
        rightQ ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) q'.1 := by
      rw [hqComponent]
      refine ⟨hrightQCircle.1, ?_⟩
      change rightQ.2 < interfaceY
      rw [hrightQCircle.2]
      exact hcommonBelow
    have hleftPLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A p hK hleftPComponent
    have hrightPLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A p hK hrightPComponent
    have hleftQLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A q' hK hleftQComponent
    have hrightQLocal :=
      mixedAtlas_locallyOneSided_of_mem_connectedComponentIn
        A q' hK hrightQComponent
    have hleftPTransverse :
        leftP.1 ≠ (A.supportingCenterAt p).1 := by
      intro heq
      dsimp only [leftP, rightP, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hpPair
      linarith [hpPair.2]
    have hrightPTransverse :
        rightP.1 ≠ (A.supportingCenterAt p).1 := by
      intro heq
      dsimp only [leftP, rightP, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hpPair
      linarith [hpPair.2]
    have hleftQTransverse :
        leftQ.1 ≠ (A.supportingCenterAt q').1 := by
      intro heq
      dsimp only [leftQ, rightQ, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hqPair
      linarith [hqPair.2]
    have hrightQTransverse :
        rightQ.1 ≠ (A.supportingCenterAt q').1 := by
      intro heq
      dsimp only [leftQ, rightQ, leftCirclePointAtHeight,
        rightCirclePointAtHeight] at heq hqPair
      linarith [hqPair.2]
    let S := horizontalSection carrier commonY
    have hleftSectionFrontier :
        leftP.1 ∈ frontier S := by
      dsimp only [S]
      rw [← hleftPCircle.2]
      exact circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hleftPCircle.1 hleftPTransverse hleftPLocal
    have hSNonempty : S.Nonempty := by
      by_contra hnone
      have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hnone
      rw [hSempty, frontier_empty] at hleftSectionFrontier
      exact hleftSectionFrontier
    have hSopen : IsOpen S :=
      isOpen_horizontalSection hcarrierOpen commonY
    have hSbounded : Bornology.IsBounded S :=
      isBounded_horizontalSection hcarrierBounded commonY
    have hsection :
        S = Ioo (sInf S) (sSup S) :=
      CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
        hSopen hSNonempty hSbounded (hsections commonY)
    have hendpointOrder : sInf S ≤ sSup S := by
      obtain ⟨s, hs⟩ := hSNonempty
      have hsInterval : s ∈ Ioo (sInf S) (sSup S) := hsection ▸ hs
      exact hsInterval.1.le.trans hsInterval.2.le
    have hpSection :
        horizontalSection carrier leftP.2 = Ioo (sInf S) (sSup S) := by
      rw [hleftPCircle.2]
      exact hsection
    have hqSection :
        horizontalSection carrier leftQ.2 = Ioo (sInf S) (sSup S) := by
      rw [hleftQCircle.2]
      exact hsection
    have hpEndpoints :=
      ordered_transverse_circle_points_are_interval_endpoints
        hendpointOrder hpSection
        (hrightPCircle.2.trans hleftPCircle.2.symm)
        hleftPCircle.1 hrightPCircle.1
        hleftPTransverse hrightPTransverse
        hleftPLocal hrightPLocal hpPair.2
    have hqEndpoints :=
      ordered_transverse_circle_points_are_interval_endpoints
        hendpointOrder hqSection
        (hrightQCircle.2.trans hleftQCircle.2.symm)
        hleftQCircle.1 hrightQCircle.1
        hleftQTransverse hrightQTransverse
        hleftQLocal hrightQLocal hqPair.2
    have hleftEq : leftP = leftQ := by
      apply Prod.ext
      · exact hpEndpoints.1.symm.trans hqEndpoints.1
      · exact hleftPCircle.2.trans hleftQCircle.2.symm
    have hsharedQ :
        leftP ∈ connectedComponentIn
          (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) q'.1 := by
      rw [hleftEq]
      exact hleftQComponent
    have hcomponentEq :
        connectedComponentIn
            (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) p.1 =
          connectedComponentIn
            (frontier carrier ∩ {z : PlanePoint | z.2 < interfaceY}) q'.1 :=
      (connectedComponentIn_eq hleftPComponent).trans
        (connectedComponentIn_eq hsharedQ).symm
    rw [hcomponentEq]
    exact mem_connectedComponentIn q'.2

/-- A frontier point strictly below a level yields an actual carrier point
below that level by the definition of closure. -/
theorem exists_carrier_snd_lt_of_frontier_snd_lt
    {carrier : Set PlanePoint} {p : PlanePoint} {level : ℝ}
    (hpFrontier : p ∈ frontier carrier) (hpHeight : p.2 < level) :
    ∃ q ∈ carrier, q.2 < level := by
  rcases mem_closure_iff.1 (frontier_subset_closure hpFrontier)
      {q : PlanePoint | q.2 < level}
      (isOpen_Iio.preimage continuous_snd) hpHeight with
    ⟨q, hqHeight, hqCarrier⟩
  exact ⟨q, hqCarrier, hqHeight⟩

/-- Reflected closure consequence above a level. -/
theorem exists_carrier_snd_gt_of_frontier_snd_gt
    {carrier : Set PlanePoint} {p : PlanePoint} {level : ℝ}
    (hpFrontier : p ∈ frontier carrier) (hpHeight : level < p.2) :
    ∃ q ∈ carrier, level < q.2 := by
  rcases mem_closure_iff.1 (frontier_subset_closure hpFrontier)
      {q : PlanePoint | level < q.2}
      (isOpen_Ioi.preimage continuous_snd) hpHeight with
    ⟨q, hqHeight, hqCarrier⟩
  exact ⟨q, hqCarrier, hqHeight⟩

/-- With nonempty exterior loci on both sides of two ordered interfaces, all
reach premises are derived from the actual frontier and both exterior loci are
single continuation components.  No ordered contact tuple or pole geometry is
an input. -/
theorem twoSidedExterior_unique_components
    {carrier : Set PlanePoint}
    {KUpper KLower lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) KUpper)
    (ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) KLower)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) pUpper.1 =
      frontier carrier ∩ {q : PlanePoint | upperY < q.2} ∧
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) pLower.1 =
      frontier carrier ∩ {q : PlanePoint | q.2 < lowerY} := by
  obtain ⟨qLower, hqLowerCarrier, hqLowerHeight⟩ :=
    exists_carrier_snd_lt_of_frontier_snd_lt pLower.2.1
      (pLower.2.2.trans hlowerUpper)
  obtain ⟨qUpper, hqUpperCarrier, hqUpperHeight⟩ :=
    exists_carrier_snd_gt_of_frontier_snd_gt pUpper.2.1
      (hlowerUpper.trans pUpper.2.2)
  have hreachUpper : ∃ q ∈ carrier, q.2 ≤ upperY :=
    ⟨qLower, hqLowerCarrier, hqLowerHeight.le⟩
  have hreachLower : ∃ q ∈ carrier, lowerY ≤ q.2 :=
    ⟨qUpper, hqUpperCarrier, hqUpperHeight.le⟩
  exact ⟨upperExterior_connectedComponentIn_eq_locus_of_global_reach
    AUpper hcarrierOpen hcarrierBounded hcarrierConnected hsections
      hreachUpper pUpper,
    lowerExterior_connectedComponentIn_eq_locus_of_global_reach
      ALower hcarrierOpen hcarrierBounded hcarrierConnected hsections
        hreachLower pLower⟩


/-- Before any cap angle is selected, the upper support has exactly the
detached, tangent, or secant relation to the interface. -/
theorem upperExterior_support_position_trichotomy
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    interfaceY < (A.supportingCenterAt p).2 - |1 / K| ∨
      interfaceY = (A.supportingCenterAt p).2 - |1 / K| ∨
      (A.supportingCenterAt p).2 - |1 / K| < interfaceY :=
  lt_trichotomy interfaceY
    ((A.supportingCenterAt p).2 - |1 / K|)

/-- Lower support position trichotomy, retaining secant, tangent, and detached
possibilities in reflected order. -/
theorem lowerExterior_support_position_trichotomy
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    (A.supportingCenterAt p).2 + |1 / K| < interfaceY ∨
      (A.supportingCenterAt p).2 + |1 / K| = interfaceY ∨
      interfaceY < (A.supportingCenterAt p).2 + |1 / K| :=
  lt_trichotomy ((A.supportingCenterAt p).2 + |1 / K|)
    interfaceY

/-- Exact upper support alternatives with their complete interface-contact
sets.  In the secant case both ordered contacts are derived algebraically; in
the tangent case the one contact is the lower pole; in the detached case there
is no contact and the actual component is the full circle. -/
theorem upperExterior_detached_tangent_or_secant
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    (interfaceY < (A.supportingCenterAt p).2 - |1 / K| ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} = ∅) ∨
    (interfaceY = (A.supportingCenterAt p).2 - |1 / K| ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} =
        {lowerSupportingPole A p}) ∨
    ((A.supportingCenterAt p).2 - |1 / K| < interfaceY ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} =
        {leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY,
          rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
            interfaceY} ∧
      (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
          interfaceY).1 <
        (rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
          interfaceY).1) := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  rcases upperExterior_support_position_trichotomy A p with
      hdetached | htangent | hsecant
  · exact Or.inl ⟨hdetached,
      upperExterior_component_eq_fullCircle_of_interface_lt_lowerPole
        A p hK hdetached,
      circleValue_zero_and_snd_eq_empty_of_below_lowerPole
        hradius hdetached⟩
  · exact Or.inr (Or.inl ⟨htangent,
      circleValue_zero_and_snd_eq_singleton_of_lower_tangent htangent⟩)
  · have hpCircle :
        circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
      have hpSupport := A.base_mem_supportAt p
      rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
    have htop :
        interfaceY < (A.supportingCenterAt p).2 + |1 / K| :=
      p.2.2.trans_le (circleValue_zero_snd_bounds hradius hpCircle).2
    exact Or.inr (Or.inr ⟨hsecant,
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hsecant htop⟩)

/-- Reflected complete alternative and contact accounting for a lower
exterior component. -/
theorem lowerExterior_detached_tangent_or_secant
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    ((A.supportingCenterAt p).2 + |1 / K| < interfaceY ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} = ∅) ∨
    ((A.supportingCenterAt p).2 + |1 / K| = interfaceY ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} =
        {upperSupportingPole A p}) ∨
    (interfaceY < (A.supportingCenterAt p).2 + |1 / K| ∧
      {q : PlanePoint |
        circleValue (A.supportingCenterAt p) |1 / K| q = 0 ∧
          q.2 = interfaceY} =
        {leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| interfaceY,
          rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
            interfaceY} ∧
      (leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
          interfaceY).1 <
        (rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K|
          interfaceY).1) := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  rcases lowerExterior_support_position_trichotomy A p with
      hdetached | htangent | hsecant
  · exact Or.inl ⟨hdetached,
      lowerExterior_component_eq_fullCircle_of_upperPole_lt_interface
        A p hK hdetached,
      circleValue_zero_and_snd_eq_empty_of_above_upperPole
        hradius hdetached⟩
  · exact Or.inr (Or.inl ⟨htangent,
      circleValue_zero_and_snd_eq_singleton_of_upper_tangent htangent.symm⟩)
  · have hpCircle :
        circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
      have hpSupport := A.base_mem_supportAt p
      rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
    have hbottom :
        (A.supportingCenterAt p).2 - |1 / K| < interfaceY :=
      (circleValue_zero_snd_bounds hradius hpCircle).1.trans_lt p.2.2
    exact Or.inr (Or.inr ⟨hsecant,
      circleValue_zero_and_snd_eq_pair_of_between_poles
        hradius hbottom hsecant⟩)


/-- On a bounded actual representative, every nonempty upper exterior
component is a complete positive-radius circle clip and contains its actual
upper pole. -/
theorem boundedUpperExterior_completeCircularArc
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    K ≠ 0 ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
          {q : PlanePoint | interfaceY < q.2} ∧
      upperSupportingPole A p ∈
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 := by
  have hK := commonCurvature_ne_zero_of_bounded_upperExterior
    A hcarrierBounded p
  exact ⟨hK, upperExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK,
    upperSupportingPole_mem_upperExterior_component A p hK⟩

/-- Complete lower circular arc and derived pole for every bounded
representative. -/
theorem boundedLowerExterior_completeCircularArc
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    K ≠ 0 ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
          {q : PlanePoint | q.2 < interfaceY} ∧
      lowerSupportingPole A p ∈
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 := by
  have hK := commonCurvature_ne_zero_of_bounded_lowerExterior
    A hcarrierBounded p
  exact ⟨hK, lowerExterior_connectedComponentIn_eq_circle_of_ne_zero A p hK,
    lowerSupportingPole_mem_lowerExterior_component A p hK⟩


/-- Exact saturation on the source upper exterior locus
`frontier carrier ∩ {y > 1}`. -/
theorem upperOneExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | 1 < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | 1 < q.2} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | 1 < q.2}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | 1 < q.2} :=
  upperExterior_connectedComponentIn_eq_supportAt A p

/-- Exact saturation on the source lower exterior locus
`frontier carrier ∩ {y < -1}`. -/
theorem lowerNegOneExterior_connectedComponentIn_eq_supportAt
    {carrier : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < -1}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < -1} : Set PlanePoint)) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < -1}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < -1} :=
  lowerExterior_connectedComponentIn_eq_supportAt A p

/-- Any actual interface contact on a nonzero support proves that the
interface is below its upper pole. -/
theorem interface_le_supportingCenterAt_add_radius_of_contact
    {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    interfaceY ≤ (A.supportingCenterAt p).2 + |1 / K| := by
  rw [A.supportAt_eq_circleValue_zero p hK] at hcontact
  change circleValue (A.supportingCenterAt p) |1 / K| contact = 0
    at hcontact
  unfold circleValue at hcontact
  rw [hheight] at hcontact
  by_contra htop
  have hlt :
      (A.supportingCenterAt p).2 + |1 / K| < interfaceY :=
    lt_of_not_ge htop
  have hfirst :
      0 < interfaceY - (A.supportingCenterAt p).2 - |1 / K| := by
    linarith
  have hsecond :
      0 < interfaceY - (A.supportingCenterAt p).2 + |1 / K| := by
    linarith [abs_nonneg (1 / K)]
  have hsq :
      |1 / K| ^ 2 <
        (interfaceY - (A.supportingCenterAt p).2) ^ 2 := by
    nlinarith [mul_pos hfirst hsecond]
  nlinarith [sq_nonneg
    (contact.1 - (A.supportingCenterAt p).1)]

/-- Exact lower exterior-component saturation in the nonzero-curvature branch
from one derived support contact with the interface. -/
theorem lowerExterior_connectedComponentIn_eq_supportAt_of_circle_contact
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      A.supportAt p ∩ {q : PlanePoint | q.2 < interfaceY} := by
  apply lowerExterior_connectedComponentIn_eq_supportAt_of_isPreconnected
  exact supportAt_inter_lower_isPreconnected_of_ne_zero_of_le_top
    A p hK
      (interface_le_supportingCenterAt_add_radius_of_contact
        A p hK hcontact hheight)

/-- Literal-circle form of lower component saturation. -/
theorem lowerExterior_connectedComponentIn_eq_circle_of_contact
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) {contact : PlanePoint}
    (hcontact : contact ∈ A.supportAt p)
    (hheight : contact.2 = interfaceY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
      {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
        {q : PlanePoint | q.2 < interfaceY} := by
  rw [lowerExterior_connectedComponentIn_eq_supportAt_of_circle_contact
    A p hK hcontact hheight, A.supportAt_eq_circleValue_zero p hK]

/-- One branch-neutral continuation component reaches an interface in two
ordered actual points and also contains a point strictly on the exterior side.
All three points live in the atlas locus and hence on the actual frontier.
No supporting carrier or component image is supplied. -/
structure TwoInterfaceReach
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (interfaceY : ℝ) where
  left : locus
  right : locus
  exterior : locus
  right_mem_component : right ∈ connectedComponent left
  exterior_mem_component : exterior ∈ connectedComponent left
  left_on_interface : left.1.2 = interfaceY
  right_on_interface : right.1.2 = interfaceY
  left_lt_right : left.1.1 < right.1.1
  exterior_above : interfaceY < exterior.1.2

namespace TwoInterfaceReach

variable {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    {A : BranchNeutralGraphAtlas carrier locus K}
    (R : TwoInterfaceReach A interfaceY)

/-- The reach witnesses are actual frontier points; this follows from their
locus membership rather than from any equality transported through AE sets. -/
theorem points_mem_frontier :
    R.left.1 ∈ frontier carrier ∧
      R.right.1 ∈ frontier carrier ∧
      R.exterior.1 ∈ frontier carrier :=
  ⟨A.locus_subset_frontier R.left.2,
    A.locus_subset_frontier R.right.2,
    A.locus_subset_frontier R.exterior.2⟩

/-- Continuation, not a supplied support equality, puts both the second contact
and the exterior witness on the support selected at the first contact. -/
theorem points_mem_commonSupport :
    R.left.1 ∈ A.supportAt R.left ∧
      R.right.1 ∈ A.supportAt R.left ∧
      R.exterior.1 ∈ A.supportAt R.left := by
  refine ⟨A.base_mem_supportAt R.left, ?_, ?_⟩
  · exact A.connectedComponent_subset_supportAt R.left
      ⟨R.right, R.right_mem_component, rfl⟩
  · exact A.connectedComponent_subset_supportAt R.left
      ⟨R.exterior, R.exterior_mem_component, rfl⟩

/-- Two distinct interface contacts and one exterior point rule out the affine
support alternative.  This uses neither boundedness nor compactness: a line
through two distinct points at the same height is horizontal and cannot also
contain the exterior witness. -/
theorem curvature_ne_zero (R : TwoInterfaceReach A interfaceY) : K ≠ 0 := by
  intro hK
  have hsupport := points_mem_commonSupport R
  have hright := hsupport.2.1
  have hexterior := hsupport.2.2
  unfold BranchNeutralGraphAtlas.supportAt at hright hexterior
  rw [if_pos hK] at hright hexterior
  change R.right.1.2 =
      (A.chart R.left).patch.graph R.left.1.1 +
        deriv (A.chart R.left).patch.graph R.left.1.1 *
          (R.right.1.1 - R.left.1.1) at hright
  change R.exterior.1.2 =
      (A.chart R.left).patch.graph R.left.1.1 +
        deriv (A.chart R.left).patch.graph R.left.1.1 *
          (R.exterior.1.1 - R.left.1.1) at hexterior
  have hbase := congrArg Prod.snd (A.base_eq R.left)
  simp only [GraphPatch.graphTrace] at hbase
  have hslope : deriv (A.chart R.left).patch.graph R.left.1.1 = 0 := by
    rw [R.right_on_interface, hbase, R.left_on_interface] at hright
    nlinarith [R.left_lt_right]
  rw [hslope, zero_mul, add_zero, hbase, R.left_on_interface] at hexterior
  linarith [R.exterior_above]

/-- After the affine branch is discharged, all three actual reach witnesses lie
on the derived literal supporting circle. -/
theorem points_mem_supportingCircle :
    R.left.1 ∈ (A.chart R.left).patch.supportingCircle K R.left.1.1 ∧
      R.right.1 ∈ (A.chart R.left).patch.supportingCircle K R.left.1.1 ∧
      R.exterior.1 ∈ (A.chart R.left).patch.supportingCircle K R.left.1.1 := by
  have hsupport := points_mem_commonSupport R
  unfold BranchNeutralGraphAtlas.supportAt at hsupport
  rw [if_neg (curvature_ne_zero R)] at hsupport
  exact hsupport

/-- The two actual interface contacts select opposite horizontal intersections
of the derived support circle.  In particular the supporting center lies
strictly between their abscissae. -/
theorem ordered_contacts_center :
    R.left.1.1 + R.right.1.1 =
        2 * ((A.chart R.left).patch.supportingCenter K R.left.1.1).1 ∧
      R.left.1.1 <
        ((A.chart R.left).patch.supportingCenter K R.left.1.1).1 ∧
      ((A.chart R.left).patch.supportingCenter K R.left.1.1).1 <
        R.right.1.1 := by
  let center := (A.chart R.left).patch.supportingCenter K R.left.1.1
  let radiusSquared :=
    (1 / ((A.chart R.left).patch.side.areaSign * K)) ^ 2
  have hcircle := R.points_mem_supportingCircle
  have hleftFiber : R.left.1.1 ∈
      circleHorizontalFiber center radiusSquared interfaceY := by
    change (R.left.1.1 - center.1) ^ 2 +
        (interfaceY - center.2) ^ 2 = radiusSquared
    have h := hcircle.1
    change (R.left.1.1 - center.1) ^ 2 +
        (R.left.1.2 - center.2) ^ 2 = radiusSquared at h
    rwa [R.left_on_interface] at h
  have hrightFiber : R.right.1.1 ∈
      circleHorizontalFiber center radiusSquared interfaceY := by
    change (R.right.1.1 - center.1) ^ 2 +
        (interfaceY - center.2) ^ 2 = radiusSquared
    have h := hcircle.2.1
    change (R.right.1.1 - center.1) ^ 2 +
        (R.right.1.2 - center.2) ^ 2 = radiusSquared at h
    rwa [R.right_on_interface] at h
  exact ordered_circle_intersections hleftFiber hrightFiber R.left_lt_right

/-- The full maximal continuation-component image is actual frontier and lies
on the derived support circle.  This is the global consequence available
before identifying that component with a parameterized cap. -/
theorem maximalComponent_subset_frontier_inter_supportingCircle :
    A.maximalComponentTraceImage R.left ⊆
      frontier carrier ∩
        (A.chart R.left).patch.supportingCircle K R.left.1.1 := by
  intro p hp
  have hpComponent : p ∈ connectedComponentIn locus R.left.1 := by
    rwa [A.maximalComponentTraceImage_eq] at hp
  have hpLocus := connectedComponentIn_subset locus R.left.1 hpComponent
  refine ⟨A.locus_subset_frontier hpLocus, ?_⟩
  have hpSupport := A.maximalComponentTraceImage_subset_supportAt R.left hp
  unfold BranchNeutralGraphAtlas.supportAt at hpSupport
  rwa [if_neg (curvature_ne_zero R)] at hpSupport

/-- The actual maximal continuation component has no missing horizontal
coordinate between its two interface contacts.  This is a consequence of
connectedness of the component itself; it does not assume a finite arc list,
compactness of the regular locus, or a complete component image. -/
theorem contactInterval_subset_fst_image_maximalComponent :
    Icc R.left.1.1 R.right.1.1 ⊆
      Prod.fst '' A.maximalComponentTraceImage R.left := by
  intro x hx
  have hleftComponent :
      R.left.1 ∈ connectedComponentIn locus R.left.1 :=
    mem_connectedComponentIn R.left.2
  have hrightComponent :
      R.right.1 ∈ connectedComponentIn locus R.left.1 := by
    rw [connectedComponentIn_eq_image R.left.2]
    exact ⟨R.right, R.right_mem_component, rfl⟩
  have hxImage : x ∈ Prod.fst ''
      connectedComponentIn locus R.left.1 := by
    apply isPreconnected_connectedComponentIn.intermediate_value
      hleftComponent hrightComponent continuous_fst.continuousOn
    exact hx
  rw [A.maximalComponentTraceImage_eq]
  exact hxImage

/-- Pointwise no-gap form: every abscissa between the actual contacts is
realized by an actual frontier point of the same maximal component and that
point satisfies the one derived supporting-circle equation.  The ordinate is
not selected by a minor/major branch. -/
theorem contactInterval_has_actual_circlePoint
    {x : ℝ} (hx : x ∈ Icc R.left.1.1 R.right.1.1) :
    ∃ y : ℝ,
      (x, y) ∈ A.maximalComponentTraceImage R.left ∧
      (x, y) ∈ frontier carrier ∧
      circleValue
        ((A.chart R.left).patch.supportingCenter K R.left.1.1)
          |1 / K| (x, y) = 0 := by
  obtain ⟨q, hqComponent, hqx⟩ :=
    contactInterval_subset_fst_image_maximalComponent R hx
  have hqEq : (x, q.2) = q := by
    apply Prod.ext
    · exact hqx.symm
    · rfl
  have hqActual :=
    R.maximalComponent_subset_frontier_inter_supportingCircle hqComponent
  have hqSupport :=
    A.maximalComponentTraceImage_subset_supportAt R.left hqComponent
  rw [supportAt_eq_circleValue_zero A R.left (curvature_ne_zero R)]
    at hqSupport
  refine ⟨q.2, hqEq ▸ hqComponent, hqEq ▸ hqActual.1, ?_⟩
  exact hqEq ▸ hqSupport

end TwoInterfaceReach
/-- Mixed-coordinate counterpart of `TwoInterfaceReach`.  Its continuation
component may cross vertical circle tangencies and switch occupied-side labels;
the atlas contains neither a global graph axis nor a global side. -/
structure MixedTwoInterfaceReach
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (interfaceY : ℝ) where
  left : locus
  right : locus
  exterior : locus
  right_mem_component : right ∈ connectedComponent left
  exterior_mem_component : exterior ∈ connectedComponent left
  left_on_interface : left.1.2 = interfaceY
  right_on_interface : right.1.2 = interfaceY
  left_lt_right : left.1.1 < right.1.1
  exterior_above : interfaceY < exterior.1.2

namespace MixedTwoInterfaceReach

variable {carrier locus : Set PlanePoint} {K interfaceY : ℝ}
    {A : BranchNeutralMixedGraphAtlas carrier locus K}
    (R : MixedTwoInterfaceReach A interfaceY)

/-- All mixed reach witnesses are actual frontier points. -/
theorem points_mem_frontier :
    R.left.1 ∈ frontier carrier ∧
      R.right.1 ∈ frontier carrier ∧
      R.exterior.1 ∈ frontier carrier :=
  ⟨A.locus_subset_frontier R.left.2,
    A.locus_subset_frontier R.right.2,
    A.locus_subset_frontier R.exterior.2⟩

/-- Topological continuation puts all mixed reach witnesses on the one support
derived at the first contact. -/
theorem points_mem_commonSupport :
    R.left.1 ∈ A.supportAt R.left ∧
      R.right.1 ∈ A.supportAt R.left ∧
      R.exterior.1 ∈ A.supportAt R.left := by
  refine ⟨A.base_mem_supportAt R.left, ?_, ?_⟩
  · exact A.connectedComponent_subset_supportAt R.left
      ⟨R.right, R.right_mem_component, rfl⟩
  · exact A.connectedComponent_subset_supportAt R.left
      ⟨R.exterior, R.exterior_mem_component, rfl⟩

/-- The same geometric reach rules out the affine branch even when the
continuation switches between vertical and horizontal graph coordinates. -/
theorem curvature_ne_zero (R : MixedTwoInterfaceReach A interfaceY) : K ≠ 0 := by
  intro hK
  have hsupport := points_mem_commonSupport R
  have hright := hsupport.2.1
  have hexterior := hsupport.2.2
  unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
    RegularChart.supportAtParameter at hright hexterior
  rw [if_pos hK] at hright hexterior
  cases hC : A.chart R.left with
  | vertical C hcurv hoccupied =>
      simp only [hC, RegularChart.parameter] at hright hexterior
      change R.right.1.2 =
          C.patch.graph R.left.1.1 +
            deriv C.patch.graph R.left.1.1 *
              (R.right.1.1 - R.left.1.1) at hright
      change R.exterior.1.2 =
          C.patch.graph R.left.1.1 +
            deriv C.patch.graph R.left.1.1 *
              (R.exterior.1.1 - R.left.1.1) at hexterior
      have hbaseTrace := A.base_eq R.left
      rw [hC] at hbaseTrace
      have hbase := congrArg Prod.snd hbaseTrace
      change C.patch.graph R.left.1.1 = R.left.1.2 at hbase
      have hslope : deriv C.patch.graph R.left.1.1 = 0 := by
        rw [R.right_on_interface, hbase, R.left_on_interface] at hright
        nlinarith [R.left_lt_right]
      rw [hslope, zero_mul, add_zero, hbase, R.left_on_interface] at hexterior
      linarith [R.exterior_above]
  | horizontal C hcurv hoccupied =>
      simp only [hC, RegularChart.parameter] at hright
      change R.right.1.1 =
          C.patch.graph R.left.1.2 +
            deriv C.patch.graph R.left.1.2 *
              (R.right.1.2 - R.left.1.2) at hright
      have hbaseTrace := A.base_eq R.left
      rw [hC] at hbaseTrace
      have hbase := congrArg Prod.fst hbaseTrace
      change C.patch.graph R.left.1.2 = R.left.1.1 at hbase
      have hbaseI := hbase
      rw [R.left_on_interface] at hbaseI
      rw [R.right_on_interface, R.left_on_interface, sub_self, mul_zero,
        add_zero, hbaseI] at hright
      linarith [R.left_lt_right]

/-- The complete mixed maximal component is actual frontier and lies on its
literal derived support circle.  Unlike the vertical-only predecessor, this
statement remains valid through coordinate tangencies. -/
theorem connectedComponentIn_subset_frontier_inter_circle :
    connectedComponentIn locus R.left.1 ⊆
      frontier carrier ∩
        {q : PlanePoint |
          circleValue (A.supportingCenterAt R.left) |1 / K| q = 0} := by
  intro q hq
  have hqLocus := connectedComponentIn_subset locus R.left.1 hq
  refine ⟨A.locus_subset_frontier hqLocus, ?_⟩
  have hqImage : q ∈
      ((↑) : locus → PlanePoint) '' connectedComponent R.left := by
    rwa [← connectedComponentIn_eq_image R.left.2]
  have hqSupport := A.connectedComponent_subset_supportAt R.left hqImage
  rw [A.supportAt_eq_circleValue_zero R.left R.curvature_ne_zero] at hqSupport
  exact hqSupport

/-- The mixed continuation component has no missing horizontal coordinate
between its two actual interface contacts. -/
theorem contactInterval_subset_fst_image_component :
    Icc R.left.1.1 R.right.1.1 ⊆
      Prod.fst '' connectedComponentIn locus R.left.1 := by
  intro x hx
  have hleftComponent :
      R.left.1 ∈ connectedComponentIn locus R.left.1 :=
    mem_connectedComponentIn R.left.2
  have hrightComponent :
      R.right.1 ∈ connectedComponentIn locus R.left.1 := by
    rw [connectedComponentIn_eq_image R.left.2]
    exact ⟨R.right, R.right_mem_component, rfl⟩
  exact isPreconnected_connectedComponentIn.intermediate_value
    hleftComponent hrightComponent continuous_fst.continuousOn hx

/-- Pointwise no-gap form for the mixed atlas: every intermediate abscissa is
realized by an actual point of the same maximal component on the derived
positive-radius support circle. -/
theorem contactInterval_has_actual_circlePoint
    {x : ℝ} (hx : x ∈ Icc R.left.1.1 R.right.1.1) :
    ∃ y : ℝ,
      (x, y) ∈ connectedComponentIn locus R.left.1 ∧
      (x, y) ∈ frontier carrier ∧
      circleValue (A.supportingCenterAt R.left) |1 / K| (x, y) = 0 := by
  obtain ⟨q, hqComponent, hqx⟩ :=
    R.contactInterval_subset_fst_image_component hx
  have hqEq : (x, q.2) = q := by
    apply Prod.ext
    · exact hqx.symm
    · rfl
  have hqActual :=
    R.connectedComponentIn_subset_frontier_inter_circle hqComponent
  exact ⟨q.2, hqEq ▸ hqComponent, hqEq ▸ hqActual.1, hqEq ▸ hqActual.2⟩

end MixedTwoInterfaceReach


/-- An `x = g(y)` chart can never place its supporting-circle center directly
above or below its base point: the horizontal normal component is nonzero. -/
theorem horizontalSupportingCenter_fst_ne_graphTrace_fst
    (P : CMVTransverseContactVariation.HorizontalGraphPatch)
    {K y : ℝ} (hK : K ≠ 0) :
    (P.supportingCenter K y).1 ≠ (P.graphTrace y).1 := by
  intro heq
  have hsqrt : √(1 + deriv P.graph y ^ 2) ≠ 0 := by positivity
  have hcurvature : -(P.side.areaSign * K) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero P.side.areaSign_ne_zero hK)
  have hterm :
      (1 / √(1 + deriv P.graph y ^ 2)) /
        (-(P.side.areaSign * K)) ≠ 0 :=
    div_ne_zero (one_div_ne_zero hsqrt) hcurvature
  unfold CMVTransverseContactVariation.HorizontalGraphPatch.supportingCenter
    CMVCurvatureIntegration.centerInvariant
    CMVCurvatureIntegration.normalizedTangent at heq
  simp only [CMVTransverseContactVariation.HorizontalGraphPatch.graphTrace,
    CMVTransverseContactVariation.HorizontalGraphPatch.graphVelocity,
    P.euclideanSpeed_graphVelocity] at heq
  apply hterm
  linarith

/-- For a `y = f(x)` chart, vertical center alignment is equivalent to a
horizontal tangent at the base point. -/
theorem deriv_eq_zero_of_supportingCenter_fst_eq_graphTrace_fst
    (P : CMVTwoPatchGraphVariation.GraphPatch)
    {K x : ℝ} (hK : K ≠ 0)
    (hcenter : (P.supportingCenter K x).1 = (P.graphTrace x).1) :
    deriv P.graph x = 0 := by
  have hsqrt : √(1 + deriv P.graph x ^ 2) ≠ 0 := by positivity
  have hcurvature : P.side.areaSign * K ≠ 0 :=
    mul_ne_zero P.side.areaSign_ne_zero hK
  unfold CMVTwoPatchGraphVariation.GraphPatch.supportingCenter
    CMVCurvatureIntegration.centerInvariant
    CMVCurvatureIntegration.normalizedTangent at hcenter
  simp only [CMVTwoPatchGraphVariation.GraphPatch.graphTrace,
    CMVTwoPatchGraphVariation.GraphPatch.graphVelocity,
    P.euclideanSpeed_graphVelocity] at hcenter
  field_simp [hsqrt, hcurvature] at hcenter
  have hdiv : deriv P.graph x / P.side.areaSign = 0 := by
    linarith [hcenter]
  field_simp [P.side.areaSign_ne_zero] at hdiv
  simpa only [mul_zero] using hdiv

/-- The upper pole as an actual point of the complete exterior atlas locus. -/
def upperExteriorPole
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint) :=
  ⟨upperSupportingPole A p,
    connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1
      (upperSupportingPole_mem_upperExterior_component A p hK)⟩

theorem upperExteriorPole_mem_connectedComponent
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    upperExteriorPole A p hK ∈ connectedComponent p := by
  have hpole :=
    upperSupportingPole_mem_upperExterior_component A p hK
  rw [connectedComponentIn_eq_image p.2] at hpole
  rcases hpole with ⟨q, hq, hqeq⟩
  have hqPole : q = upperExteriorPole A p hK :=
    Subtype.ext hqeq
  rwa [← hqPole]

/-- The lower pole as an actual point of the lower exterior atlas locus. -/
def lowerExteriorPole
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint) :=
  ⟨lowerSupportingPole A p,
    connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1
      (lowerSupportingPole_mem_lowerExterior_component A p hK)⟩

theorem lowerExteriorPole_mem_connectedComponent
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    lowerExteriorPole A p hK ∈ connectedComponent p := by
  have hpole :=
    lowerSupportingPole_mem_lowerExterior_component A p hK
  rw [connectedComponentIn_eq_image p.2] at hpole
  rcases hpole with ⟨q, hq, hqeq⟩
  have hqPole : q = lowerExteriorPole A p hK :=
    Subtype.ext hqeq
  rwa [← hqPole]

/-- The derived upper pole necessarily uses a `y = f(x)` chart and that chart
has horizontal tangent.  Both facts come from complete support saturation and
center propagation; no pole chart or tangent is supplied. -/
theorem upperExteriorPole_verticalChart_and_tangent
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint))
    (hK : K ≠ 0) :
    ∃ (C : ActualRegularGraphChart carrier)
      (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
        C.patch.orientedGraphCurvature z = K)
      (hoccupied : ∀ z ∈ Ioo C.patch.a C.patch.b,
        ∀ᶠ q in 𝓝 (C.patch.graphTrace z),
          (q ∈ carrier ↔
            q ∈ C.patch.occupiedGraphDomain C.patch.graph)),
      A.chart (upperExteriorPole A p hK) =
          RegularChart.vertical C hcurv hoccupied ∧
        deriv C.patch.graph (upperExteriorPole A p hK).1.1 = 0 := by
  let pole := upperExteriorPole A p hK
  have hcenter := supportingCenterAt_eq_of_mem_connectedComponent
    A p pole hK (upperExteriorPole_mem_connectedComponent A p hK)
  have hcenterFst :
      (A.supportingCenterAt pole).1 = pole.1.1 := by
    rw [hcenter]
    rfl
  cases hchart : A.chart pole with
  | vertical C hcurv hoccupied =>
      have hbase := A.base_eq pole
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace] at hbase
      have hcenterAlign :
          (C.patch.supportingCenter K pole.1.1).1 =
            (C.patch.graphTrace pole.1.1).1 := by
        rw [hbase]
        simpa only [BranchNeutralMixedGraphAtlas.supportingCenterAt, hchart]
          using hcenterFst
      exact ⟨C, hcurv, hoccupied, rfl,
        deriv_eq_zero_of_supportingCenter_fst_eq_graphTrace_fst
          C.patch hK hcenterAlign⟩
  | horizontal C hcurv hoccupied =>
      exfalso
      apply horizontalSupportingCenter_fst_ne_graphTrace_fst C.patch hK
      have hbase := A.base_eq pole
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace] at hbase
      rw [hbase]
      simpa only [BranchNeutralMixedGraphAtlas.supportingCenterAt, hchart]
        using hcenterFst

/-- Reflected pole-chart and tangent derivation. -/
theorem lowerExteriorPole_verticalChart_and_tangent
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint))
    (hK : K ≠ 0) :
    ∃ (C : ActualRegularGraphChart carrier)
      (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
        C.patch.orientedGraphCurvature z = K)
      (hoccupied : ∀ z ∈ Ioo C.patch.a C.patch.b,
        ∀ᶠ q in 𝓝 (C.patch.graphTrace z),
          (q ∈ carrier ↔
            q ∈ C.patch.occupiedGraphDomain C.patch.graph)),
      A.chart (lowerExteriorPole A p hK) =
          RegularChart.vertical C hcurv hoccupied ∧
        deriv C.patch.graph (lowerExteriorPole A p hK).1.1 = 0 := by
  let pole := lowerExteriorPole A p hK
  have hcenter := supportingCenterAt_eq_of_mem_connectedComponent
    A p pole hK (lowerExteriorPole_mem_connectedComponent A p hK)
  have hcenterFst :
      (A.supportingCenterAt pole).1 = pole.1.1 := by
    rw [hcenter]
    rfl
  cases hchart : A.chart pole with
  | vertical C hcurv hoccupied =>
      have hbase := A.base_eq pole
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace] at hbase
      have hcenterAlign :
          (C.patch.supportingCenter K pole.1.1).1 =
            (C.patch.graphTrace pole.1.1).1 := by
        rw [hbase]
        simpa only [BranchNeutralMixedGraphAtlas.supportingCenterAt, hchart]
          using hcenterFst
      exact ⟨C, hcurv, hoccupied, rfl,
        deriv_eq_zero_of_supportingCenter_fst_eq_graphTrace_fst
          C.patch hK hcenterAlign⟩
  | horizontal C hcurv hoccupied =>
      exfalso
      apply horizontalSupportingCenter_fst_ne_graphTrace_fst C.patch hK
      have hbase := A.base_eq pole
      rw [hchart] at hbase
      simp only [RegularChart.parameter, RegularChart.trace] at hbase
      rw [hbase]
      simpa only [BranchNeutralMixedGraphAtlas.supportingCenterAt, hchart]
        using hcenterFst

/-- A nonempty bounded planar set has an actual frontier point maximizing the
second coordinate over its compact closure.  Compactness is used only for the
closed closure, never for the open set or an exterior locus. -/
theorem exists_frontier_snd_max_of_isBounded
    {carrier : Set PlanePoint} (hbounded : Bornology.IsBounded carrier)
    (hne : carrier.Nonempty) :
    ∃ top ∈ frontier carrier,
      ∀ q ∈ closure carrier, q.2 ≤ top.2 := by
  have hcompact : IsCompact (closure carrier) := hbounded.isCompact_closure
  obtain ⟨top, htopClosure, htopMax⟩ :=
    hcompact.exists_isMaxOn hne.closure continuous_snd.continuousOn
  have htopFrontier : top ∈ frontier carrier := by
    rw [closure_eq_interior_union_frontier] at htopClosure
    rcases htopClosure with htopInterior | htopFrontier
    · exfalso
      obtain ⟨epsilon, hepsilon, hball⟩ :=
        Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds htopInterior)
      let q : PlanePoint := (top.1, top.2 + epsilon / 2)
      have hqBall : q ∈ Metric.ball top epsilon := by
        rw [Metric.mem_ball, Prod.dist_eq]
        dsimp only [q]
        rw [dist_self,
          max_eq_right (dist_nonneg : 0 ≤ dist (top.2 + epsilon / 2) top.2),
          Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
      have hqClosure : q ∈ closure carrier :=
        subset_closure (interior_subset (hball hqBall))
      have hqMax := htopMax hqClosure
      change top.2 + epsilon / 2 ≤ top.2 at hqMax
      linarith
    · exact htopFrontier
  exact ⟨top, htopFrontier, fun _q hq => htopMax hq⟩

/-- Reflected compact-closure extremum: the minimum second coordinate is also
attained on the actual frontier. -/
theorem exists_frontier_snd_min_of_isBounded
    {carrier : Set PlanePoint} (hbounded : Bornology.IsBounded carrier)
    (hne : carrier.Nonempty) :
    ∃ bottom ∈ frontier carrier,
      ∀ q ∈ closure carrier, bottom.2 ≤ q.2 := by
  have hcompact : IsCompact (closure carrier) := hbounded.isCompact_closure
  obtain ⟨bottom, hbottomClosure, hbottomMin⟩ :=
    hcompact.exists_isMinOn hne.closure continuous_snd.continuousOn
  have hbottomFrontier : bottom ∈ frontier carrier := by
    rw [closure_eq_interior_union_frontier] at hbottomClosure
    rcases hbottomClosure with hbottomInterior | hbottomFrontier
    · exfalso
      obtain ⟨epsilon, hepsilon, hball⟩ :=
        Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hbottomInterior)
      let q : PlanePoint := (bottom.1, bottom.2 - epsilon / 2)
      have hqBall : q ∈ Metric.ball bottom epsilon := by
        rw [Metric.mem_ball, Prod.dist_eq]
        dsimp only [q]
        rw [dist_self,
          max_eq_right (dist_nonneg : 0 ≤ dist (bottom.2 - epsilon / 2) bottom.2),
          Real.dist_eq, abs_of_nonpos (by linarith)]
        linarith
      have hqClosure : q ∈ closure carrier :=
        subset_closure (interior_subset (hball hqBall))
      have hqMin := hbottomMin hqClosure
      change bottom.2 ≤ bottom.2 - epsilon / 2 at hqMin
      linarith
    · exact hbottomFrontier
  exact ⟨bottom, hbottomFrontier, fun _q hq => hbottomMin hq⟩

/-- A truthful vertical graph germ at a global upper boundary point must occupy
the side below the graph.  The conclusion is derived from actual nearby carrier
points, not supplied as pole geometry. -/
theorem occupiedSide_eq_below_of_snd_max
    {carrier : Set PlanePoint} (P : GraphPatch) {x : ℝ}
    (hoccupied :
      ∀ᶠ q in 𝓝 (P.graphTrace x),
        (q ∈ carrier ↔ q ∈ P.occupiedGraphDomain P.graph))
    (hmax : ∀ q ∈ carrier, q.2 ≤ (P.graphTrace x).2) :
    P.side = .below := by
  cases hside : P.side with
  | below => rfl
  | above =>
      exfalso
      obtain ⟨epsilon, hepsilon, hball⟩ :=
        Metric.mem_nhds_iff.mp hoccupied
      let q : PlanePoint := (x, P.graph x + epsilon / 2)
      have hqBall : q ∈ Metric.ball (P.graphTrace x) epsilon := by
        rw [Metric.mem_ball, Prod.dist_eq]
        dsimp only [q, GraphPatch.graphTrace]
        rw [dist_self,
          max_eq_right
            (dist_nonneg : 0 ≤ dist (P.graph x + epsilon / 2) (P.graph x)),
          Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
      have hqDomain : q ∈ P.occupiedGraphDomain P.graph := by
        simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq]
        dsimp only [q]
        linarith
      have hqCarrier : q ∈ carrier := (hball hqBall).mpr hqDomain
      have hqMax := hmax q hqCarrier
      dsimp only [q, GraphPatch.graphTrace] at hqMax
      linarith

/-- Lower-extremum counterpart of `occupiedSide_eq_below_of_snd_max`. -/
theorem occupiedSide_eq_above_of_snd_min
    {carrier : Set PlanePoint} (P : GraphPatch) {x : ℝ}
    (hoccupied :
      ∀ᶠ q in 𝓝 (P.graphTrace x),
        (q ∈ carrier ↔ q ∈ P.occupiedGraphDomain P.graph))
    (hmin : ∀ q ∈ carrier, (P.graphTrace x).2 ≤ q.2) :
    P.side = .above := by
  cases hside : P.side with
  | below =>
      exfalso
      obtain ⟨epsilon, hepsilon, hball⟩ :=
        Metric.mem_nhds_iff.mp hoccupied
      let q : PlanePoint := (x, P.graph x - epsilon / 2)
      have hqBall : q ∈ Metric.ball (P.graphTrace x) epsilon := by
        rw [Metric.mem_ball, Prod.dist_eq]
        dsimp only [q, GraphPatch.graphTrace]
        rw [dist_self,
          max_eq_right
            (dist_nonneg : 0 ≤ dist (P.graph x - epsilon / 2) (P.graph x)),
          Real.dist_eq, abs_of_nonpos (by linarith)]
        linarith
      have hqDomain : q ∈ P.occupiedGraphDomain P.graph := by
        simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq]
        dsimp only [q]
        linarith
      have hqCarrier : q ∈ carrier := (hball hqBall).mpr hqDomain
      have hqMin := hmin q hqCarrier
      dsimp only [q, GraphPatch.graphTrace] at hqMin
      linarith
  | above => rfl



/-- At an upper exterior pole, the explicit `below` occupied-side convention
and a supporting center below the pole force negative common occupied-side
curvature. -/
theorem commonCurvature_neg_of_below_tangent_center_below
    {carrier : Set PlanePoint} (A : ActualRegularGraphChart carrier)
    {K x : ℝ} (_hK : K ≠ 0) (hside : A.patch.side = .below)
    (htangent : deriv A.patch.graph x = 0)
    (hcenter :
      (A.patch.supportingCenter K x).2 <
        (A.patch.graphTrace x).2) :
    K < 0 := by
  have hspeed :
      CMVCurvatureIntegration.euclideanSpeed A.patch.graphVelocity x = 1 := by
    unfold CMVCurvatureIntegration.euclideanSpeed
      CMVTwoPatchGraphVariation.GraphPatch.graphVelocity
    rw [htangent]
    norm_num
  have hformula :
      (A.patch.supportingCenter K x).2 =
        (A.patch.graphTrace x).2 + 1 / K := by
    unfold CMVTwoPatchGraphVariation.GraphPatch.supportingCenter
      CMVCurvatureIntegration.centerInvariant
      CMVCurvatureIntegration.normalizedTangent
    simp only [CMVTwoPatchGraphVariation.GraphPatch.graphVelocity,
      hspeed, one_div, div_one]
    rw [hside]
    simp only [CMVTwoPatchGraphVariation.OccupiedSide.areaSign_below,
      one_mul]
  rw [hformula] at hcenter
  simp only [one_div] at hcenter
  have hinvneg : K⁻¹ < 0 := by linarith [hcenter]
  exact inv_lt_zero.mp hinvneg

/-- Lower-pole counterpart: with the explicit `above` occupied-side convention
and the support center above the pole, the same common curvature is negative. -/
theorem commonCurvature_neg_of_above_tangent_center_above
    {carrier : Set PlanePoint} (A : ActualRegularGraphChart carrier)
    {K x : ℝ} (hK : K ≠ 0) (hside : A.patch.side = .above)
    (htangent : deriv A.patch.graph x = 0)
    (hcenter :
      (A.patch.graphTrace x).2 <
        (A.patch.supportingCenter K x).2) :
    K < 0 := by
  have hspeed :
      CMVCurvatureIntegration.euclideanSpeed A.patch.graphVelocity x = 1 := by
    unfold CMVCurvatureIntegration.euclideanSpeed
      CMVTwoPatchGraphVariation.GraphPatch.graphVelocity
    rw [htangent]
    norm_num
  have hformula :
      (A.patch.supportingCenter K x).2 =
        (A.patch.graphTrace x).2 - 1 / K := by
    unfold CMVTwoPatchGraphVariation.GraphPatch.supportingCenter
      CMVCurvatureIntegration.centerInvariant
      CMVCurvatureIntegration.normalizedTangent
    simp only [CMVTwoPatchGraphVariation.GraphPatch.graphVelocity,
      hspeed, one_div, div_one]
    rw [hside]
    simp only [CMVTwoPatchGraphVariation.OccupiedSide.areaSign_above]
    field_simp [hK]
    ring
  rw [hformula] at hcenter
  simp only [one_div] at hcenter
  have hinvneg : K⁻¹ < 0 := by linarith [hcenter]
  exact inv_lt_zero.mp hinvneg
/-- Bounded representative geometry forces negative common occupied-side
curvature on every nonempty upper exterior locus.  The proof selects the actual
global upper frontier extremum on the compact closure, identifies it with the
derived supporting pole using complete component saturation, and reads the
occupied side from the atlas germ. -/
theorem commonCurvature_neg_of_bounded_upperExterior
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    K < 0 := by
  have hcarrierNonempty : carrier.Nonempty := by
    apply closure_nonempty_iff.mp
    exact ⟨p.1, frontier_subset_closure p.2.1⟩
  obtain ⟨top, htopFrontier, htopMax⟩ :=
    exists_frontier_snd_max_of_isBounded hcarrierBounded hcarrierNonempty
  have htopAbove : interfaceY < top.2 :=
    p.2.2.trans_le (htopMax p.1 (frontier_subset_closure p.2.1))
  let topPoint :
      (frontier carrier ∩
        {q : PlanePoint | interfaceY < q.2} : Set PlanePoint) :=
    ⟨top, htopFrontier, htopAbove⟩
  have hcomplete :=
    boundedUpperExterior_completeCircularArc A hcarrierBounded topPoint
  have hK : K ≠ 0 := hcomplete.1
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have htopCircle :
      circleValue (A.supportingCenterAt topPoint) |1 / K| top = 0 := by
    have htopSupport := A.base_mem_supportAt topPoint
    rwa [A.supportAt_eq_circleValue_zero topPoint hK] at htopSupport
  have hpoleFrontier :
      upperSupportingPole A topPoint ∈ frontier carrier :=
    (connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) top
        hcomplete.2.2).1
  have hpoleMax :=
    htopMax (upperSupportingPole A topPoint)
      (frontier_subset_closure hpoleFrontier)
  have htopSnd :
      top.2 = (A.supportingCenterAt topPoint).2 + |1 / K| := by
    apply le_antisymm
    · exact (circleValue_zero_snd_bounds hradius htopCircle).2
    · simpa only [upperSupportingPole] using hpoleMax
  have htopFst : top.1 = (A.supportingCenterAt topPoint).1 := by
    unfold circleValue at htopCircle
    rw [htopSnd] at htopCircle
    nlinarith
  have htopEqPole : top = upperSupportingPole A topPoint := by
    apply Prod.ext
    · exact htopFst
    · simpa only [upperSupportingPole] using htopSnd
  let pole := upperExteriorPole A topPoint hK
  have hpoleVal : pole.1 = top := by
    change upperSupportingPole A topPoint = top
    exact htopEqPole.symm
  obtain ⟨C, hcurv, hoccupied, hchart, htangent⟩ :=
    upperExteriorPole_verticalChart_and_tangent A topPoint hK
  have hpoleInterior := A.base_interior pole
  rw [hchart] at hpoleInterior
  simp only [RegularChart.parameter, RegularChart.parameterInterval]
    at hpoleInterior
  have hpoleBase := A.base_eq pole
  rw [hchart] at hpoleBase
  simp only [RegularChart.parameter, RegularChart.trace] at hpoleBase
  have hside : C.patch.side = .below := by
    apply occupiedSide_eq_below_of_snd_max C.patch
      (hoccupied pole.1.1 hpoleInterior)
    intro q hq
    rw [hpoleBase, hpoleVal]
    exact htopMax q (subset_closure hq)
  have hcenterPropagation :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A topPoint pole hK (upperExteriorPole_mem_connectedComponent A topPoint hK)
  have hcenterEq :
      C.patch.supportingCenter K pole.1.1 =
        A.supportingCenterAt topPoint := by
    rw [← hcenterPropagation]
    unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
    rw [hchart]
  have hcenterBelow :
      (C.patch.supportingCenter K pole.1.1).2 <
        (C.patch.graphTrace pole.1.1).2 := by
    rw [hcenterEq, hpoleBase, hpoleVal, htopSnd]
    exact lt_add_of_pos_right _ hradius
  exact commonCurvature_neg_of_below_tangent_center_below
    C hK hside htangent hcenterBelow

/-- The reflected lower-exterior argument derives the occupied-above pole germ
and the same negative common curvature. -/
theorem commonCurvature_neg_of_bounded_lowerExterior
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    K < 0 := by
  have hcarrierNonempty : carrier.Nonempty := by
    apply closure_nonempty_iff.mp
    exact ⟨p.1, frontier_subset_closure p.2.1⟩
  obtain ⟨bottom, hbottomFrontier, hbottomMin⟩ :=
    exists_frontier_snd_min_of_isBounded hcarrierBounded hcarrierNonempty
  have hbottomBelow : bottom.2 < interfaceY :=
    (hbottomMin p.1 (frontier_subset_closure p.2.1)).trans_lt p.2.2
  let bottomPoint :
      (frontier carrier ∩
        {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint) :=
    ⟨bottom, hbottomFrontier, hbottomBelow⟩
  have hcomplete :=
    boundedLowerExterior_completeCircularArc A hcarrierBounded bottomPoint
  have hK : K ≠ 0 := hcomplete.1
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hbottomCircle :
      circleValue (A.supportingCenterAt bottomPoint) |1 / K| bottom = 0 := by
    have hbottomSupport := A.base_mem_supportAt bottomPoint
    rwa [A.supportAt_eq_circleValue_zero bottomPoint hK] at hbottomSupport
  have hpoleFrontier :
      lowerSupportingPole A bottomPoint ∈ frontier carrier :=
    (connectedComponentIn_subset
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) bottom
        hcomplete.2.2).1
  have hpoleMin :=
    hbottomMin (lowerSupportingPole A bottomPoint)
      (frontier_subset_closure hpoleFrontier)
  have hbottomSnd :
      bottom.2 = (A.supportingCenterAt bottomPoint).2 - |1 / K| := by
    apply le_antisymm
    · simpa only [lowerSupportingPole] using hpoleMin
    · exact (circleValue_zero_snd_bounds hradius hbottomCircle).1
  have hbottomFst : bottom.1 = (A.supportingCenterAt bottomPoint).1 := by
    unfold circleValue at hbottomCircle
    rw [hbottomSnd] at hbottomCircle
    nlinarith
  have hbottomEqPole : bottom = lowerSupportingPole A bottomPoint := by
    apply Prod.ext
    · exact hbottomFst
    · simpa only [lowerSupportingPole] using hbottomSnd
  let pole := lowerExteriorPole A bottomPoint hK
  have hpoleVal : pole.1 = bottom := by
    change lowerSupportingPole A bottomPoint = bottom
    exact hbottomEqPole.symm
  obtain ⟨C, hcurv, hoccupied, hchart, htangent⟩ :=
    lowerExteriorPole_verticalChart_and_tangent A bottomPoint hK
  have hpoleInterior := A.base_interior pole
  rw [hchart] at hpoleInterior
  simp only [RegularChart.parameter, RegularChart.parameterInterval]
    at hpoleInterior
  have hpoleBase := A.base_eq pole
  rw [hchart] at hpoleBase
  simp only [RegularChart.parameter, RegularChart.trace] at hpoleBase
  have hside : C.patch.side = .above := by
    apply occupiedSide_eq_above_of_snd_min C.patch
      (hoccupied pole.1.1 hpoleInterior)
    intro q hq
    rw [hpoleBase, hpoleVal]
    exact hbottomMin q (subset_closure hq)
  have hcenterPropagation :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A bottomPoint pole hK
        (lowerExteriorPole_mem_connectedComponent A bottomPoint hK)
  have hcenterEq :
      C.patch.supportingCenter K pole.1.1 =
        A.supportingCenterAt bottomPoint := by
    rw [← hcenterPropagation]
    unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
    rw [hchart]
  have hcenterAbove :
      (C.patch.graphTrace pole.1.1).2 <
        (C.patch.supportingCenter K pole.1.1).2 := by
    rw [hcenterEq, hpoleBase, hpoleVal, hbottomSnd]
    linarith
  exact commonCurvature_neg_of_above_tangent_center_above
    C hK hside htangent hcenterAbove

/-- The bounded upper-exterior conclusion in its final per-component form:
the common occupied curvature is negative, the component is the complete
supporting-circle clip, and its geometric upper pole is actual frontier. -/
theorem boundedUpperExterior_completeCircularArc_and_curvature_neg
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    K < 0 ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
          {q : PlanePoint | interfaceY < q.2} ∧
      upperSupportingPole A p ∈
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) p.1 := by
  have hcomplete :=
    boundedUpperExterior_completeCircularArc A hcarrierBounded p
  exact ⟨commonCurvature_neg_of_bounded_upperExterior
    A hcarrierBounded p, hcomplete.2⟩

/-- Reflected final per-component conclusion for the lower exterior locus. -/
theorem boundedLowerExterior_completeCircularArc_and_curvature_neg
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    K < 0 ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 =
        {q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩
          {q : PlanePoint | q.2 < interfaceY} ∧
      lowerSupportingPole A p ∈
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) p.1 := by
  have hcomplete :=
    boundedLowerExterior_completeCircularArc A hcarrierBounded p
  exact ⟨commonCurvature_neg_of_bounded_lowerExterior
    A hcarrierBounded p, hcomplete.2⟩

/-- Final two-sided inventory statement: opposite nonempty exterior loci
derive the global reach, each entire exterior locus is one continuation
component, and both common occupied curvatures are negative. -/
theorem twoSidedExterior_unique_components_and_curvature_neg
    {carrier : Set PlanePoint}
    {KUpper KLower lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) KUpper)
    (ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) KLower)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    KUpper < 0 ∧ KLower < 0 ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) pUpper.1 =
        frontier carrier ∩ {q : PlanePoint | upperY < q.2} ∧
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) pLower.1 =
        frontier carrier ∩ {q : PlanePoint | q.2 < lowerY} := by
  have hcomponents :=
    twoSidedExterior_unique_components AUpper ALower hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hlowerUpper pUpper pLower
  exact ⟨commonCurvature_neg_of_bounded_upperExterior
      AUpper hcarrierBounded pUpper,
    commonCurvature_neg_of_bounded_lowerExterior
      ALower hcarrierBounded pLower,
    hcomponents⟩

/-- Once negative curvature and the derived upper-pole center order are known,
the chart label itself is forced to be `below`. -/
theorem occupiedSide_eq_below_of_tangent_center_below_of_curvature_neg
    (P : GraphPatch) {K x : ℝ}
    (hK : K < 0) (htangent : deriv P.graph x = 0)
    (hcenter :
      (P.supportingCenter K x).2 < (P.graphTrace x).2) :
    P.side = .below := by
  cases hside : P.side with
  | below => rfl
  | above =>
      exfalso
      have hspeed :
          CMVCurvatureIntegration.euclideanSpeed P.graphVelocity x = 1 := by
        unfold CMVCurvatureIntegration.euclideanSpeed
          CMVTwoPatchGraphVariation.GraphPatch.graphVelocity
        rw [htangent]
        norm_num
      have hformula :
          (P.supportingCenter K x).2 =
            (P.graphTrace x).2 - 1 / K := by
        unfold CMVTwoPatchGraphVariation.GraphPatch.supportingCenter
          CMVCurvatureIntegration.centerInvariant
          CMVCurvatureIntegration.normalizedTangent
        simp only [CMVTwoPatchGraphVariation.GraphPatch.graphVelocity,
          hspeed, one_div, div_one]
        rw [hside]
        simp only [CMVTwoPatchGraphVariation.OccupiedSide.areaSign_above]
        field_simp [hK.ne]
        ring
      have hinvneg : K⁻¹ < 0 := inv_lt_zero.mpr hK
      rw [hformula] at hcenter
      simp only [one_div] at hcenter
      linarith

/-- Reflected forced-label theorem at a lower pole. -/
theorem occupiedSide_eq_above_of_tangent_center_above_of_curvature_neg
    (P : GraphPatch) {K x : ℝ}
    (hK : K < 0) (htangent : deriv P.graph x = 0)
    (hcenter :
      (P.graphTrace x).2 < (P.supportingCenter K x).2) :
    P.side = .above := by
  cases hside : P.side with
  | below =>
      exfalso
      have hspeed :
          CMVCurvatureIntegration.euclideanSpeed P.graphVelocity x = 1 := by
        unfold CMVCurvatureIntegration.euclideanSpeed
          CMVTwoPatchGraphVariation.GraphPatch.graphVelocity
        rw [htangent]
        norm_num
      have hformula :
          (P.supportingCenter K x).2 =
            (P.graphTrace x).2 + 1 / K := by
        unfold CMVTwoPatchGraphVariation.GraphPatch.supportingCenter
          CMVCurvatureIntegration.centerInvariant
          CMVCurvatureIntegration.normalizedTangent
        simp only [CMVTwoPatchGraphVariation.GraphPatch.graphVelocity,
          hspeed, one_div, div_one]
        rw [hside]
        simp only [CMVTwoPatchGraphVariation.OccupiedSide.areaSign_below,
          one_mul]
      have hinvneg : K⁻¹ < 0 := inv_lt_zero.mpr hK
      rw [hformula] at hcenter
      simp only [one_div] at hcenter
      linarith
  | above => rfl

/-- Complete derived upper-pole payload for an arbitrary point of a nonempty
bounded upper exterior locus.  It exposes the actual atlas chart, truthful
occupied germ, horizontal tangent, forced occupied-below convention, supporting
center order, and negative common curvature without accepting pole geometry as
an input. -/
theorem boundedUpperExterior_derivedPoleGeometry
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | interfaceY < q.2}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | interfaceY < q.2} : Set PlanePoint)) :
    ∃ (hK : K ≠ 0) (C : ActualRegularGraphChart carrier)
      (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
        C.patch.orientedGraphCurvature z = K)
      (hoccupied : ∀ z ∈ Ioo C.patch.a C.patch.b,
        ∀ᶠ q in 𝓝 (C.patch.graphTrace z),
          (q ∈ carrier ↔ q ∈ C.patch.occupiedGraphDomain C.patch.graph)),
      A.chart (upperExteriorPole A p hK) =
          RegularChart.vertical C hcurv hoccupied ∧
        deriv C.patch.graph (upperExteriorPole A p hK).1.1 = 0 ∧
        C.patch.side = .below ∧
        (C.patch.supportingCenter K
            (upperExteriorPole A p hK).1.1).2 <
          (C.patch.graphTrace (upperExteriorPole A p hK).1.1).2 ∧
        K < 0 := by
  let hK : K ≠ 0 :=
    commonCurvature_ne_zero_of_bounded_upperExterior A hcarrierBounded p
  let pole := upperExteriorPole A p hK
  obtain ⟨C, hcurv, hoccupied, hchart, htangent⟩ :=
    upperExteriorPole_verticalChart_and_tangent A p hK
  have hpoleBase := A.base_eq pole
  rw [hchart] at hpoleBase
  simp only [RegularChart.parameter, RegularChart.trace] at hpoleBase
  have hcenterPropagation :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A p pole hK (upperExteriorPole_mem_connectedComponent A p hK)
  have hcenterEq :
      C.patch.supportingCenter K pole.1.1 =
        A.supportingCenterAt p := by
    rw [← hcenterPropagation]
    unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
    rw [hchart]
  have hcenterBelow :
      (C.patch.supportingCenter K pole.1.1).2 <
        (C.patch.graphTrace pole.1.1).2 := by
    rw [hcenterEq, hpoleBase]
    change (A.supportingCenterAt p).2 <
      (upperSupportingPole A p).2
    simp only [upperSupportingPole]
    exact lt_add_of_pos_right _
      (abs_pos.mpr (one_div_ne_zero hK))
  have hneg :=
    commonCurvature_neg_of_bounded_upperExterior A hcarrierBounded p
  have hside :=
    occupiedSide_eq_below_of_tangent_center_below_of_curvature_neg
      C.patch hneg htangent hcenterBelow
  exact ⟨hK, C, hcurv, hoccupied, hchart, htangent, hside,
    hcenterBelow, hneg⟩

/-- Complete reflected lower-pole payload, including the forced occupied-above
convention. -/
theorem boundedLowerExterior_derivedPoleGeometry
    {carrier : Set PlanePoint} {K interfaceY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < interfaceY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (p : (frontier carrier ∩
      {q : PlanePoint | q.2 < interfaceY} : Set PlanePoint)) :
    ∃ (hK : K ≠ 0) (C : ActualRegularGraphChart carrier)
      (hcurv : ∀ z ∈ Ioo C.patch.a C.patch.b,
        C.patch.orientedGraphCurvature z = K)
      (hoccupied : ∀ z ∈ Ioo C.patch.a C.patch.b,
        ∀ᶠ q in 𝓝 (C.patch.graphTrace z),
          (q ∈ carrier ↔ q ∈ C.patch.occupiedGraphDomain C.patch.graph)),
      A.chart (lowerExteriorPole A p hK) =
          RegularChart.vertical C hcurv hoccupied ∧
        deriv C.patch.graph (lowerExteriorPole A p hK).1.1 = 0 ∧
        C.patch.side = .above ∧
        (C.patch.graphTrace (lowerExteriorPole A p hK).1.1).2 <
          (C.patch.supportingCenter K
            (lowerExteriorPole A p hK).1.1).2 ∧
        K < 0 := by
  let hK : K ≠ 0 :=
    commonCurvature_ne_zero_of_bounded_lowerExterior A hcarrierBounded p
  let pole := lowerExteriorPole A p hK
  obtain ⟨C, hcurv, hoccupied, hchart, htangent⟩ :=
    lowerExteriorPole_verticalChart_and_tangent A p hK
  have hpoleBase := A.base_eq pole
  rw [hchart] at hpoleBase
  simp only [RegularChart.parameter, RegularChart.trace] at hpoleBase
  have hcenterPropagation :=
    supportingCenterAt_eq_of_mem_connectedComponent
      A p pole hK (lowerExteriorPole_mem_connectedComponent A p hK)
  have hcenterEq :
      C.patch.supportingCenter K pole.1.1 =
        A.supportingCenterAt p := by
    rw [← hcenterPropagation]
    unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
    rw [hchart]
  have hcenterAbove :
      (C.patch.graphTrace pole.1.1).2 <
        (C.patch.supportingCenter K pole.1.1).2 := by
    rw [hcenterEq, hpoleBase]
    change (lowerSupportingPole A p).2 <
      (A.supportingCenterAt p).2
    simp only [lowerSupportingPole]
    linarith [abs_pos.mpr (one_div_ne_zero hK)]
  have hneg :=
    commonCurvature_neg_of_bounded_lowerExterior A hcarrierBounded p
  have hside :=
    occupiedSide_eq_above_of_tangent_center_above_of_curvature_neg
      C.patch hneg htangent hcenterAbove
  exact ⟨hK, C, hcurv, hoccupied, hchart, htangent, hside,
    hcenterAbove, hneg⟩

/-! ## Strict-slab component and circle-branch inventory -/

/-- Local saturation identifies the actual frontier component with the
component cut out of its propagated support set.  The right-hand side remains
a connected component: an open slab can cut one supporting circle into two
distinct branches. -/
theorem connectedComponentIn_eq_connectedComponentIn_supportAt_inter
    {carrier H : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier (frontier carrier ∩ H) K)
    (p : (frontier carrier ∩ H : Set PlanePoint)) :
    connectedComponentIn (frontier carrier ∩ H) p.1 =
      connectedComponentIn (A.supportAt p ∩ H) p.1 := by
  apply connectedComponentIn_eq_supportPortion_of_local_saturation
      isClosed_frontier p.2
      ((connectedComponentIn_subset (A.supportAt p ∩ H) p.1).trans inter_subset_right)
      (mem_connectedComponentIn ⟨A.base_mem_supportAt p, p.2.2⟩)
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn p.2)
    intro q hq
    exact ⟨A.connectedComponentIn_subset_supportAt p hq,
      (connectedComponentIn_subset (frontier carrier ∩ H) p.1 hq).2⟩
  · intro q hq
    have hqLocus : q ∈ frontier carrier ∩ H :=
      connectedComponentIn_subset (frontier carrier ∩ H) p.1 hq
    let q' : (frontier carrier ∩ H : Set PlanePoint) := ⟨q, hqLocus⟩
    have hqSubtype : q' ∈ connectedComponent p := by
      rw [connectedComponentIn_eq_image p.2] at hq
      rcases hq with ⟨r, hr, hrq⟩
      have hrq' : r = q' := Subtype.ext hrq
      rwa [← hrq']
    have hsupportEq : A.supportAt q' = A.supportAt p :=
      A.supportAt_eq_of_mem_connectedComponent p q' hqSubtype
    rcases A.exists_open_supportAt_inter_subset_connectedComponentIn q' with
      ⟨W, hWopen, hqW, hWsubset⟩
    refine ⟨W, hWopen, hqW, ?_⟩
    intro z hz
    have hzSupportQ : z ∈ A.supportAt q' := by
      rw [hsupportEq]
      exact (connectedComponentIn_subset (A.supportAt p ∩ H) p.1 hz.1).1
    have hzComponentQ := hWsubset ⟨hzSupportQ, hz.2⟩
    have hcomponentEq :
        connectedComponentIn (frontier carrier ∩ H) p.1 =
          connectedComponentIn (frontier carrier ∩ H) q'.1 :=
      connectedComponentIn_eq hq
    rwa [hcomponentEq]
  · exact isPreconnected_connectedComponentIn

/-- In the curved branch, every actual strict-slab frontier component is
exactly one connected component of the corresponding supporting-circle clip. -/
theorem connectedComponentIn_eq_circleClip_component
    {carrier H : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier (frontier carrier ∩ H) K)
    (p : (frontier carrier ∩ H : Set PlanePoint)) (hK : K ≠ 0) :
    connectedComponentIn (frontier carrier ∩ H) p.1 =
      connectedComponentIn
        ({q : PlanePoint |
          circleValue (A.supportingCenterAt p) |1 / K| q = 0} ∩ H) p.1 := by
  rw [connectedComponentIn_eq_connectedComponentIn_supportAt_inter A p,
    A.supportAt_eq_circleValue_zero p hK]

/-- A transverse point of a supporting-circle component in a pole-bounded
strict slab is one of the two endpoints of its horizontal carrier section. -/
theorem strictSlab_frontier_point_eq_section_endpoint
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hlowerPole : (A.supportingCenterAt p).2 - |1 / K| ≤ lowerY)
    (hupperPole : upperY ≤ (A.supportingCenterAt p).2 + |1 / K|) :
    p.1.1 = sInf (horizontalSection carrier p.1.2) ∨
      p.1.1 = sSup (horizontalSection carrier p.1.2) := by
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have hlowerNe :
      p.1.2 ≠ (A.supportingCenterAt p).2 - |1 / K| := by
    intro heq
    have := p.2.2.1
    linarith
  have hupperNe :
      p.1.2 ≠ (A.supportingCenterAt p).2 + |1 / K| := by
    intro heq
    have := p.2.2.2
    linarith
  have hpTransverse : p.1.1 ≠ (A.supportingCenterAt p).1 :=
    circle_horizontal_transverse_of_height_ne_extrema hpCircle hlowerNe hupperNe
  have hpSectionFrontier :
      p.1.1 ∈ frontier (horizontalSection carrier p.1.2) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided hpCircle
      hpTransverse (mixedAtlas_locallyOneSided_supportingCircle A p hK)
  let S : Set ℝ := horizontalSection carrier p.1.2
  have hSNonempty : S.Nonempty := by
    by_contra hnone
    have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hnone
    rw [show horizontalSection carrier p.1.2 = S from rfl,
      hSempty, frontier_empty] at hpSectionFrontier
    exact hpSectionFrontier
  have hSopen : IsOpen S := isOpen_horizontalSection hcarrierOpen p.1.2
  have hSbounded : Bornology.IsBounded S :=
    isBounded_horizontalSection hcarrierBounded p.1.2
  have hsection : S = Ioo (sInf S) (sSup S) :=
    CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hSNonempty hSbounded (hsections p.1.2)
  have horder : sInf S < sSup S := by
    obtain ⟨x, hx⟩ := hSNonempty
    have hx' : x ∈ Ioo (sInf S) (sSup S) := hsection ▸ hx
    exact hx'.1.trans hx'.2
  exact transverse_circle_point_eq_interval_endpoint horder
    (show horizontalSection carrier p.1.2 = Ioo (sInf S) (sSup S) from hsection)
    hpCircle hpTransverse
    (mixedAtlas_locallyOneSided_supportingCircle A p hK)

/-- Open left branch of a circle between two horizontal interfaces. -/
def leftCircleStrictSlabArc (center : PlanePoint)
    (radius lowerY upperY : ℝ) : Set PlanePoint :=
  {q | circleValue center radius q = 0 ∧
    lowerY < q.2 ∧ q.2 < upperY ∧ q.1 < center.1}

/-- Open right branch of a circle between two horizontal interfaces. -/
def rightCircleStrictSlabArc (center : PlanePoint)
    (radius lowerY upperY : ℝ) : Set PlanePoint :=
  {q | circleValue center radius q = 0 ∧
    lowerY < q.2 ∧ q.2 < upperY ∧ center.1 < q.1}

/-- The left geometric branch is parametrized by height throughout a
pole-bounded strict slab. -/
theorem leftCircleStrictSlabArc_eq_image
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius) :
    leftCircleStrictSlabArc center radius lowerY upperY =
      leftCirclePointAtHeight center radius '' Ioo lowerY upperY := by
  ext q
  constructor
  · intro hq
    have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
      hradius (hlowerPole.trans_lt hq.2.1)
        (hq.2.2.1.trans_le hupperPole)
    have hmem :
        q ∈ ({leftCirclePointAtHeight center radius q.2,
          rightCirclePointAtHeight center radius q.2} : Set PlanePoint) := by
      rw [← hpair.1]
      exact ⟨hq.1, rfl⟩
    rcases hmem with hleft | hright
    · exact ⟨q.2, ⟨hq.2.1, hq.2.2.1⟩, hleft.symm⟩
    · rw [hright] at hq
      unfold rightCirclePointAtHeight at hq
      have hsqrt : 0 <
          √(radius ^ 2 - (q.2 - center.2) ^ 2) := by
        unfold leftCirclePointAtHeight rightCirclePointAtHeight at hpair
        dsimp only at hpair
        linarith [hpair.2]
      linarith [hq.2.2.2]
  · rintro ⟨y, hy, rfl⟩
    have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
      hradius (hlowerPole.trans_lt hy.1) (hy.2.trans_le hupperPole)
    have hmem :
        leftCirclePointAtHeight center radius y ∈
          {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} := by
      rw [hpair.1]
      exact Set.mem_insert _ _
    refine ⟨hmem.1, hy.1, hy.2, ?_⟩
    unfold leftCirclePointAtHeight at hpair ⊢
    unfold rightCirclePointAtHeight at hpair
    dsimp only at hpair ⊢
    linarith [hpair.2]

/-- The right geometric branch is parametrized by height throughout a
pole-bounded strict slab. -/
theorem rightCircleStrictSlabArc_eq_image
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius) :
    rightCircleStrictSlabArc center radius lowerY upperY =
      rightCirclePointAtHeight center radius '' Ioo lowerY upperY := by
  ext q
  constructor
  · intro hq
    have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
      hradius (hlowerPole.trans_lt hq.2.1)
        (hq.2.2.1.trans_le hupperPole)
    have hmem :
        q ∈ ({leftCirclePointAtHeight center radius q.2,
          rightCirclePointAtHeight center radius q.2} : Set PlanePoint) := by
      rw [← hpair.1]
      exact ⟨hq.1, rfl⟩
    rcases hmem with hleft | hright
    · rw [hleft] at hq
      unfold leftCirclePointAtHeight at hq
      have hsqrt : 0 <
          √(radius ^ 2 - (q.2 - center.2) ^ 2) := by
        unfold leftCirclePointAtHeight rightCirclePointAtHeight at hpair
        dsimp only at hpair
        linarith [hpair.2]
      linarith [hq.2.2.2]
    · exact ⟨q.2, ⟨hq.2.1, hq.2.2.1⟩, hright.symm⟩
  · rintro ⟨y, hy, rfl⟩
    have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
      hradius (hlowerPole.trans_lt hy.1) (hy.2.trans_le hupperPole)
    have hmem :
        rightCirclePointAtHeight center radius y ∈
          {q : PlanePoint | circleValue center radius q = 0 ∧ q.2 = y} := by
      rw [hpair.1]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    refine ⟨hmem.1, hy.1, hy.2, ?_⟩
    unfold leftCirclePointAtHeight at hpair
    unfold rightCirclePointAtHeight at hpair ⊢
    dsimp only at hpair ⊢
    linarith [hpair.2]

theorem leftCircleStrictSlabArc_isPreconnected
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius) :
    IsPreconnected (leftCircleStrictSlabArc center radius lowerY upperY) := by
  rw [leftCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
  exact isPreconnected_Ioo.image _
    (show Continuous (leftCirclePointAtHeight center radius) by
      unfold leftCirclePointAtHeight
      fun_prop).continuousOn

theorem rightCircleStrictSlabArc_isPreconnected
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius) :
    IsPreconnected (rightCircleStrictSlabArc center radius lowerY upperY) := by
  rw [rightCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
  exact isPreconnected_Ioo.image _
    (show Continuous (rightCirclePointAtHeight center radius) by
      unfold rightCirclePointAtHeight
      fun_prop).continuousOn

/-- A maximal strict-slab continuation component reaches both interfaces when
its ambient closure meets both interface lines.  No contact point, supporting
circle, or endpoint order is stored. -/
def StrictSlabComponentReachesBothInterfaces
    (locus : Set PlanePoint) (p : PlanePoint) (lowerY upperY : ℝ) : Prop :=
  (closure (connectedComponentIn locus p) ∩
      {q : PlanePoint | q.2 = lowerY}).Nonempty ∧
    (closure (connectedComponentIn locus p) ∩
      {q : PlanePoint | q.2 = upperY}).Nonempty

/-- Curved support propagation keeps the closure of an actual strict-slab
component on both its supporting circle and the ambient frontier. -/
theorem closure_strictSlab_component_subset_supportAt_and_frontier
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) :
    closure (connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1) ⊆
      A.supportAt p ∩ frontier carrier := by
  intro q hq
  constructor
  · apply closure_minimal (A.connectedComponentIn_subset_supportAt p)
      (show IsClosed (A.supportAt p) by
        rw [A.supportAt_eq_circleValue_zero p hK]
        exact isClosed_eq (by unfold circleValue; fun_prop) continuous_const)
    exact hq
  · apply closure_minimal
      ((connectedComponentIn_subset
        (frontier carrier ∩ {z : PlanePoint |
          lowerY < z.2 ∧ z.2 < upperY}) p.1).trans inter_subset_left)
      isClosed_frontier
    exact hq

/-- Interface reach produces actual frontier contacts on the same propagated
support and forces the circle radius to span at least half the slab height. -/
theorem strictSlab_component_reach_derives_actual_support_contacts
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hreach : StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY) :
    ∃ lowerContact upperContact : PlanePoint,
      lowerContact ∈ frontier carrier ∩ A.supportAt p ∧
      upperContact ∈ frontier carrier ∩ A.supportAt p ∧
      lowerContact.2 = lowerY ∧ upperContact.2 = upperY ∧
      (upperY - lowerY) / 2 ≤ |1 / K| := by
  rcases hreach.1 with ⟨lowerContact, hlowerClosure, hlowerHeight⟩
  rcases hreach.2 with ⟨upperContact, hupperClosure, hupperHeight⟩
  have hclosure :=
    closure_strictSlab_component_subset_supportAt_and_frontier A p hK
  have hlower := hclosure hlowerClosure
  have hupper := hclosure hupperClosure
  have hlowerPole :
      (A.supportingCenterAt p).2 - |1 / K| ≤ lowerY :=
    supportingCenterAt_sub_radius_le_interface_of_contact
      A p hK hlower.1 hlowerHeight
  have hupperPole :
      upperY ≤ (A.supportingCenterAt p).2 + |1 / K| :=
    interface_le_supportingCenterAt_add_radius_of_contact
      A p hK hupper.1 hupperHeight
  refine ⟨lowerContact, upperContact, ⟨hlower.2, hlower.1⟩,
    ⟨hupper.2, hupper.1⟩, hlowerHeight, hupperHeight, ?_⟩
  linarith

/-- For a curved component that reaches both slab interfaces, every point is
the left or right endpoint of its horizontal carrier section. -/
theorem strictSlab_frontier_point_eq_section_endpoint_of_component_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hreach : StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY) :
    p.1.1 = sInf (horizontalSection carrier p.1.2) ∨
      p.1.1 = sSup (horizontalSection carrier p.1.2) := by
  obtain ⟨lowerContact, upperContact, hlower, hupper,
      hlowerHeight, hupperHeight, _hradius⟩ :=
    strictSlab_component_reach_derives_actual_support_contacts A p hK hreach
  apply strictSlab_frontier_point_eq_section_endpoint
    A hcarrierOpen hcarrierBounded hsections p hK
  · exact supportingCenterAt_sub_radius_le_interface_of_contact
      A p hK hlower.2 hlowerHeight
  · exact interface_le_supportingCenterAt_add_radius_of_contact
      A p hK hupper.2 hupperHeight

/-- The geometric clip of one circle by an open horizontal slab. -/
def circleStrictSlabClip (center : PlanePoint)
    (radius lowerY upperY : ℝ) : Set PlanePoint :=
  {q | circleValue center radius q = 0} ∩
    {q | lowerY < q.2 ∧ q.2 < upperY}

/-- A pole-bounded circle clip's component through a left-branch point is the
complete left branch. -/
theorem connectedComponentIn_circleStrictSlabClip_eq_left
    {center p : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius)
    (hp : p ∈ leftCircleStrictSlabArc center radius lowerY upperY) :
    connectedComponentIn (circleStrictSlabClip center radius lowerY upperY) p =
      leftCircleStrictSlabArc center radius lowerY upperY := by
  apply Subset.antisymm
  · intro q hqComponent
    have hqClip := connectedComponentIn_subset
      (circleStrictSlabClip center radius lowerY upperY) p hqComponent
    have hqTransverse : q.1 ≠ center.1 := by
      apply circle_horizontal_transverse_of_height_ne_extrema hqClip.1
      · intro heq
        linarith [hqClip.2.1]
      · intro heq
        linarith [hqClip.2.2]
    have hqLeft : q.1 < center.1 := by
      by_contra hnotLeft
      have hqRight : center.1 < q.1 :=
        lt_of_le_of_ne (le_of_not_gt hnotLeft) hqTransverse.symm
      have hbetween : center.1 ∈ Icc p.1 q.1 :=
        ⟨hp.2.2.2.le, hqRight.le⟩
      have himage := isPreconnected_connectedComponentIn.intermediate_value
        (mem_connectedComponentIn
          (show p ∈ circleStrictSlabClip center radius lowerY upperY from
            ⟨hp.1, hp.2.1, hp.2.2.1⟩))
        hqComponent continuous_fst.continuousOn hbetween
      rcases himage with ⟨z, hzComponent, hzCenter⟩
      have hzClip := connectedComponentIn_subset
        (circleStrictSlabClip center radius lowerY upperY) p hzComponent
      have hzTransverse : z.1 ≠ center.1 := by
        apply circle_horizontal_transverse_of_height_ne_extrema hzClip.1
        · intro heq
          linarith [hzClip.2.1]
        · intro heq
          linarith [hzClip.2.2]
      exact hzTransverse hzCenter
    exact ⟨hqClip.1, hqClip.2.1, hqClip.2.2, hqLeft⟩
  · exact
      (leftCircleStrictSlabArc_isPreconnected
        hradius hlowerPole hupperPole).subset_connectedComponentIn
          hp (by
            intro q hq
            exact ⟨hq.1, hq.2.1, hq.2.2.1⟩)

/-- A pole-bounded circle clip's component through a right-branch point is the
complete right branch. -/
theorem connectedComponentIn_circleStrictSlabClip_eq_right
    {center p : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius)
    (hp : p ∈ rightCircleStrictSlabArc center radius lowerY upperY) :
    connectedComponentIn (circleStrictSlabClip center radius lowerY upperY) p =
      rightCircleStrictSlabArc center radius lowerY upperY := by
  apply Subset.antisymm
  · intro q hqComponent
    have hqClip := connectedComponentIn_subset
      (circleStrictSlabClip center radius lowerY upperY) p hqComponent
    have hqTransverse : q.1 ≠ center.1 := by
      apply circle_horizontal_transverse_of_height_ne_extrema hqClip.1
      · intro heq
        linarith [hqClip.2.1]
      · intro heq
        linarith [hqClip.2.2]
    have hqRight : center.1 < q.1 := by
      by_contra hnotRight
      have hqLeft : q.1 < center.1 :=
        lt_of_le_of_ne (le_of_not_gt hnotRight) hqTransverse
      have hbetween : center.1 ∈ Icc q.1 p.1 :=
        ⟨hqLeft.le, hp.2.2.2.le⟩
      have himage := isPreconnected_connectedComponentIn.intermediate_value
        hqComponent
        (mem_connectedComponentIn
          (show p ∈ circleStrictSlabClip center radius lowerY upperY from
            ⟨hp.1, hp.2.1, hp.2.2.1⟩))
        continuous_fst.continuousOn hbetween
      rcases himage with ⟨z, hzComponent, hzCenter⟩
      have hzClip := connectedComponentIn_subset
        (circleStrictSlabClip center radius lowerY upperY) p hzComponent
      have hzTransverse : z.1 ≠ center.1 := by
        apply circle_horizontal_transverse_of_height_ne_extrema hzClip.1
        · intro heq
          linarith [hzClip.2.1]
        · intro heq
          linarith [hzClip.2.2]
      exact hzTransverse hzCenter
    exact ⟨hqClip.1, hqClip.2.1, hqClip.2.2, hqRight⟩
  · exact
      (rightCircleStrictSlabArc_isPreconnected
        hradius hlowerPole hupperPole).subset_connectedComponentIn
          hp (by
            intro q hq
            exact ⟨hq.1, hq.2.1, hq.2.2.1⟩)

/-- Under pole bounds, an actual curved strict-slab component is one complete
geometric circle branch, selected by the base point's horizontal side. -/
theorem strictSlab_component_eq_left_or_right_arc
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hlowerPole : (A.supportingCenterAt p).2 - |1 / K| ≤ lowerY)
    (hupperPole : upperY ≤ (A.supportingCenterAt p).2 + |1 / K|) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        leftCircleStrictSlabArc
          (A.supportingCenterAt p) |1 / K| lowerY upperY ∨
      connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        rightCircleStrictSlabArc
          (A.supportingCenterAt p) |1 / K| lowerY upperY := by
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle :
      circleValue (A.supportingCenterAt p) |1 / K| p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  have hpTransverse : p.1.1 ≠ (A.supportingCenterAt p).1 := by
    apply circle_horizontal_transverse_of_height_ne_extrema hpCircle
    · intro heq
      linarith [p.2.2.1]
    · intro heq
      linarith [p.2.2.2]
  rcases lt_or_gt_of_ne hpTransverse with hpLeft | hpRight
  · left
    rw [connectedComponentIn_eq_circleClip_component A p hK]
    exact connectedComponentIn_circleStrictSlabClip_eq_left
      hradius hlowerPole hupperPole
        ⟨hpCircle, p.2.2.1, p.2.2.2, hpLeft⟩
  · right
    rw [connectedComponentIn_eq_circleClip_component A p hK]
    exact connectedComponentIn_circleStrictSlabClip_eq_right
      hradius hlowerPole hupperPole
        ⟨hpCircle, p.2.2.1, p.2.2.2, hpRight⟩

/-- Both-interface reach supplies the pole bounds, so every such actual curved
component is a complete left or right circle arc across the strict slab. -/
theorem strictSlab_component_eq_complete_circle_arc_of_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hreach : StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY) :
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        leftCircleStrictSlabArc
          (A.supportingCenterAt p) |1 / K| lowerY upperY ∨
      connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        rightCircleStrictSlabArc
          (A.supportingCenterAt p) |1 / K| lowerY upperY := by
  obtain ⟨lowerContact, upperContact, hlower, hupper,
      hlowerHeight, hupperHeight, _hradius⟩ :=
    strictSlab_component_reach_derives_actual_support_contacts A p hK hreach
  apply strictSlab_component_eq_left_or_right_arc A p hK
  · exact supportingCenterAt_sub_radius_le_interface_of_contact
      A p hK hlower.2 hlowerHeight
  · exact interface_le_supportingCenterAt_add_radius_of_contact
      A p hK hupper.2 hupperHeight

/-- Actual upper-pole data retain the truthful occupied-side germ of the same
carrier.  The sign, tangent, and center order are not folded into an abstract
positive-radius choice. -/
structure UpperPoleGeometry
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) where
  pole : locus
  occupied_below : A.side = .below
  actual_occupied_germ :
    ∀ᶠ q in 𝓝 pole.1,
      (q ∈ carrier ↔
        q ∈ (A.chart pole).patch.occupiedGraphDomain
          (A.chart pole).patch.graph)
  tangent : deriv (A.chart pole).patch.graph pole.1.1 = 0
  center_below_pole :
    ((A.chart pole).patch.supportingCenter K pole.1.1).2 <
      ((A.chart pole).patch.graphTrace pole.1.1).2

namespace UpperPoleGeometry

variable {carrier locus : Set PlanePoint} {K : ℝ}
    {A : BranchNeutralGraphAtlas carrier locus K}

/-- The upper-pole geometry forces negative common occupied curvature. -/
theorem curvature_neg (P : UpperPoleGeometry A) (hK : K ≠ 0) : K < 0 :=
  commonCurvature_neg_of_below_tangent_center_below (A.chart P.pole) hK
    ((A.chart_side P.pole).trans P.occupied_below) P.tangent
      P.center_below_pole

end UpperPoleGeometry

/-- Truthful occupied-side data at a lower pole. -/
structure LowerPoleGeometry
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) where
  pole : locus
  occupied_above : A.side = .above
  actual_occupied_germ :
    ∀ᶠ q in 𝓝 pole.1,
      (q ∈ carrier ↔
        q ∈ (A.chart pole).patch.occupiedGraphDomain
          (A.chart pole).patch.graph)
  tangent : deriv (A.chart pole).patch.graph pole.1.1 = 0
  pole_below_center :
    ((A.chart pole).patch.graphTrace pole.1.1).2 <
      ((A.chart pole).patch.supportingCenter K pole.1.1).2

namespace LowerPoleGeometry

variable {carrier locus : Set PlanePoint} {K : ℝ}
    {A : BranchNeutralGraphAtlas carrier locus K}

/-- The lower-pole geometry forces the same negative common curvature. -/
theorem curvature_neg (P : LowerPoleGeometry A) (hK : K ≠ 0) : K < 0 :=
  commonCurvature_neg_of_above_tangent_center_above (A.chart P.pole) hK
    ((A.chart_side P.pole).trans P.occupied_above) P.tangent
      P.pole_below_center

end LowerPoleGeometry

/-- Every complete affine support line is unbounded. -/
theorem not_isBounded_supportingLineAt
    {carrier : Set PlanePoint} (A : ActualRegularGraphChart carrier)
    (x : ℝ) :
    ¬ Bornology.IsBounded (A.patch.supportingLineAt x) := by
  intro hbounded
  have hfst : Bornology.IsBounded
      (Prod.fst '' A.patch.supportingLineAt x) := hbounded.image_fst
  have hfstEq : Prod.fst '' A.patch.supportingLineAt x = Set.univ := by
    ext z
    constructor
    · intro _hz
      exact Set.mem_univ z
    · intro _hz
      refine ⟨(z, A.patch.graph x +
        deriv A.patch.graph x * (z - x)), ?_, rfl⟩
      rfl
  rw [hfstEq] at hfst
  exact NormedSpace.unbounded_univ ℝ ℝ hfst

/-- Consequently a bounded representative cannot have an entire affine
support line in its frontier. -/
theorem not_supportingLineAt_subset_frontier_of_isBounded
    {carrier : Set PlanePoint} (A : ActualRegularGraphChart carrier)
    (hbounded : Bornology.IsBounded carrier) (x : ℝ) :
    ¬ A.patch.supportingLineAt x ⊆ frontier carrier := by
  intro hsubset
  have hfrontier : Bornology.IsBounded (frontier carrier) :=
    hbounded.closure.subset frontier_subset_closure
  exact not_isBounded_supportingLineAt A x (hfrontier.subset hsubset)
/-- Connectedness and global reach make every intermediate horizontal carrier
section nonempty, including the two slab interface heights. -/
theorem horizontalSection_nonempty_of_connected_twoSided_reach
    {carrier : Set PlanePoint} {lowerY upperY y : ℝ}
    (hcarrierConnected : IsConnected carrier)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (hy : lowerY ≤ y ∧ y ≤ upperY) :
    (horizontalSection carrier y).Nonempty := by
  obtain ⟨qLow, hqLow, hqLowY⟩ := hlow
  obtain ⟨qHigh, hqHigh, hqHighY⟩ := hhigh
  have hyImage : y ∈ Prod.snd '' carrier := by
    apply hcarrierConnected.isPreconnected.intermediate_value hqLow hqHigh
      continuous_snd.continuousOn
    exact ⟨hqLowY.trans hy.1, hy.2.trans hqHighY⟩
  rcases hyImage with ⟨q, hqCarrier, hqy⟩
  refine ⟨q.1, ?_⟩
  rw [← hqy]
  exact hqCarrier

/-- An affine vertical-graph support clipped by a strict slab is preconnected. -/
theorem verticalAffineLine_inter_strictSlab_isPreconnected
    (b m s lowerY upperY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.2 = b + m * (q.1 - s)} ∩
        {q : PlanePoint | lowerY < q.2 ∧ q.2 < upperY}) := by
  have heq :
      {q : PlanePoint | q.2 = b + m * (q.1 - s)} =
        {q : PlanePoint | q.2 - m * q.1 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  rw [show ({q : PlanePoint | q.2 - m*q.1 = b-m*s} ∩
      {q | lowerY < q.2 ∧ q.2 < upperY}) =
      (({q | q.2 - m*q.1 = b-m*s} ∩ {q | lowerY < q.2}) ∩
        {q | q.2 < upperY}) by ext q; simp [and_assoc]]
  have hc := (convex_hyperplane
    (plane_snd_sub_mul_fst_isLinearMap m) (b - m*s)).inter
      (convex_halfSpace_gt plane_snd_isLinearMap lowerY)
  exact (hc.inter
    (convex_halfSpace_lt plane_snd_isLinearMap upperY)).isPreconnected

/-- An affine horizontal-graph support clipped by a strict slab is preconnected. -/
theorem horizontalAffineLine_inter_strictSlab_isPreconnected
    (b m s lowerY upperY : ℝ) :
    IsPreconnected
      ({q : PlanePoint | q.1 = b + m * (q.2 - s)} ∩
        {q : PlanePoint | lowerY < q.2 ∧ q.2 < upperY}) := by
  have heq :
      {q : PlanePoint | q.1 = b + m * (q.2 - s)} =
        {q : PlanePoint | q.1 - m * q.2 = b - m * s} := by
    ext q
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  rw [show ({q : PlanePoint | q.1 - m*q.2 = b-m*s} ∩
      {q | lowerY < q.2 ∧ q.2 < upperY}) =
      (({q | q.1 - m*q.2 = b-m*s} ∩ {q | lowerY < q.2}) ∩
        {q | q.2 < upperY}) by ext q; simp [and_assoc]]
  have hc := (convex_hyperplane
    (plane_fst_sub_mul_snd_isLinearMap m) (b - m*s)).inter
      (convex_halfSpace_gt plane_snd_isLinearMap lowerY)
  exact (hc.inter
    (convex_halfSpace_lt plane_snd_isLinearMap upperY)).isPreconnected

/-- Continuous height graphs contain both endpoint values in the closure of
their open-interval images. -/
theorem continuous_image_Ioo_endpoints_mem_closure
    {f : ℝ → PlanePoint} {lowerY upperY : ℝ}
    (hf : Continuous f) (hlowerUpper : lowerY < upperY) :
    f lowerY ∈ closure (f '' Ioo lowerY upperY) ∧
      f upperY ∈ closure (f '' Ioo lowerY upperY) := by
  have hlower : lowerY ∈ closure (Ioo lowerY upperY) := by
    rw [closure_Ioo hlowerUpper.ne]
    exact ⟨le_rfl, hlowerUpper.le⟩
  have hupper : upperY ∈ closure (Ioo lowerY upperY) := by
    rw [closure_Ioo hlowerUpper.ne]
    exact ⟨hlowerUpper.le, le_rfl⟩
  exact ⟨image_closure_subset_closure_image hf ⟨lowerY, hlower, rfl⟩,
    image_closure_subset_closure_image hf ⟨upperY, hupper, rfl⟩⟩



/-- A lower circle pole on an actual slab component would pinch nonempty
ordered horizontal sections to zero width. -/
private theorem lowerCirclePole_pinch_contradiction
    {carrier : Set PlanePoint} {center : PlanePoint} {radius upperY : ℝ}
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hradius : 0 < radius)
    (hpoleTop : center.2 - radius < upperY)
    (hhalfFrontier :
      {q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < upperY} ⊆ frontier carrier)
    (hhalfGerm : ∀ q : PlanePoint,
      circleValue center radius q = 0 → q.2 < upperY →
        LocallyOneSided carrier center radius q)
    (hpoleSection :
      (horizontalSection carrier (center.2 - radius)).Nonempty) : False := by
  let pole : PlanePoint := (center.1, center.2 - radius)
  have hpoleCircle : circleValue center radius pole = 0 := by
    dsimp only [pole]
    unfold circleValue
    ring
  have hpoleFrontier : pole ∈ frontier carrier :=
    hhalfFrontier ⟨hpoleCircle, hpoleTop⟩
  obtain ⟨x, hxCarrier⟩ := hpoleSection
  have hxNe : x ≠ center.1 := by
    intro hx
    have hpoleCarrier : pole ∈ carrier := by
      dsimp only [pole]
      rw [← hx]
      exact hxCarrier
    have : pole ∈ carrier ∩ frontier carrier := ⟨hpoleCarrier, hpoleFrontier⟩
    rw [hcarrierOpen.inter_frontier_eq] at this
    exact this
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hcarrierOpen (x, center.2 - radius) hxCarrier
  let d2 : ℝ := (x - center.1) ^ 2
  have hd2 : 0 < d2 := by
    dsimp only [d2]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hxNe)
  let delta : ℝ :=
    min epsilon (min (upperY - (center.2 - radius))
      (min radius (d2 / (4 * radius)))) / 2
  have hgap : 0 < upperY - (center.2 - radius) := sub_pos.mpr hpoleTop
  have hfrac : 0 < d2 / (4 * radius) := div_pos hd2 (by positivity)
  have hminPos : 0 < min epsilon
      (min (upperY - (center.2 - radius))
        (min radius (d2 / (4 * radius)))) := by
    exact lt_min hepsilon (lt_min hgap (lt_min hradius hfrac))
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hdeltaEpsilon : delta < epsilon := by
    dsimp only [delta]
    have hle := min_le_left epsilon
      (min (upperY - (center.2 - radius))
        (min radius (d2 / (4 * radius))))
    linarith
  have hdeltaGap : delta < upperY - (center.2 - radius) := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min (upperY - (center.2 - radius))
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_left (upperY - (center.2 - radius))
      (min radius (d2 / (4 * radius)))
    linarith
  have hdeltaRadius : delta < radius := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min (upperY - (center.2 - radius))
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_right (upperY - (center.2 - radius))
      (min radius (d2 / (4 * radius)))
    have hle3 := min_le_left radius (d2 / (4 * radius))
    linarith
  have hdeltaFrac : delta < d2 / (4 * radius) := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min (upperY - (center.2 - radius))
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_right (upperY - (center.2 - radius))
      (min radius (d2 / (4 * radius)))
    have hle3 := min_le_right radius (d2 / (4 * radius))
    linarith
  let y := center.2 - radius + delta
  have hyLowerPole : center.2 - radius < y := by dsimp only [y]; linarith
  have hyUpperPole : y < center.2 + radius := by dsimp only [y]; linarith
  have hyUpper : y < upperY := by dsimp only [y]; linarith
  have hxyCarrier : (x, y) ∈ carrier := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq]
    dsimp only [y]
    simp only [Real.dist_eq, sub_self, abs_zero]
    rw [show center.2 - radius + delta - (center.2 - radius) = delta by ring,
      abs_of_pos hdelta, max_eq_right hdelta.le]
    exact hdeltaEpsilon
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius hyLowerPole hyUpperPole
  let left := leftCirclePointAtHeight center radius y
  let right := rightCirclePointAtHeight center radius y
  have hleftCircle : circleValue center radius left = 0 := by
    have hm : left ∈ ({left, right} : Set PlanePoint) := Set.mem_insert _ _
    rw [← hpair.1] at hm
    exact hm.1
  have hrightCircle : circleValue center radius right = 0 := by
    have hm : right ∈ ({left, right} : Set PlanePoint) :=
      Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← hpair.1] at hm
    exact hm.1
  have hleftTransverse : left.1 ≠ center.1 := by
    dsimp only [left, leftCirclePointAtHeight]
    have := hpair.2
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at this
    linarith
  have hrightTransverse : right.1 ≠ center.1 := by
    dsimp only [right, rightCirclePointAtHeight]
    have := hpair.2
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at this
    linarith
  have hleftSectionFrontier :
      left.1 ∈ frontier (horizontalSection carrier y) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hleftCircle hleftTransverse (hhalfGerm left hleftCircle (by
        dsimp only [left, leftCirclePointAtHeight]; exact hyUpper))
  have hrightSectionFrontier :
      right.1 ∈ frontier (horizontalSection carrier y) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hrightCircle hrightTransverse (hhalfGerm right hrightCircle (by
        dsimp only [right, rightCirclePointAtHeight]; exact hyUpper))
  let S : Set ℝ := horizontalSection carrier y
  have hSNonempty : S.Nonempty := ⟨x, hxyCarrier⟩
  have hSopen : IsOpen S := isOpen_horizontalSection hcarrierOpen y
  have hSbounded : Bornology.IsBounded S :=
    isBounded_horizontalSection hcarrierBounded y
  have hsection : S = Ioo (sInf S) (sSup S) :=
    CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hSNonempty hSbounded (hsections y)
  have horder : sInf S ≤ sSup S := by
    obtain ⟨z, hz⟩ := hSNonempty
    have hz' : z ∈ Ioo (sInf S) (sSup S) := hsection ▸ hz
    exact hz'.1.le.trans hz'.2.le
  have hends := openInterval_endpoints_of_ordered_frontier horder hsection
    hleftSectionFrontier hrightSectionFrontier hpair.2
  have hxInterval : x ∈ Ioo left.1 right.1 := by
    have hxS : x ∈ S := hxyCarrier
    rw [hsection, hends.1, hends.2] at hxS
    exact hxS
  have hsqrtSq :
      (√(radius ^ 2 - (y - center.2) ^ 2)) ^ 2 =
        radius ^ 2 - (y - center.2) ^ 2 := by
    apply Real.sq_sqrt
    have hleft : 0 < radius - (y - center.2) := by linarith
    have hright : 0 < radius + (y - center.2) := by linarith
    nlinarith [mul_pos hleft hright]
  have hd2Lt : d2 < radius ^ 2 - (y - center.2) ^ 2 := by
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at hxInterval
    dsimp only [d2]
    have hprod := mul_pos (sub_pos.mpr hxInterval.1)
      (sub_pos.mpr hxInterval.2)
    nlinarith [hprod]
  have hradicandLt : radius ^ 2 - (y - center.2) ^ 2 < d2 := by
    dsimp only [y]
    have hmul0 := (lt_div_iff₀ (by positivity : 0 < 4 * radius)).mp
      hdeltaFrac
    have hmul : 4 * radius * delta < d2 := by nlinarith [hmul0]
    dsimp only [d2] at hmul ⊢
    nlinarith [sq_nonneg delta]
  linarith


/-- In the flat branch a nonhorizontal affine support reaches both interfaces;
a horizontal support would put a complete unbounded line in the bounded
carrier's frontier. -/
theorem strictSlab_component_reaches_both_interfaces_of_eq_zero
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hlowerUpper : lowerY < upperY)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K = 0) :
    StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY := by
  let slab : Set PlanePoint := {q : PlanePoint |
    lowerY < q.2 ∧ q.2 < upperY}
  have hpre : IsPreconnected (A.supportAt p ∩ slab) := by
    unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
      RegularChart.supportAtParameter
    rw [if_pos hK]
    cases hchart : A.chart p with
    | vertical C hcurv hoccupied =>
        exact verticalAffineLine_inter_strictSlab_isPreconnected
          (C.patch.graph p.1.1) (deriv C.patch.graph p.1.1) p.1.1
          lowerY upperY
    | horizontal C hcurv hoccupied =>
        exact horizontalAffineLine_inter_strictSlab_isPreconnected
          (C.patch.graph p.1.2) (deriv C.patch.graph p.1.2) p.1.2
          lowerY upperY
  have hcomponent :
      connectedComponentIn (frontier carrier ∩ slab) p.1 =
        A.supportAt p ∩ slab := by
    exact connectedComponentIn_eq_supportAt_inter_of_isPreconnected A p hpre
  change
    (closure (connectedComponentIn (frontier carrier ∩ slab) p.1) ∩
        {q : PlanePoint | q.2 = lowerY}).Nonempty ∧
      (closure (connectedComponentIn (frontier carrier ∩ slab) p.1) ∩
        {q : PlanePoint | q.2 = upperY}).Nonempty
  cases hchart : A.chart p with
  | vertical C hcurv hoccupied =>
      let b := C.patch.graph p.1.1
      let m := deriv C.patch.graph p.1.1
      have hsupport : A.supportAt p = C.patch.supportingLineAt p.1.1 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK, hchart]
        rfl
      have hpBase := A.base_eq p
      rw [hchart] at hpBase
      simp only [RegularChart.parameter, RegularChart.trace] at hpBase
      have hbSlab : lowerY < b ∧ b < upperY := by
        dsimp only [b]
        have hb := congrArg Prod.snd hpBase
        simp only [GraphPatch.graphTrace] at hb
        rw [hb]
        exact p.2.2
      by_cases hm : m = 0
      · exfalso
        apply not_supportingLineAt_subset_frontier_of_isBounded C
          hcarrierBounded p.1.1
        intro q hqLine
        have hqHeight : q.2 = b := by
          dsimp only [b, m] at hm ⊢
          change q.2 = C.patch.graph p.1.1 +
            deriv C.patch.graph p.1.1 * (q.1 - p.1.1) at hqLine
          rw [hm, zero_mul] at hqLine
          simpa only [add_zero] using hqLine
        have hqSlab : q ∈ slab := by
          change lowerY < q.2 ∧ q.2 < upperY
          rw [hqHeight]
          exact hbSlab
        have hqComponent : q ∈
            connectedComponentIn (frontier carrier ∩ slab) p.1 := by
          rw [hcomponent]
          exact ⟨hsupport.symm ▸ hqLine, hqSlab⟩
        exact (connectedComponentIn_subset (frontier carrier ∩ slab) p.1
          hqComponent).1
      · let f : ℝ → PlanePoint := fun y =>
          (p.1.1 + (y - b) / m, y)
        have hf : Continuous f := by
          dsimp only [f]
          fun_prop
        have himage : f '' Ioo lowerY upperY ⊆
            connectedComponentIn (frontier carrier ∩ slab) p.1 := by
          rintro q ⟨y, hy, rfl⟩
          rw [hcomponent]
          constructor
          · rw [hsupport]
            change y = b + m * (p.1.1 + (y - b) / m - p.1.1)
            field_simp [hm]
            ring
          · exact hy
        have hend := continuous_image_Ioo_endpoints_mem_closure hf hlowerUpper
        refine ⟨⟨f lowerY, closure_mono himage hend.1, rfl⟩,
          ⟨f upperY, closure_mono himage hend.2, rfl⟩⟩
  | horizontal C hcurv hoccupied =>
      let b := C.patch.graph p.1.2
      let m := deriv C.patch.graph p.1.2
      have hsupport : A.supportAt p = C.patch.supportingLineAt p.1.2 := by
        unfold BranchNeutralMixedGraphAtlas.supportAt RegularChart.supportAt
          RegularChart.supportAtParameter
        rw [if_pos hK, hchart]
        rfl
      let f : ℝ → PlanePoint := fun y =>
        (b + m * (y - p.1.2), y)
      have hf : Continuous f := by
        dsimp only [f]
        fun_prop
      have himage : f '' Ioo lowerY upperY ⊆
          connectedComponentIn (frontier carrier ∩ slab) p.1 := by
        rintro q ⟨y, hy, rfl⟩
        rw [hcomponent]
        constructor
        · rw [hsupport]
          rfl
        · exact hy
      have hend := continuous_image_Ioo_endpoints_mem_closure hf hlowerUpper
      refine ⟨⟨f lowerY, closure_mono himage hend.1, rfl⟩,
        ⟨f upperY, closure_mono himage hend.2, rfl⟩⟩


/-- The reflected pinching argument excludes an upper circle pole from the
interior of a slab with nonempty ordered sections. -/
private theorem upperCirclePole_pinch_contradiction
    {carrier : Set PlanePoint} {center : PlanePoint} {radius lowerY : ℝ}
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hradius : 0 < radius)
    (hlowerPole : lowerY < center.2 + radius)
    (hhalfFrontier :
      {q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | lowerY < q.2} ⊆ frontier carrier)
    (hhalfGerm : ∀ q : PlanePoint,
      circleValue center radius q = 0 → lowerY < q.2 →
        LocallyOneSided carrier center radius q)
    (hpoleSection :
      (horizontalSection carrier (center.2 + radius)).Nonempty) : False := by
  let pole : PlanePoint := (center.1, center.2 + radius)
  have hpoleCircle : circleValue center radius pole = 0 := by
    dsimp only [pole]
    unfold circleValue
    ring
  have hpoleFrontier : pole ∈ frontier carrier :=
    hhalfFrontier ⟨hpoleCircle, hlowerPole⟩
  obtain ⟨x, hxCarrier⟩ := hpoleSection
  have hxNe : x ≠ center.1 := by
    intro hx
    have hpoleCarrier : pole ∈ carrier := by
      dsimp only [pole]
      rw [← hx]
      exact hxCarrier
    have : pole ∈ carrier ∩ frontier carrier := ⟨hpoleCarrier, hpoleFrontier⟩
    rw [hcarrierOpen.inter_frontier_eq] at this
    exact this
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hcarrierOpen (x, center.2 + radius) hxCarrier
  let d2 : ℝ := (x - center.1) ^ 2
  have hd2 : 0 < d2 := by
    dsimp only [d2]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hxNe)
  let delta : ℝ :=
    min epsilon (min ((center.2 + radius) - lowerY)
      (min radius (d2 / (4 * radius)))) / 2
  have hgap : 0 < (center.2 + radius) - lowerY := sub_pos.mpr hlowerPole
  have hfrac : 0 < d2 / (4 * radius) := div_pos hd2 (by positivity)
  have hminPos : 0 < min epsilon
      (min ((center.2 + radius) - lowerY)
        (min radius (d2 / (4 * radius)))) := by
    exact lt_min hepsilon (lt_min hgap (lt_min hradius hfrac))
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hdeltaEpsilon : delta < epsilon := by
    dsimp only [delta]
    have hle := min_le_left epsilon
      (min ((center.2 + radius) - lowerY)
        (min radius (d2 / (4 * radius))))
    linarith
  have hdeltaGap : delta < (center.2 + radius) - lowerY := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min ((center.2 + radius) - lowerY)
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_left ((center.2 + radius) - lowerY)
      (min radius (d2 / (4 * radius)))
    linarith
  have hdeltaRadius : delta < radius := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min ((center.2 + radius) - lowerY)
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_right ((center.2 + radius) - lowerY)
      (min radius (d2 / (4 * radius)))
    have hle3 := min_le_left radius (d2 / (4 * radius))
    linarith
  have hdeltaFrac : delta < d2 / (4 * radius) := by
    dsimp only [delta]
    have hle1 := min_le_right epsilon
      (min ((center.2 + radius) - lowerY)
        (min radius (d2 / (4 * radius))))
    have hle2 := min_le_right ((center.2 + radius) - lowerY)
      (min radius (d2 / (4 * radius)))
    have hle3 := min_le_right radius (d2 / (4 * radius))
    linarith
  let y := center.2 + radius - delta
  have hyLowerPole : center.2 - radius < y := by dsimp only [y]; linarith
  have hyUpperPole : y < center.2 + radius := by dsimp only [y]; linarith
  have hyLower : lowerY < y := by dsimp only [y]; linarith
  have hxyCarrier : (x, y) ∈ carrier := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq]
    dsimp only [y]
    simp only [Real.dist_eq, sub_self, abs_zero]
    rw [show center.2 + radius - delta - (center.2 + radius) = -delta by ring,
      abs_neg, abs_of_pos hdelta, max_eq_right hdelta.le]
    exact hdeltaEpsilon
  have hpair := circleValue_zero_and_snd_eq_pair_of_between_poles
    hradius hyLowerPole hyUpperPole
  let left := leftCirclePointAtHeight center radius y
  let right := rightCirclePointAtHeight center radius y
  have hleftCircle : circleValue center radius left = 0 := by
    have hm : left ∈ ({left, right} : Set PlanePoint) := Set.mem_insert _ _
    rw [← hpair.1] at hm
    exact hm.1
  have hrightCircle : circleValue center radius right = 0 := by
    have hm : right ∈ ({left, right} : Set PlanePoint) :=
      Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [← hpair.1] at hm
    exact hm.1
  have hleftTransverse : left.1 ≠ center.1 := by
    dsimp only [left, leftCirclePointAtHeight]
    have := hpair.2
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at this
    linarith
  have hrightTransverse : right.1 ≠ center.1 := by
    dsimp only [right, rightCirclePointAtHeight]
    have := hpair.2
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at this
    linarith
  have hleftSectionFrontier :
      left.1 ∈ frontier (horizontalSection carrier y) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hleftCircle hleftTransverse (hhalfGerm left hleftCircle (by
        dsimp only [left, leftCirclePointAtHeight]; exact hyLower))
  have hrightSectionFrontier :
      right.1 ∈ frontier (horizontalSection carrier y) :=
    circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hrightCircle hrightTransverse (hhalfGerm right hrightCircle (by
        dsimp only [right, rightCirclePointAtHeight]; exact hyLower))
  let S : Set ℝ := horizontalSection carrier y
  have hSNonempty : S.Nonempty := ⟨x, hxyCarrier⟩
  have hSopen : IsOpen S := isOpen_horizontalSection hcarrierOpen y
  have hSbounded : Bornology.IsBounded S :=
    isBounded_horizontalSection hcarrierBounded y
  have hsection : S = Ioo (sInf S) (sSup S) :=
    CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hSNonempty hSbounded (hsections y)
  have horder : sInf S ≤ sSup S := by
    obtain ⟨z, hz⟩ := hSNonempty
    have hz' : z ∈ Ioo (sInf S) (sSup S) := hsection ▸ hz
    exact hz'.1.le.trans hz'.2.le
  have hends := openInterval_endpoints_of_ordered_frontier horder hsection
    hleftSectionFrontier hrightSectionFrontier hpair.2
  have hxInterval : x ∈ Ioo left.1 right.1 := by
    have hxS : x ∈ S := hxyCarrier
    rw [hsection, hends.1, hends.2] at hxS
    exact hxS
  have hsqrtSq :
      (√(radius ^ 2 - (y - center.2) ^ 2)) ^ 2 =
        radius ^ 2 - (y - center.2) ^ 2 := by
    apply Real.sq_sqrt
    have hleft : 0 < radius - (y - center.2) := by linarith
    have hright : 0 < radius + (y - center.2) := by linarith
    nlinarith [mul_pos hleft hright]
  have hd2Lt : d2 < radius ^ 2 - (y - center.2) ^ 2 := by
    dsimp only [left, right, leftCirclePointAtHeight,
      rightCirclePointAtHeight] at hxInterval
    dsimp only [d2]
    have hprod := mul_pos (sub_pos.mpr hxInterval.1)
      (sub_pos.mpr hxInterval.2)
    nlinarith [hprod]
  have hradicandLt : radius ^ 2 - (y - center.2) ^ 2 < d2 := by
    dsimp only [y]
    have hmul0 := (lt_div_iff₀ (by positivity : 0 < 4 * radius)).mp
      hdeltaFrac
    have hmul : 4 * radius * delta < d2 := by nlinarith [hmul0]
    dsimp only [d2] at hmul ⊢
    nlinarith [sq_nonneg delta]
  linarith


/-- Global two-sided carrier reach excludes both supporting-circle poles from
the interior of a strict slab by horizontal-section pinching. -/
theorem strictSlab_supporting_poles_outside_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) :
    (A.supportingCenterAt p).2 - |1 / K| ≤ lowerY ∧
      upperY ≤ (A.supportingCenterAt p).2 + |1 / K| := by
  let center := A.supportingCenterAt p
  let radius := |1 / K|
  let slab : Set PlanePoint := {q : PlanePoint |
    lowerY < q.2 ∧ q.2 < upperY}
  have hradius : 0 < radius := abs_pos.mpr (one_div_ne_zero hK)
  have hpCircle : circleValue center radius p.1 = 0 := by
    have hpSupport := A.base_mem_supportAt p
    dsimp only [center, radius]
    rwa [A.supportAt_eq_circleValue_zero p hK] at hpSupport
  constructor
  · by_contra hnot
    have hbad : lowerY < center.2 - radius := lt_of_not_ge hnot
    let half : Set PlanePoint :=
      {q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | q.2 < upperY}
    have hclip :
        ({q : PlanePoint | circleValue center radius q = 0} ∩ slab) = half := by
      ext q
      constructor
      · rintro ⟨hqCircle, hqLower, hqUpper⟩
        exact ⟨hqCircle, hqUpper⟩
      · rintro ⟨hqCircle, hqUpper⟩
        have hqBottom := (circleValue_zero_snd_bounds hradius hqCircle).1
        exact ⟨hqCircle, hbad.trans_le hqBottom, hqUpper⟩
    have hpHalf : p.1 ∈ half := ⟨hpCircle, p.2.2.2⟩
    have hcomponent :
        connectedComponentIn (frontier carrier ∩ slab) p.1 = half := by
      rw [connectedComponentIn_eq_circleClip_component A p hK, hclip]
      apply Set.Subset.antisymm (connectedComponentIn_subset half p.1)
      exact (circleValue_zero_inter_lower_isPreconnected hradius).subset_connectedComponentIn
        hpHalf (Subset.rfl)
    have hhalfFrontier : half ⊆ frontier carrier := by
      rw [← hcomponent]
      exact (connectedComponentIn_subset (frontier carrier ∩ slab) p.1).trans
        inter_subset_left
    have hhalfGerm : ∀ q : PlanePoint,
        circleValue center radius q = 0 → q.2 < upperY →
          LocallyOneSided carrier center radius q := by
      intro q hqCircle hqUpper
      have hqBottom := (circleValue_zero_snd_bounds hradius hqCircle).1
      have hqLocus : q ∈ frontier carrier ∩ slab := by
        exact ⟨hhalfFrontier ⟨hqCircle, hqUpper⟩,
          hbad.trans_le hqBottom, hqUpper⟩
      have hqComponent : q ∈
          connectedComponentIn (frontier carrier ∩ slab) p.1 := by
        rw [hcomponent]
        exact ⟨hqCircle, hqUpper⟩
      have hqImage : q ∈ ((↑) :
          (frontier carrier ∩ slab : Set PlanePoint) → PlanePoint) ''
            connectedComponent p := by
        rwa [← connectedComponentIn_eq_image p.2]
      rcases hqImage with ⟨z, hzComponent, hzq⟩
      have hcenterEq := supportingCenterAt_eq_of_mem_connectedComponent
        A p z hK hzComponent
      have hgerm := mixedAtlas_locallyOneSided_supportingCircle A z hK
      dsimp only [center, radius]
      rw [hcenterEq, hzq] at hgerm
      exact hgerm
    have hpoleSection :
        (horizontalSection carrier (center.2 - radius)).Nonempty := by
      apply horizontalSection_nonempty_of_connected_twoSided_reach
        hcarrierConnected hlow hhigh
      constructor
      · exact hbad.le
      · have hpBounds := circleValue_zero_snd_bounds hradius hpCircle
        exact hpBounds.1.trans p.2.2.2.le
    exact lowerCirclePole_pinch_contradiction hcarrierOpen hcarrierBounded
      hsections hradius (by
        have hpBounds := circleValue_zero_snd_bounds hradius hpCircle
        exact hpBounds.1.trans_lt p.2.2.2)
      hhalfFrontier hhalfGerm hpoleSection
  · by_contra hnot
    have hbad : center.2 + radius < upperY := lt_of_not_ge hnot
    let half : Set PlanePoint :=
      {q : PlanePoint | circleValue center radius q = 0} ∩
        {q : PlanePoint | lowerY < q.2}
    have hclip :
        ({q : PlanePoint | circleValue center radius q = 0} ∩ slab) = half := by
      ext q
      constructor
      · rintro ⟨hqCircle, hqLower, hqUpper⟩
        exact ⟨hqCircle, hqLower⟩
      · rintro ⟨hqCircle, hqLower⟩
        have hqTop := (circleValue_zero_snd_bounds hradius hqCircle).2
        exact ⟨hqCircle, hqLower, hqTop.trans_lt hbad⟩
    have hpHalf : p.1 ∈ half := ⟨hpCircle, p.2.2.1⟩
    have hcomponent :
        connectedComponentIn (frontier carrier ∩ slab) p.1 = half := by
      rw [connectedComponentIn_eq_circleClip_component A p hK, hclip]
      apply Set.Subset.antisymm (connectedComponentIn_subset half p.1)
      exact (circleValue_zero_inter_upper_isPreconnected hradius).subset_connectedComponentIn
        hpHalf (Subset.rfl)
    have hhalfFrontier : half ⊆ frontier carrier := by
      rw [← hcomponent]
      exact (connectedComponentIn_subset (frontier carrier ∩ slab) p.1).trans
        inter_subset_left
    have hhalfGerm : ∀ q : PlanePoint,
        circleValue center radius q = 0 → lowerY < q.2 →
          LocallyOneSided carrier center radius q := by
      intro q hqCircle hqLower
      have hqTop := (circleValue_zero_snd_bounds hradius hqCircle).2
      have hqLocus : q ∈ frontier carrier ∩ slab := by
        exact ⟨hhalfFrontier ⟨hqCircle, hqLower⟩,
          hqLower, hqTop.trans_lt hbad⟩
      have hqComponent : q ∈
          connectedComponentIn (frontier carrier ∩ slab) p.1 := by
        rw [hcomponent]
        exact ⟨hqCircle, hqLower⟩
      have hqImage : q ∈ ((↑) :
          (frontier carrier ∩ slab : Set PlanePoint) → PlanePoint) ''
            connectedComponent p := by
        rwa [← connectedComponentIn_eq_image p.2]
      rcases hqImage with ⟨z, hzComponent, hzq⟩
      have hcenterEq := supportingCenterAt_eq_of_mem_connectedComponent
        A p z hK hzComponent
      have hgerm := mixedAtlas_locallyOneSided_supportingCircle A z hK
      dsimp only [center, radius]
      rw [hcenterEq, hzq] at hgerm
      exact hgerm
    have hpoleSection :
        (horizontalSection carrier (center.2 + radius)).Nonempty := by
      apply horizontalSection_nonempty_of_connected_twoSided_reach
        hcarrierConnected hlow hhigh
      constructor
      · have hpBounds := circleValue_zero_snd_bounds hradius hpCircle
        exact p.2.2.1.le.trans hpBounds.2
      · exact hbad.le
    exact upperCirclePole_pinch_contradiction hcarrierOpen hcarrierBounded
      hsections hradius (by
        have hpBounds := circleValue_zero_snd_bounds hradius hpCircle
        exact p.2.2.1.trans_le hpBounds.2)
      hhalfFrontier hhalfGerm hpoleSection


/-- Once interior poles are excluded, a curved strict-slab component is one
complete left or right branch and its closure reaches both interfaces. -/
theorem strictSlab_component_reaches_both_interfaces_of_ne_zero
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) :
    StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY := by
  obtain ⟨hlowerPole, hupperPole⟩ :=
    strictSlab_supporting_poles_outside_of_global_reach A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hlow hhigh p hK
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hleftEndpoints := continuous_image_Ioo_endpoints_mem_closure
    (show Continuous (leftCirclePointAtHeight
      (A.supportingCenterAt p) |1 / K|) by
        unfold leftCirclePointAtHeight
        fun_prop) hlowerUpper
  have hrightEndpoints := continuous_image_Ioo_endpoints_mem_closure
    (show Continuous (rightCirclePointAtHeight
      (A.supportingCenterAt p) |1 / K|) by
        unfold rightCirclePointAtHeight
        fun_prop) hlowerUpper
  rcases strictSlab_component_eq_left_or_right_arc A p hK
      hlowerPole hupperPole with hleft | hright
  · rw [leftCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
      at hleft
    unfold StrictSlabComponentReachesBothInterfaces
    rw [hleft]
    exact ⟨⟨leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| lowerY,
        hleftEndpoints.1, rfl⟩,
      ⟨leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| upperY,
        hleftEndpoints.2, rfl⟩⟩
  · rw [rightCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
      at hright
    unfold StrictSlabComponentReachesBothInterfaces
    rw [hright]
    exact ⟨⟨rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| lowerY,
        hrightEndpoints.1, rfl⟩,
      ⟨rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| upperY,
        hrightEndpoints.2, rfl⟩⟩

/-- Every actual full strict-slab frontier component reaches both interfaces,
with the affine and curved cases discharged separately. -/
theorem strictSlab_component_reaches_both_interfaces_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint)) :
    StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY := by
  rcases eq_or_ne K 0 with hK | hK
  · exact strictSlab_component_reaches_both_interfaces_of_eq_zero A
      hcarrierBounded hlowerUpper p hK
  · exact strictSlab_component_reaches_both_interfaces_of_ne_zero A
      hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
      hlow hhigh p hK

/-- In the curved branch the derived global reach premise feeds both existing
consumers: actual frontier/support contacts and complete left/right arc
classification.  No contact, pole bound, or component reach is supplied by
the caller. -/
theorem strictSlab_component_contacts_and_complete_circle_arc_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) :
    (∃ lowerContact upperContact : PlanePoint,
        lowerContact ∈ frontier carrier ∩ A.supportAt p ∧
        upperContact ∈ frontier carrier ∩ A.supportAt p ∧
        lowerContact.2 = lowerY ∧ upperContact.2 = upperY ∧
        (upperY - lowerY) / 2 ≤ |1 / K|) ∧
      (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
          leftCircleStrictSlabArc
            (A.supportingCenterAt p) |1 / K| lowerY upperY ∨
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
          rightCircleStrictSlabArc
            (A.supportingCenterAt p) |1 / K| lowerY upperY) := by
  have hreach :=
    strictSlab_component_reaches_both_interfaces_of_ne_zero A
      hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
      hlow hhigh p hK
  exact ⟨strictSlab_component_reach_derives_actual_support_contacts
      A p hK hreach,
    strictSlab_component_eq_complete_circle_arc_of_reach A p hK hreach⟩

/-- One geometric left branch has at most one point at each height. -/
theorem leftCircleStrictSlabArc_eq_of_snd_eq
    {center p q : PlanePoint} {radius lowerY upperY : ℝ}
    (hp : p ∈ leftCircleStrictSlabArc center radius lowerY upperY)
    (hq : q ∈ leftCircleStrictSlabArc center radius lowerY upperY)
    (hheight : p.2 = q.2) :
    p = q := by
  apply Prod.ext
  · unfold leftCircleStrictSlabArc at hp hq
    simp only [Set.mem_ofPred_eq] at hp hq
    unfold circleValue at hp hq
    have hsquares :
        (p.1 - center.1) ^ 2 = (q.1 - center.1) ^ 2 := by
      rw [hheight] at hp
      nlinarith [hp.1, hq.1]
    rcases eq_or_eq_neg_of_sq_eq_sq
        (p.1 - center.1) (q.1 - center.1) hsquares with heq | heq
    · linarith
    · nlinarith [hp.2.2.2, hq.2.2.2]
  · exact hheight

/-- One geometric right branch has at most one point at each height. -/
theorem rightCircleStrictSlabArc_eq_of_snd_eq
    {center p q : PlanePoint} {radius lowerY upperY : ℝ}
    (hp : p ∈ rightCircleStrictSlabArc center radius lowerY upperY)
    (hq : q ∈ rightCircleStrictSlabArc center radius lowerY upperY)
    (hheight : p.2 = q.2) :
    p = q := by
  apply Prod.ext
  · unfold rightCircleStrictSlabArc at hp hq
    simp only [Set.mem_ofPred_eq] at hp hq
    unfold circleValue at hp hq
    have hsquares :
        (p.1 - center.1) ^ 2 = (q.1 - center.1) ^ 2 := by
      rw [hheight] at hp
      nlinarith [hp.1, hq.1]
    rcases eq_or_eq_neg_of_sq_eq_sq
        (p.1 - center.1) (q.1 - center.1) hsquares with heq | heq
    · linarith
    · nlinarith [hp.2.2.2, hq.2.2.2]
  · exact hheight

/-- Closing a complete left strict-slab branch adds exactly its two interface
endpoints. -/
theorem closure_leftCircleStrictSlabArc_eq_image_Icc
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius)
    (hlowerUpper : lowerY < upperY) :
    closure (leftCircleStrictSlabArc center radius lowerY upperY) =
      leftCirclePointAtHeight center radius '' Icc lowerY upperY := by
  rw [leftCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
  let f := leftCirclePointAtHeight center radius
  have hf : Continuous f := by
    dsimp only [f]
    unfold leftCirclePointAtHeight
    fun_prop
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact image_mono Ioo_subset_Icc_self
    · exact (isCompact_Icc.image hf).isClosed
  · intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    apply image_closure_subset_closure_image hf
    refine ⟨y, ?_, rfl⟩
    rw [closure_Ioo hlowerUpper.ne]
    exact hy

/-- Closing a complete right strict-slab branch likewise adds only its two
interface endpoints. -/
theorem closure_rightCircleStrictSlabArc_eq_image_Icc
    {center : PlanePoint} {radius lowerY upperY : ℝ}
    (hradius : 0 < radius)
    (hlowerPole : center.2 - radius ≤ lowerY)
    (hupperPole : upperY ≤ center.2 + radius)
    (hlowerUpper : lowerY < upperY) :
    closure (rightCircleStrictSlabArc center radius lowerY upperY) =
      rightCirclePointAtHeight center radius '' Icc lowerY upperY := by
  rw [rightCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
  let f := rightCirclePointAtHeight center radius
  have hf : Continuous f := by
    dsimp only [f]
    unfold rightCirclePointAtHeight
    fun_prop
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact image_mono Ioo_subset_Icc_self
    · exact (isCompact_Icc.image hf).isClosed
  · intro q hq
    rcases hq with ⟨y, hy, rfl⟩
    apply image_closure_subset_closure_image hf
    refine ⟨y, ?_, rfl⟩
    rw [closure_Ioo hlowerUpper.ne]
    exact hy

/-- The closed image of a height graph meets each horizontal line in its
canonical point. -/
theorem heightGraph_image_Icc_inter_horizontal_eq_singleton
    {f : ℝ → PlanePoint} {a b y : ℝ}
    (hheight : ∀ t, (f t).2 = t) (hy : y ∈ Icc a b) :
    f '' Icc a b ∩ {q : PlanePoint | q.2 = y} = {f y} := by
  ext q
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hty⟩
    have htEq : t = y := (hheight t).symm.trans hty
    subst t
    exact Set.mem_singleton _
  · intro hq
    have hqEq : q = f y := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    exact ⟨⟨y, hy, rfl⟩, hheight y⟩

/-- The closure of a curved strict-slab component has exactly one contact on
each interface.  Both contacts stay on the selected component's propagated
support and on the actual carrier frontier; component incidence is not erased
to bare support incidence. -/
theorem strictSlab_component_closure_interface_singletons_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) :
    ∃ lowerContact upperContact : PlanePoint,
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
          {q : PlanePoint | q.2 = lowerY} = {lowerContact} ∧
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
          {q : PlanePoint | q.2 = upperY} = {upperContact} ∧
      lowerContact ∈ frontier carrier ∩ A.supportAt p ∧
      upperContact ∈ frontier carrier ∩ A.supportAt p ∧
      lowerContact.2 = lowerY ∧ upperContact.2 = upperY := by
  obtain ⟨hlowerPole, hupperPole⟩ :=
    strictSlab_supporting_poles_outside_of_global_reach A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hlow hhigh p hK
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  have hclosureSubset :=
    closure_strictSlab_component_subset_supportAt_and_frontier A p hK
  rcases strictSlab_component_eq_left_or_right_arc
      A p hK hlowerPole hupperPole with hleft | hright
  · let lowerContact :=
      leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| lowerY
    let upperContact :=
      leftCirclePointAtHeight (A.supportingCenterAt p) |1 / K| upperY
    have hlowerEq :
        closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = lowerY} = {lowerContact} := by
      rw [hleft,
        closure_leftCircleStrictSlabArc_eq_image_Icc hradius
          hlowerPole hupperPole hlowerUpper]
      exact heightGraph_image_Icc_inter_horizontal_eq_singleton
        (fun _ => rfl) ⟨le_rfl, hlowerUpper.le⟩
    have hupperEq :
        closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = upperY} = {upperContact} := by
      rw [hleft,
        closure_leftCircleStrictSlabArc_eq_image_Icc hradius
          hlowerPole hupperPole hlowerUpper]
      exact heightGraph_image_Icc_inter_horizontal_eq_singleton
        (fun _ => rfl) ⟨hlowerUpper.le, le_rfl⟩
    have hlowerClosure :
        lowerContact ∈ closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) := by
      have : lowerContact ∈
          closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = lowerY} := by
        rw [hlowerEq]
        exact Set.mem_singleton _
      exact this.1
    have hupperClosure :
        upperContact ∈ closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) := by
      have : upperContact ∈
          closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = upperY} := by
        rw [hupperEq]
        exact Set.mem_singleton _
      exact this.1
    have hlowerActual := hclosureSubset hlowerClosure
    have hupperActual := hclosureSubset hupperClosure
    exact ⟨lowerContact, upperContact, hlowerEq, hupperEq,
      ⟨hlowerActual.2, hlowerActual.1⟩,
      ⟨hupperActual.2, hupperActual.1⟩, rfl, rfl⟩
  · let lowerContact :=
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| lowerY
    let upperContact :=
      rightCirclePointAtHeight (A.supportingCenterAt p) |1 / K| upperY
    have hlowerEq :
        closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = lowerY} = {lowerContact} := by
      rw [hright,
        closure_rightCircleStrictSlabArc_eq_image_Icc hradius
          hlowerPole hupperPole hlowerUpper]
      exact heightGraph_image_Icc_inter_horizontal_eq_singleton
        (fun _ => rfl) ⟨le_rfl, hlowerUpper.le⟩
    have hupperEq :
        closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = upperY} = {upperContact} := by
      rw [hright,
        closure_rightCircleStrictSlabArc_eq_image_Icc hradius
          hlowerPole hupperPole hlowerUpper]
      exact heightGraph_image_Icc_inter_horizontal_eq_singleton
        (fun _ => rfl) ⟨hlowerUpper.le, le_rfl⟩
    have hlowerClosure :
        lowerContact ∈ closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) := by
      have : lowerContact ∈
          closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = lowerY} := by
        rw [hlowerEq]
        exact Set.mem_singleton _
      exact this.1
    have hupperClosure :
        upperContact ∈ closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1) := by
      have : upperContact ∈
          closure (connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) p.1) ∩
            {q : PlanePoint | q.2 = upperY} := by
        rw [hupperEq]
        exact Set.mem_singleton _
      exact this.1
    have hlowerActual := hclosureSubset hlowerClosure
    have hupperActual := hclosureSubset hupperClosure
    exact ⟨lowerContact, upperContact, hlowerEq, hupperEq,
      ⟨hlowerActual.2, hlowerActual.1⟩,
      ⟨hupperActual.2, hupperActual.1⟩, rfl, rfl⟩

/-- A curved maximal strict-slab component is a graph over height.  This is a
consequence of its derived complete left/right circle-branch classification,
not an assumed graph orientation. -/
theorem strictSlab_component_snd_injective_of_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0)
    (hreach : StrictSlabComponentReachesBothInterfaces
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY)
    {q r : PlanePoint}
    (hq : q ∈ connectedComponentIn
      (frontier carrier ∩ {z : PlanePoint |
        lowerY < z.2 ∧ z.2 < upperY}) p.1)
    (hr : r ∈ connectedComponentIn
      (frontier carrier ∩ {z : PlanePoint |
        lowerY < z.2 ∧ z.2 < upperY}) p.1)
    (hheight : q.2 = r.2) :
    q = r := by
  rcases strictSlab_component_eq_complete_circle_arc_of_reach
      A p hK hreach with hleft | hright
  · exact leftCircleStrictSlabArc_eq_of_snd_eq
      (hleft ▸ hq) (hleft ▸ hr) hheight
  · exact rightCircleStrictSlabArc_eq_of_snd_eq
      (hright ▸ hq) (hright ▸ hr) hheight

/-- Every curved strict-slab component contains one actual frontier point at
every strict intermediate height. -/
theorem strictSlab_component_contains_height_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY y : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ z : ℝ, (horizontalSection carrier z).OrdConnected)
    (_hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint))
    (hK : K ≠ 0) (hy : lowerY < y ∧ y < upperY) :
    ∃ q ∈ connectedComponentIn
        (frontier carrier ∩ {z : PlanePoint |
          lowerY < z.2 ∧ z.2 < upperY}) p.1,
      q.2 = y := by
  obtain ⟨hlowerPole, hupperPole⟩ :=
    strictSlab_supporting_poles_outside_of_global_reach A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hlow hhigh p hK
  have hradius : 0 < |1 / K| := abs_pos.mpr (one_div_ne_zero hK)
  rcases strictSlab_component_eq_left_or_right_arc
      A p hK hlowerPole hupperPole with hleft | hright
  · refine ⟨leftCirclePointAtHeight
        (A.supportingCenterAt p) |1 / K| y, ?_, rfl⟩
    rw [hleft,
      leftCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
    exact ⟨y, hy, rfl⟩
  · refine ⟨rightCirclePointAtHeight
        (A.supportingCenterAt p) |1 / K| y, ?_, rfl⟩
    rw [hright,
      rightCircleStrictSlabArc_eq_image hradius hlowerPole hupperPole]
    exact ⟨y, hy, rfl⟩

/-- Every strict intermediate section supplies two ordered actual frontier
bases for the strict-slab atlas.  They are constructed from the true open
carrier section, not from a supplied strip-arc list. -/
theorem exists_ordered_strictSlab_section_bases
    {carrier : Set PlanePoint} {K lowerY upperY y : ℝ}
    (_A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ z : ℝ, (horizontalSection carrier z).OrdConnected)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (hy : lowerY < y ∧ y < upperY) :
    ∃ leftBase rightBase :
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint),
      leftBase.1.2 = y ∧ rightBase.1.2 = y ∧
      leftBase.1.1 =
        sInf (horizontalSection carrier y) ∧
      rightBase.1.1 =
        sSup (horizontalSection carrier y) ∧
      leftBase.1.1 < rightBase.1.1 := by
  let S : Set ℝ := horizontalSection carrier y
  have hSNonempty : S.Nonempty := by
    apply horizontalSection_nonempty_of_connected_twoSided_reach
      hcarrierConnected hlow hhigh
    exact ⟨hy.1.le, hy.2.le⟩
  have hSopen : IsOpen S := isOpen_horizontalSection hcarrierOpen y
  have hSbounded : Bornology.IsBounded S :=
    isBounded_horizontalSection hcarrierBounded y
  have hsection : S = Ioo (sInf S) (sSup S) :=
    CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hSNonempty hSbounded (hsections y)
  have horder : sInf S < sSup S := by
    obtain ⟨x, hx⟩ := hSNonempty
    have hx' : x ∈ Ioo (sInf S) (sSup S) := hsection ▸ hx
    exact hx'.1.trans hx'.2
  have hsectionFrontier :
      frontier S = ({sInf S, sSup S} : Set ℝ) := by
    calc
      frontier S = frontier (Ioo (sInf S) (sSup S)) :=
        congrArg frontier hsection
      _ = {sInf S, sSup S} := frontier_Ioo horder
  have hleftSectionFrontier : sInf S ∈ frontier S := by
    rw [hsectionFrontier]
    simp
  have hrightSectionFrontier : sSup S ∈ frontier S := by
    rw [hsectionFrontier]
    simp
  have hleftFrontier : (sInf S, y) ∈ frontier carrier :=
    frontier_horizontalSection_subset carrier y hleftSectionFrontier
  have hrightFrontier : (sSup S, y) ∈ frontier carrier :=
    frontier_horizontalSection_subset carrier y hrightSectionFrontier
  let leftBase :
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint) :=
    ⟨(sInf S, y), hleftFrontier, hy⟩
  let rightBase :
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint) :=
    ⟨(sSup S, y), hrightFrontier, hy⟩
  refine ⟨leftBase, rightBase, rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa only [leftBase, rightBase] using horder

/-- Complete branch-neutral inventory of the regular strict slab.  The two
bases lie on the ordered endpoints of one actual section; their distinct
maximal components cover the whole strict-slab frontier.  Both components have
the common geometric radius `|1 / K|`, actual contacts on both interfaces, and
complete left/right circle-branch descriptions. -/
def StrictSlabTwoArcInventory
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K) : Prop :=
  ∃ leftBase rightBase :
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint),
    leftBase.1.2 = rightBase.1.2 ∧
    leftBase.1.1 < rightBase.1.1 ∧
    0 < |1 / K| ∧
    (upperY - lowerY) / 2 ≤ |1 / K| ∧
    connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ≠
      connectedComponentIn
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 ∧
    (∀ p : (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint),
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ∨
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1) ∧
    frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY} =
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ∪
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 ∧
    (∃ lowerContact upperContact : PlanePoint,
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1) ∩
          {q : PlanePoint | q.2 = lowerY} = {lowerContact} ∧
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1) ∩
          {q : PlanePoint | q.2 = upperY} = {upperContact} ∧
      lowerContact ∈ frontier carrier ∩ A.supportAt leftBase ∧
      upperContact ∈ frontier carrier ∩ A.supportAt leftBase ∧
      lowerContact.2 = lowerY ∧ upperContact.2 = upperY) ∧
    (∃ lowerContact upperContact : PlanePoint,
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1) ∩
          {q : PlanePoint | q.2 = lowerY} = {lowerContact} ∧
      closure (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1) ∩
          {q : PlanePoint | q.2 = upperY} = {upperContact} ∧
      lowerContact ∈ frontier carrier ∩ A.supportAt rightBase ∧
      upperContact ∈ frontier carrier ∩ A.supportAt rightBase ∧
      lowerContact.2 = lowerY ∧ upperContact.2 = upperY) ∧
    (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 =
          leftCircleStrictSlabArc
            (A.supportingCenterAt leftBase) |1 / K| lowerY upperY ∨
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 =
          rightCircleStrictSlabArc
            (A.supportingCenterAt leftBase) |1 / K| lowerY upperY) ∧
    (connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 =
          leftCircleStrictSlabArc
            (A.supportingCenterAt rightBase) |1 / K| lowerY upperY ∨
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 =
          rightCircleStrictSlabArc
            (A.supportingCenterAt rightBase) |1 / K| lowerY upperY)

/-- Global representative reach constructs the complete two-arc inventory;
neither component bases, contacts, supporting circles, nor a finite component
list are premises. -/
theorem strictSlab_twoArcInventory_of_global_reach
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (A : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (hlow : ∃ q ∈ carrier, q.2 ≤ lowerY)
    (hhigh : ∃ q ∈ carrier, upperY ≤ q.2)
    (hK : K ≠ 0) :
    StrictSlabTwoArcInventory A := by
  let y : ℝ := (lowerY + upperY) / 2
  have hy : lowerY < y ∧ y < upperY := by
    dsimp only [y]
    constructor <;> linarith
  obtain ⟨leftBase, rightBase, hleftHeight, hrightHeight,
      hleftEndpoint, hrightEndpoint, hbaseOrder⟩ :=
    exists_ordered_strictSlab_section_bases A hcarrierOpen
      hcarrierBounded hcarrierConnected hsections hlow hhigh hy
  have hreach (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint)) :
      StrictSlabComponentReachesBothInterfaces
        (frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY}) p.1 lowerY upperY :=
    strictSlab_component_reaches_both_interfaces_of_global_reach A
      hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
      hlow hhigh p
  have hevery (p : (frontier carrier ∩ {q : PlanePoint |
      lowerY < q.2 ∧ q.2 < upperY} : Set PlanePoint)) :
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
          connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ∨
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) p.1 =
          connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 := by
    obtain ⟨q, hqComponent, hqHeight⟩ :=
      strictSlab_component_contains_height_of_global_reach A hcarrierOpen
        hcarrierBounded hcarrierConnected hsections hlowerUpper hlow hhigh
        p hK hy
    have hqLocus :
        q ∈ frontier carrier ∩ {z : PlanePoint |
          lowerY < z.2 ∧ z.2 < upperY} :=
      connectedComponentIn_subset
        (frontier carrier ∩ {z : PlanePoint |
          lowerY < z.2 ∧ z.2 < upperY}) p.1 hqComponent
    let q' : (frontier carrier ∩ {z : PlanePoint |
        lowerY < z.2 ∧ z.2 < upperY} : Set PlanePoint) := ⟨q, hqLocus⟩
    have hqEndpoint :=
      strictSlab_frontier_point_eq_section_endpoint_of_component_reach
        A hcarrierOpen hcarrierBounded hsections q' hK (hreach q')
    rw [hqHeight] at hqEndpoint
    rcases hqEndpoint with hqLeft | hqRight
    · left
      have hqEq : q = leftBase.1 := by
        apply Prod.ext
        · exact hqLeft.trans hleftEndpoint.symm
        · exact hqHeight.trans hleftHeight.symm
      simpa only [hqEq] using connectedComponentIn_eq hqComponent
    · right
      have hqEq : q = rightBase.1 := by
        apply Prod.ext
        · exact hqRight.trans hrightEndpoint.symm
        · exact hqHeight.trans hrightHeight.symm
      simpa only [hqEq] using connectedComponentIn_eq hqComponent
  have hcomponentsNe :
      connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ≠
        connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 := by
    intro hcomponents
    have hrightInLeft :
        rightBase.1 ∈ connectedComponentIn
          (frontier carrier ∩ {q : PlanePoint |
            lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 := by
      rw [hcomponents]
      exact mem_connectedComponentIn rightBase.2
    have hpointsEq :=
      strictSlab_component_snd_injective_of_reach A leftBase hK
        (hreach leftBase)
        (mem_connectedComponentIn leftBase.2) hrightInLeft
        (hleftHeight.trans hrightHeight.symm)
    have hfstEq := congrArg Prod.fst hpointsEq
    exact (ne_of_lt hbaseOrder) hfstEq
  have hcomplete :
      frontier carrier ∩ {q : PlanePoint |
          lowerY < q.2 ∧ q.2 < upperY} =
        connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) leftBase.1 ∪
          connectedComponentIn
            (frontier carrier ∩ {q : PlanePoint |
              lowerY < q.2 ∧ q.2 < upperY}) rightBase.1 := by
    apply Set.Subset.antisymm
    · intro q hq
      let q' : (frontier carrier ∩ {z : PlanePoint |
          lowerY < z.2 ∧ z.2 < upperY} : Set PlanePoint) := ⟨q, hq⟩
      rcases hevery q' with hleft | hright
      · left
        rw [← hleft]
        exact mem_connectedComponentIn q'.2
      · right
        rw [← hright]
        exact mem_connectedComponentIn q'.2
    · exact union_subset
        (connectedComponentIn_subset _ leftBase.1)
        (connectedComponentIn_subset _ rightBase.1)
  have hleftData :=
    strictSlab_component_contacts_and_complete_circle_arc_of_global_reach
      A hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
        hlow hhigh leftBase hK
  have hrightData :=
    strictSlab_component_contacts_and_complete_circle_arc_of_global_reach
      A hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
        hlow hhigh rightBase hK
  have hradiusSpan : (upperY - lowerY) / 2 ≤ |1 / K| := by
    rcases hleftData.1 with
      ⟨_lowerContact, _upperContact, _hlower, _hupper,
        _hlowerHeight, _hupperHeight, hspan⟩
    exact hspan
  have hleftClosure :=
    strictSlab_component_closure_interface_singletons_of_global_reach
      A hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
        hlow hhigh leftBase hK
  have hrightClosure :=
    strictSlab_component_closure_interface_singletons_of_global_reach
      A hcarrierOpen hcarrierBounded hcarrierConnected hsections hlowerUpper
        hlow hhigh rightBase hK
  exact ⟨leftBase, rightBase,
    hleftHeight.trans hrightHeight.symm,
    hbaseOrder,
    abs_pos.mpr (one_div_ne_zero hK),
    hradiusSpan,
    hcomponentsNe,
    hevery,
    hcomplete,
    hleftClosure,
    hrightClosure,
    hleftData.2,
    hrightData.2⟩


/-- If the upper and lower exterior atlases carry the same common curvature as
the strict slab, actual nonempty exterior components derive nonzero curvature
and both global reach witnesses.  Thus the two-strip-arc inventory has no
caller-supplied curvature or component-reach premise. -/
theorem strictSlab_twoArcInventory_of_twoSidedExterior
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) K)
    (_ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) K)
    (ASlab : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    StrictSlabTwoArcInventory ASlab := by
  obtain ⟨qLow, hqLowCarrier, hqLowHeight⟩ :=
    exists_carrier_snd_lt_of_frontier_snd_lt
      pLower.2.1 pLower.2.2
  obtain ⟨qHigh, hqHighCarrier, hqHighHeight⟩ :=
    exists_carrier_snd_gt_of_frontier_snd_gt
      pUpper.2.1 pUpper.2.2
  apply strictSlab_twoArcInventory_of_global_reach ASlab hcarrierOpen
    hcarrierBounded hcarrierConnected hsections hlowerUpper
  · exact ⟨qLow, hqLowCarrier, hqLowHeight.le⟩
  · exact ⟨qHigh, hqHighCarrier, hqHighHeight.le⟩
  · exact commonCurvature_ne_zero_of_bounded_upperExterior
      AUpper hcarrierBounded pUpper

/-! ## Contact-free density-interface accounting

The regularity assertion immediately before Lemma 3.8 in CMV (printed page 15)
is used here only in its local form: away from genuine circle contacts, an
interface frontier point has one occupied-side graph germ along the horizontal
density interface.  It is not used to continue a constant-curvature chart
through a contact, and it supplies neither contact order nor an interface
segment inventory.
-/

namespace InterfaceAccounting

open CMVRelaxation.FiniteJunctionRepair
open CMVRelaxation.LocalChartPreservation

/-- A branch-neutral vertical graph germ on the actual carrier.  Vertical is
the coordinate forced by a horizontal density interface; the occupied side
remains existential and no circle branch is selected. -/
def HasBranchNeutralVerticalGraphGerm
    (carrier : Set PlanePoint) (p : PlanePoint) : Prop :=
  ∃ side : SpliceGraphOccupiedSide,
    HasContinuousGraphGermOnSide .vertical side carrier p

/-- The source regular-boundary premise feeds the retained continuous germ API
by forgetting only smoothness, not the occupied side or the carrier. -/
theorem HasBranchNeutralVerticalGraphGerm.of_orientedSmooth
    {carrier : Set PlanePoint} {p : PlanePoint}
    (germ : ∃ side : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide .vertical side carrier p) :
    HasBranchNeutralVerticalGraphGerm carrier p := by
  rcases germ with ⟨side, hside⟩
  exact ⟨side, continuousGraphGerm_of_orientedSmooth hside⟩

/-- The two possible constant states in a contact-free vertical half-neighborhood. -/
inductive OccupancyState
  | vacant
  | occupied
  deriving DecidableEq

/-- Four actual closure contacts on one density interface: two from one
exterior continuation component and one from each of the two strict-slab
components.  Coincidences are allowed.  No order or segment decomposition is a
field. -/
structure InterfaceClosureContactInventory
    (carrier : Set PlanePoint) (interfaceY : ℝ) where
  exteriorComponent : Set PlanePoint
  stripFirstComponent : Set PlanePoint
  stripSecondComponent : Set PlanePoint
  exteriorLeft : PlanePoint
  exteriorRight : PlanePoint
  stripFirst : PlanePoint
  stripSecond : PlanePoint
  exteriorLeft_mem_closure : exteriorLeft ∈ closure exteriorComponent
  exteriorRight_mem_closure : exteriorRight ∈ closure exteriorComponent
  stripFirst_interface_singleton :
    closure stripFirstComponent ∩ {q : PlanePoint | q.2 = interfaceY} =
      {stripFirst}
  stripSecond_interface_singleton :
    closure stripSecondComponent ∩ {q : PlanePoint | q.2 = interfaceY} =
      {stripSecond}
  exteriorLeft_mem_frontier : exteriorLeft ∈ frontier carrier
  exteriorRight_mem_frontier : exteriorRight ∈ frontier carrier
  stripFirst_mem_frontier : stripFirst ∈ frontier carrier
  stripSecond_mem_frontier : stripSecond ∈ frontier carrier
  exteriorLeft_height : exteriorLeft.2 = interfaceY
  exteriorRight_height : exteriorRight.2 = interfaceY
  stripFirst_height : stripFirst.2 = interfaceY
  stripSecond_height : stripSecond.2 = interfaceY

namespace InterfaceClosureContactInventory

variable {carrier : Set PlanePoint} {interfaceY : ℝ}

/-- The contact set is derived from actual component closures; it is not a
caller-supplied finite segment inventory. -/
def contactSet (C : InterfaceClosureContactInventory carrier interfaceY) :
    Set PlanePoint :=
  {C.exteriorLeft, C.exteriorRight, C.stripFirst, C.stripSecond}

theorem contactSet_finite
    (C : InterfaceClosureContactInventory carrier interfaceY) :
    C.contactSet.Finite := by
  simp [contactSet]

theorem contactSet_subset_frontier
    (C : InterfaceClosureContactInventory carrier interfaceY) :
    C.contactSet ⊆ frontier carrier := by
  intro p hp
  simp only [contactSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact C.exteriorLeft_mem_frontier
  · exact C.exteriorRight_mem_frontier
  · exact C.stripFirst_mem_frontier
  · exact C.stripSecond_mem_frontier

theorem contactSet_second_eq
    (C : InterfaceClosureContactInventory carrier interfaceY)
    {p : PlanePoint} (hp : p ∈ C.contactSet) :
    p.2 = interfaceY := by
  simp only [contactSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact C.exteriorLeft_height
  · exact C.exteriorRight_height
  · exact C.stripFirst_height
  · exact C.stripSecond_height

end InterfaceClosureContactInventory

/-- Branch-neutral interface regularity away from the actual closure contacts.
It is required only at points already known to be on the literal frontier.
Thus it neither asserts interface saturation nor hides a segment inventory. -/
def HasInterfaceRegularityAway
    (carrier : Set PlanePoint) (interfaceY : ℝ)
    (contacts : Set PlanePoint) : Prop :=
  ∀ p : PlanePoint, p.2 = interfaceY → p ∉ contacts →
    p ∈ frontier carrier →
      HasBranchNeutralVerticalGraphGerm carrier p

/-- Local occupancy/frontier bookkeeping at one interface abscissa. -/
def HasLocalOccupancyAccounting
    (carrier : Set PlanePoint) (interfaceY x : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∃ below above : OccupancyState,
      (∀ y ∈ Ioo (interfaceY - δ) interfaceY,
        ((x, y) ∈ carrier ↔ below = .occupied)) ∧
      (∀ y ∈ Ioo interfaceY (interfaceY + δ),
        ((x, y) ∈ carrier ↔ above = .occupied)) ∧
      (((x, interfaceY) : PlanePoint) ∈ frontier carrier ↔ below ≠ above)

/-- At every contact-free interface abscissa, the two neighboring vertical
half-neighborhoods have definite occupancy states.  They differ exactly when
the interface point is on the literal frontier.  In particular a frontier slit
with the carrier occupied on both sides is impossible wherever the stated
page-15 local regularity applies. -/
theorem InterfaceClosureContactInventory.contactFree_accounting
    {carrier : Set PlanePoint} {interfaceY : ℝ}
    (C : InterfaceClosureContactInventory carrier interfaceY)
    (hregular :
      HasInterfaceRegularityAway carrier interfaceY C.contactSet)
    {x : ℝ} (hx : ((x, interfaceY) : PlanePoint) ∉ C.contactSet) :
    HasLocalOccupancyAccounting carrier interfaceY x := by
  unfold HasLocalOccupancyAccounting
  by_cases hp : ((x, interfaceY) : PlanePoint) ∈ frontier carrier
  · obtain ⟨side, germ⟩ := hregular (x, interfaceY) rfl hx hp
    cases side with
    | negative =>
        obtain ⟨f, _hf, hfp, hlocal⟩ :=
          germ.exists_vertical_graph_eq_base hp
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
        refine ⟨δ, hδ, .occupied, .vacant, ?_, ?_, by simp [hp]⟩
        · intro y hy
          have hxy := hball (show dist ((x, y) : PlanePoint)
              (x, interfaceY) < δ by
            rw [Prod.dist_eq, max_lt_iff]
            exact ⟨by simpa using hδ, by
              rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2]⟩)
          rw [hfp] at hxy
          constructor
          · intro _hmem
            rfl
          · intro _hstate
            exact hxy.mpr hy.2
        · intro y hy
          have hxy := hball (show dist ((x, y) : PlanePoint)
              (x, interfaceY) < δ by
            rw [Prod.dist_eq, max_lt_iff]
            exact ⟨by simpa using hδ, by
              rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2]⟩)
          rw [hfp] at hxy
          constructor
          · intro hmem
            exfalso
            exact (not_lt_of_ge hy.1.le) (hxy.mp hmem)
          · intro hstate
            cases hstate
    | positive =>
        obtain ⟨f, _hf, hfp, hlocal⟩ :=
          germ.exists_vertical_graph_eq_base hp
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
        refine ⟨δ, hδ, .vacant, .occupied, ?_, ?_, by simp [hp]⟩
        · intro y hy
          have hxy := hball (show dist ((x, y) : PlanePoint)
              (x, interfaceY) < δ by
            rw [Prod.dist_eq, max_lt_iff]
            exact ⟨by simpa using hδ, by
              rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2]⟩)
          rw [hfp] at hxy
          constructor
          · intro hmem
            exfalso
            exact (not_lt_of_ge hy.2.le) (hxy.mp hmem)
          · intro hstate
            cases hstate
        · intro y hy
          have hxy := hball (show dist ((x, y) : PlanePoint)
              (x, interfaceY) < δ by
            rw [Prod.dist_eq, max_lt_iff]
            exact ⟨by simpa using hδ, by
              rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2]⟩)
          rw [hfp] at hxy
          constructor
          · intro _hmem
            rfl
          · intro _hstate
            exact hxy.mpr hy.1
  · have hpInterior :
        ((x, interfaceY) : PlanePoint) ∈ interior carrier ∪
          interior carrierᶜ := by
      have hp' :
          ((x, interfaceY) : PlanePoint) ∈ (frontier carrier)ᶜ := hp
      rwa [compl_frontier_eq_union_interior] at hp'
    rcases hpInterior with hpCarrier | hpComplement
    · have hnhds : carrier ∈ 𝓝 ((x, interfaceY) : PlanePoint) :=
        mem_interior_iff_mem_nhds.mp hpCarrier
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      refine ⟨δ, hδ, .occupied, .occupied, ?_, ?_, by simp [hp]⟩
      · intro y hy
        constructor
        · intro _hmem
          rfl
        · intro _hstate
          apply hball
          change dist ((x, y) : PlanePoint) (x, interfaceY) < δ
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt]
          constructor
          · simpa using hδ
          · rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hy.1, hy.2]
      · intro y hy
        constructor
        · intro _hmem
          rfl
        · intro _hstate
          apply hball
          change dist ((x, y) : PlanePoint) (x, interfaceY) < δ
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt]
          constructor
          · simpa using hδ
          · rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hy.1, hy.2]
    · have hnhds : carrierᶜ ∈ 𝓝 ((x, interfaceY) : PlanePoint) :=
        mem_interior_iff_mem_nhds.mp hpComplement
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      refine ⟨δ, hδ, .vacant, .vacant, ?_, ?_, by simp [hp]⟩
      · intro y hy
        constructor
        · intro hmem
          exfalso
          exact (hball (by
            change dist ((x, y) : PlanePoint) (x, interfaceY) < δ
            rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt]
            constructor
            · simpa using hδ
            · rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2])) hmem
        · intro hstate
          cases hstate
      · intro y hy
        constructor
        · intro hmem
          exfalso
          exact (hball (by
            change dist ((x, y) : PlanePoint) (x, interfaceY) < δ
            rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt]
            constructor
            · simpa using hδ
            · rw [Real.dist_eq, abs_lt]
              constructor <;> linarith [hy.1, hy.2])) hmem
        · intro hstate
          cases hstate

/-- A two-sided occupied slit is a literal frontier point whose punctured
vertical neighborhood is occupied on both sides. -/
def HasTwoSidedOccupiedSlitAt
    (carrier : Set PlanePoint) (interfaceY x : ℝ) : Prop :=
  ((x, interfaceY) : PlanePoint) ∈ frontier carrier ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∀ y : ℝ, 0 < dist y interfaceY → dist y interfaceY < ε →
        (x, y) ∈ carrier

/-- Contact-free source regularity rules out the deleted-interface slit:
frontier status forces the two locally constant occupancy states to differ. -/
theorem InterfaceClosureContactInventory.no_twoSidedOccupiedSlit
    {carrier : Set PlanePoint} {interfaceY : ℝ}
    (C : InterfaceClosureContactInventory carrier interfaceY)
    (hregular :
      HasInterfaceRegularityAway carrier interfaceY C.contactSet)
    {x : ℝ} (hx : ((x, interfaceY) : PlanePoint) ∉ C.contactSet) :
    ¬ HasTwoSidedOccupiedSlitAt carrier interfaceY x := by
  rintro ⟨hp, ε, hε, hslit⟩
  obtain ⟨δ, hδ, below, above, hbelow, habove, hfrontier⟩ :=
    C.contactFree_accounting hregular hx
  let t := min δ ε / 2
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have htδ : t < δ := by
    dsimp only [t]
    have hmin := min_le_left δ ε
    linarith
  have htε : t < ε := by
    dsimp only [t]
    have hmin := min_le_right δ ε
    linarith
  have hbelowMem : (x, interfaceY - t) ∈ carrier := by
    apply hslit
    · simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos ht]
      exact ht
    · simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos ht]
        using htε
  have haboveMem : (x, interfaceY + t) ∈ carrier := by
    apply hslit
    · simp only [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht]
      exact ht
    · simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht]
        using htε
  have hbelowState : below = .occupied :=
    (hbelow (interfaceY - t) (by constructor <;> linarith)).mp hbelowMem
  have haboveState : above = .occupied :=
    (habove (interfaceY + t) (by constructor <;> linarith)).mp haboveMem
  exact (hfrontier.mp hp) (hbelowState.trans haboveState.symm)

/-- Interval form: every abscissa in a contact-free open interval has the
local accounting contract, with no endpoint order or segment list inferred. -/
theorem InterfaceClosureContactInventory.contactFree_accounting_on_Ioo
    {carrier : Set PlanePoint} {interfaceY : ℝ}
    (C : InterfaceClosureContactInventory carrier interfaceY)
    (hregular :
      HasInterfaceRegularityAway carrier interfaceY C.contactSet)
    {a b : ℝ}
    (hfree : ∀ x ∈ Ioo a b,
      ((x, interfaceY) : PlanePoint) ∉ C.contactSet) :
    ∀ x ∈ Ioo a b, HasLocalOccupancyAccounting carrier interfaceY x := by
  intro x hx
  exact C.contactFree_accounting hregular (hfree x hx)

/-- Upper-interface specialization: the retained two-strip-arc inventory and
the actual upper exterior component produce the four closure contacts on the
same carrier.  No interface order is assumed. -/
theorem upperInterfaceClosureContactInventory_of_twoSidedExterior
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) K)
    (ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) K)
    (ASlab : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    Nonempty (InterfaceClosureContactInventory carrier upperY) := by
  obtain ⟨qLow, hqLowCarrier, hqLowHeight⟩ :=
    exists_carrier_snd_lt_of_frontier_snd_lt pLower.2.1
      (pLower.2.2.trans hlowerUpper)
  have hreachUpper : ∃ q ∈ carrier, q.2 ≤ upperY :=
    ⟨qLow, hqLowCarrier, hqLowHeight.le⟩
  have hK : K ≠ 0 :=
    commonCurvature_ne_zero_of_bounded_upperExterior
      AUpper hcarrierBounded pUpper
  have hslab := strictSlab_twoArcInventory_of_twoSidedExterior
    AUpper ALower ASlab hcarrierOpen hcarrierBounded hcarrierConnected
      hsections hlowerUpper pUpper pLower
  rcases hslab with ⟨firstBase, secondBase, _hbaseHeight, _hbaseOrder,
    _hradius, _hspan, _hne, _hevery, _hcomplete,
    hfirstClosure, hsecondClosure, _hfirstArc, _hsecondArc⟩
  rcases hfirstClosure with
    ⟨firstLower, firstUpper, _hfirstLowerEq, hfirstUpperEq,
      _hfirstLowerActual, hfirstUpperActual,
      _hfirstLowerHeight, hfirstUpperHeight⟩
  rcases hsecondClosure with
    ⟨secondLower, secondUpper, _hsecondLowerEq, hsecondUpperEq,
      _hsecondLowerActual, hsecondUpperActual,
      _hsecondLowerHeight, hsecondUpperHeight⟩
  have hexterior := upperExterior_interfaceContacts_of_global_reach
    AUpper hcarrierOpen hcarrierBounded hcarrierConnected hsections
      hreachUpper pUpper
  let exteriorLeft :=
    leftCirclePointAtHeight (AUpper.supportingCenterAt pUpper) |1 / K| upperY
  let exteriorRight :=
    rightCirclePointAtHeight (AUpper.supportingCenterAt pUpper) |1 / K| upperY
  refine ⟨{
    exteriorComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) pUpper.1
    stripFirstComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) firstBase.1
    stripSecondComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) secondBase.1
    exteriorLeft := exteriorLeft
    exteriorRight := exteriorRight
    stripFirst := firstUpper
    stripSecond := secondUpper
    exteriorLeft_mem_closure := by simpa only [exteriorLeft] using hexterior.1.1
    exteriorRight_mem_closure := by simpa only [exteriorRight] using hexterior.1.2
    stripFirst_interface_singleton := hfirstUpperEq
    stripSecond_interface_singleton := hsecondUpperEq
    exteriorLeft_mem_frontier := by simpa only [exteriorLeft] using hexterior.2.1
    exteriorRight_mem_frontier := by simpa only [exteriorRight] using hexterior.2.2
    stripFirst_mem_frontier := hfirstUpperActual.1
    stripSecond_mem_frontier := hsecondUpperActual.1
    exteriorLeft_height := rfl
    exteriorRight_height := rfl
    stripFirst_height := hfirstUpperHeight
    stripSecond_height := hsecondUpperHeight }⟩

/-- Lower-interface counterpart, using the same strict-slab inventory and the
actual lower exterior continuation component. -/
theorem lowerInterfaceClosureContactInventory_of_twoSidedExterior
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) K)
    (ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) K)
    (ASlab : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    Nonempty (InterfaceClosureContactInventory carrier lowerY) := by
  obtain ⟨qHigh, hqHighCarrier, hqHighHeight⟩ :=
    exists_carrier_snd_gt_of_frontier_snd_gt pUpper.2.1
      (hlowerUpper.trans pUpper.2.2)
  have hreachLower : ∃ q ∈ carrier, lowerY ≤ q.2 :=
    ⟨qHigh, hqHighCarrier, hqHighHeight.le⟩
  have hK : K ≠ 0 :=
    commonCurvature_ne_zero_of_bounded_lowerExterior
      ALower hcarrierBounded pLower
  have hslab := strictSlab_twoArcInventory_of_twoSidedExterior
    AUpper ALower ASlab hcarrierOpen hcarrierBounded hcarrierConnected
      hsections hlowerUpper pUpper pLower
  rcases hslab with ⟨firstBase, secondBase, _hbaseHeight, _hbaseOrder,
    _hradius, _hspan, _hne, _hevery, _hcomplete,
    hfirstClosure, hsecondClosure, _hfirstArc, _hsecondArc⟩
  rcases hfirstClosure with
    ⟨firstLower, firstUpper, hfirstLowerEq, _hfirstUpperEq,
      hfirstLowerActual, _hfirstUpperActual,
      hfirstLowerHeight, _hfirstUpperHeight⟩
  rcases hsecondClosure with
    ⟨secondLower, secondUpper, hsecondLowerEq, _hsecondUpperEq,
      hsecondLowerActual, _hsecondUpperActual,
      hsecondLowerHeight, _hsecondUpperHeight⟩
  have hexterior := lowerExterior_interfaceContacts_of_global_reach
    ALower hcarrierOpen hcarrierBounded hcarrierConnected hsections
      hreachLower pLower
  let exteriorLeft :=
    leftCirclePointAtHeight (ALower.supportingCenterAt pLower) |1 / K| lowerY
  let exteriorRight :=
    rightCirclePointAtHeight (ALower.supportingCenterAt pLower) |1 / K| lowerY
  refine ⟨{
    exteriorComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) pLower.1
    stripFirstComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) firstBase.1
    stripSecondComponent := connectedComponentIn
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) secondBase.1
    exteriorLeft := exteriorLeft
    exteriorRight := exteriorRight
    stripFirst := firstLower
    stripSecond := secondLower
    exteriorLeft_mem_closure := by simpa only [exteriorLeft] using hexterior.1.1
    exteriorRight_mem_closure := by simpa only [exteriorRight] using hexterior.1.2
    stripFirst_interface_singleton := hfirstLowerEq
    stripSecond_interface_singleton := hsecondLowerEq
    exteriorLeft_mem_frontier := by simpa only [exteriorLeft] using hexterior.2.1
    exteriorRight_mem_frontier := by simpa only [exteriorRight] using hexterior.2.2
    stripFirst_mem_frontier := hfirstLowerActual.1
    stripSecond_mem_frontier := hsecondLowerActual.1
    exteriorLeft_height := rfl
    exteriorRight_height := rfl
    stripFirst_height := hfirstLowerHeight
    stripSecond_height := hsecondLowerHeight }⟩

/-- Both density interfaces are accounted for on one unchanged representative.
The result collects contacts only; it does not select a CMV branch or impose
any order among coincident or distinct contacts. -/
theorem interfaceClosureContactInventories_of_twoSidedExterior
    {carrier : Set PlanePoint} {K lowerY upperY : ℝ}
    (AUpper : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | upperY < q.2}) K)
    (ALower : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint | q.2 < lowerY}) K)
    (ASlab : BranchNeutralMixedGraphAtlas carrier
      (frontier carrier ∩ {q : PlanePoint |
        lowerY < q.2 ∧ q.2 < upperY}) K)
    (hcarrierOpen : IsOpen carrier)
    (hcarrierBounded : Bornology.IsBounded carrier)
    (hcarrierConnected : IsConnected carrier)
    (hsections : ∀ y : ℝ, (horizontalSection carrier y).OrdConnected)
    (hlowerUpper : lowerY < upperY)
    (pUpper : (frontier carrier ∩
      {q : PlanePoint | upperY < q.2} : Set PlanePoint))
    (pLower : (frontier carrier ∩
      {q : PlanePoint | q.2 < lowerY} : Set PlanePoint)) :
    Nonempty (InterfaceClosureContactInventory carrier upperY) ∧
      Nonempty (InterfaceClosureContactInventory carrier lowerY) := by
  exact ⟨upperInterfaceClosureContactInventory_of_twoSidedExterior
      AUpper ALower ASlab hcarrierOpen hcarrierBounded hcarrierConnected
        hsections hlowerUpper pUpper pLower,
    lowerInterfaceClosureContactInventory_of_twoSidedExterior
      AUpper ALower ASlab hcarrierOpen hcarrierBounded hcarrierConnected
        hsections hlowerUpper pUpper pLower⟩

end InterfaceAccounting

/-! ## Literal complete-arc applications

The existing exact cap parameterization is exercised on minor, major, reflected,
and horizontally translated caps.  These are complete closed images, including
both contacts and the pole; they are not finite samples of an arc.
-/

namespace CapApplications

/-- A literal upper minor cap. -/
def minor : OneSidedCircularCap where
  chord := 2
  theta := Real.pi / 3
  midpointX := 0
  baseY := 1
  side := .upper
  chord_pos := by norm_num
  theta_pos := div_pos Real.pi_pos (by norm_num)
  theta_lt_pi := by nlinarith [Real.pi_pos]

/-- A literal upper major cap. -/
def major : OneSidedCircularCap where
  chord := 2
  theta := 2 * Real.pi / 3
  midpointX := 0
  baseY := 1
  side := .upper
  chord_pos := by norm_num
  theta_pos := by positivity
  theta_lt_pi := by nlinarith [Real.pi_pos]

/-- The major cap reflected to the lower interface. -/
def reflectedMajor : OneSidedCircularCap :=
  { major with side := .lower, baseY := -1 }

/-- A genuinely translated minor cap. -/
def translatedMinor : OneSidedCircularCap :=
  { minor with midpointX := 7 }

/-- All four branch tests use the exact complete parameter image. -/
theorem complete_images :
    capParam minor '' Icc (capStart minor) (capEnd minor) = minor.arcTrace ∧
      capParam major '' Icc (capStart major) (capEnd major) = major.arcTrace ∧
      capParam reflectedMajor ''
          Icc (capStart reflectedMajor) (capEnd reflectedMajor) =
        reflectedMajor.arcTrace ∧
      capParam translatedMinor ''
          Icc (capStart translatedMinor) (capEnd translatedMinor) =
        translatedMinor.arcTrace :=
  ⟨capParam_image_Icc_eq_arcTrace minor,
    capParam_image_Icc_eq_arcTrace major,
    capParam_image_Icc_eq_arcTrace reflectedMajor,
    capParam_image_Icc_eq_arcTrace translatedMinor⟩
private theorem zero_mem_capInterval (c : OneSidedCircularCap) :
    0 ∈ Icc (capStart c) (capEnd c) := by
  constructor <;> dsimp [capStart, capEnd] <;>
    nlinarith [c.radius_pos, c.theta_pos]


/-- The parameter midpoint supplies the actual upper pole in both the minor and
major branches, and the lower pole after reflection. -/
theorem poles_continue_in_complete_images :
    capParam minor 0 ∈ minor.arcTrace ∧
      capParam major 0 ∈ major.arcTrace ∧
      capParam reflectedMajor 0 ∈ reflectedMajor.arcTrace ∧
      capParam translatedMinor 0 ∈ translatedMinor.arcTrace := by
  constructor
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨0, zero_mem_capInterval minor, rfl⟩
  constructor
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨0, zero_mem_capInterval major, rfl⟩
  constructor
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨0, zero_mem_capInterval reflectedMajor, rfl⟩
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨0, zero_mem_capInterval translatedMinor, rfl⟩

/-- A preconnected set is its own relative connected component at every point
it contains. -/
theorem connectedComponentIn_eq_self_of_isPreconnected
    {S : Set PlanePoint} {p : PlanePoint} (hp : p ∈ S)
    (hpreconnected : IsPreconnected S) :
    connectedComponentIn S p = S := by
  rw [connectedComponentIn_eq_image hp]
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace hpreconnected
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  simp only [Set.image_univ, Subtype.range_coe]

/-- The complete literal arc trace of every one-sided cap is preconnected. -/
theorem arcTrace_isPreconnected (c : OneSidedCircularCap) :
    IsPreconnected c.arcTrace := by
  rw [← capParam_image_Icc_eq_arcTrace]
  apply (convex_Icc (capStart c) (capEnd c)).isPreconnected.image
  unfold capParam OneSidedCircularCap.arcPoint
  cases c.side <;> fun_prop

/-- The complete cap image is exactly one connected component, not merely a
connected subset of one. -/
theorem cap_connectedComponentIn_eq_arcTrace (c : OneSidedCircularCap) :
    connectedComponentIn c.arcTrace (capParam c 0) = c.arcTrace := by
  apply connectedComponentIn_eq_self_of_isPreconnected
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨0, zero_mem_capInterval c, rfl⟩
  · exact arcTrace_isPreconnected c


/-- Open bounded Euclidean disk whose exterior frontier clip realizes a
literal one-sided cap. -/
def capOpenRepresentative (c : OneSidedCircularCap) : Set PlanePoint :=
  planeEuclideanHomeomorph ⁻¹'
    Metric.ball (planeEuclideanHomeomorph c.center) c.radius

theorem capOpenRepresentative_isOpen (c : OneSidedCircularCap) :
    IsOpen (capOpenRepresentative c) :=
  Metric.isOpen_ball.preimage planeEuclideanHomeomorph.continuous

theorem capOpenRepresentative_isBounded (c : OneSidedCircularCap) :
    Bornology.IsBounded (capOpenRepresentative c) := by
  have hcompact : IsCompact
      (planeEuclideanHomeomorph ⁻¹'
        Metric.closedBall (planeEuclideanHomeomorph c.center) c.radius) :=
    planeEuclideanHomeomorph.isCompact_preimage.mpr
      (isCompact_closedBall _ _)
  apply hcompact.isBounded.subset
  intro q hq
  exact Metric.ball_subset_closedBall hq

theorem frontier_capOpenRepresentative (c : OneSidedCircularCap) :
    frontier (capOpenRepresentative c) =
      {q : PlanePoint | circleValue c.center c.radius q = 0} := by
  rw [capOpenRepresentative, ← planeEuclideanHomeomorph.preimage_frontier,
    frontier_ball (planeEuclideanHomeomorph c.center) c.radius_pos.ne']
  ext q
  rw [Set.mem_preimage, Metric.mem_sphere]
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change Real.sqrt
      (dist q.1 c.center.1 ^ 2 + dist q.2 c.center.2 ^ 2) = c.radius ↔ _
  rw [Real.dist_eq, Real.dist_eq]
  constructor
  · intro hdist
    have hsq := congrArg (fun x : ℝ => x ^ 2) hdist
    rw [Real.sq_sqrt (by positivity)] at hsq
    change circleValue c.center c.radius q = 0
    unfold circleValue
    nlinarith [sq_abs (q.1 - c.center.1), sq_abs (q.2 - c.center.2)]
  · intro hcircle
    change circleValue c.center c.radius q = 0 at hcircle
    unfold circleValue at hcircle
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) c.radius_pos.le).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs (q.1 - c.center.1), sq_abs (q.2 - c.center.2)]

/-! ### Actual mixed-coordinate disk charts

The following smooth clipping is used only to extend a local square-root
circle graph to a globally `C²` function, as required by `GraphPatch`.  On the
selected chart interval it is exactly the ordinary coordinate square.
-/

def diskChartSafeSquare (center start stop t : ℝ) : ℝ :=
  (t - center) ^ 2 *
    (1 - Real.smoothTransition
      (((t - center) ^ 2 - start) / (stop - start)))

theorem diskChartSafeSquare_eq_sq
    {center start stop t : ℝ} (hstartstop : start < stop)
    (ht : (t - center) ^ 2 ≤ start) :
    diskChartSafeSquare center start stop t = (t - center) ^ 2 := by
  have harg :
      ((t - center) ^ 2 - start) / (stop - start) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
      (sub_pos.mpr hstartstop).le
  rw [diskChartSafeSquare, Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem diskChartSafeSquare_mem_Icc
    {center start stop : ℝ} (hstart : 0 ≤ start)
    (hstartstop : start < stop) (t : ℝ) :
    diskChartSafeSquare center start stop t ∈ Icc (0 : ℝ) stop := by
  have hχ0 : 0 ≤ Real.smoothTransition
      (((t - center) ^ 2 - start) / (stop - start)) :=
    Real.smoothTransition.nonneg _
  have hχ1 : Real.smoothTransition
      (((t - center) ^ 2 - start) / (stop - start)) ≤ 1 :=
    Real.smoothTransition.le_one _
  by_cases ht : (t - center) ^ 2 ≤ stop
  · constructor
    · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hχ1)
    · calc
        diskChartSafeSquare center start stop t ≤ (t - center) ^ 2 * 1 := by
          unfold diskChartSafeSquare
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ ≤ stop := by simpa using ht
  · have harg : 1 ≤
        ((t - center) ^ 2 - start) / (stop - start) := by
      rw [le_div_iff₀ (sub_pos.mpr hstartstop)]
      simp only [not_le] at ht
      linarith
    rw [diskChartSafeSquare, Real.smoothTransition.one_of_one_le harg]
    constructor
    · positivity
    · have hstopPos : 0 < stop := hstart.trans_lt hstartstop
      simp only [sub_self, mul_zero]
      exact hstopPos.le

theorem contDiff_diskChartSafeSquare (center start stop : ℝ) :
    ContDiff ℝ ∞ (diskChartSafeSquare center start stop) := by
  unfold diskChartSafeSquare
  have harg : ContDiff ℝ ∞ (fun t : ℝ =>
      ((t - center) ^ 2 - start) / (stop - start)) :=
    (((contDiff_id.sub contDiff_const).pow 2).sub contDiff_const).div_const _
  exact ((contDiff_id.sub contDiff_const).pow 2).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp harg))

def diskChartRoot (center radius start stop t : ℝ) : ℝ :=
  √(radius ^ 2 - diskChartSafeSquare center start stop t)

theorem diskChartRoot_pos
    {center radius start stop : ℝ} (_hradius : 0 < radius)
    (hstart : 0 ≤ start) (hstartstop : start < stop)
    (hstop : stop < radius ^ 2) (t : ℝ) :
    0 < diskChartRoot center radius start stop t := by
  apply Real.sqrt_pos.2
  have hsafe :=
    (diskChartSafeSquare_mem_Icc (center := center) hstart hstartstop t).2
  linarith

theorem diskChartRoot_sq
    {center radius start stop : ℝ} (_hradius : 0 < radius)
    (hstart : 0 ≤ start) (hstartstop : start < stop)
    (hstop : stop < radius ^ 2) (t : ℝ) :
    diskChartRoot center radius start stop t ^ 2 =
      radius ^ 2 - diskChartSafeSquare center start stop t := by
  exact Real.sq_sqrt (le_of_lt
    (sub_pos.mpr ((diskChartSafeSquare_mem_Icc hstart hstartstop t).2.trans_lt
      hstop)))

theorem contDiff_diskChartRoot
    {center radius start stop : ℝ} (_hradius : 0 < radius)
    (hstart : 0 ≤ start) (hstartstop : start < stop)
    (hstop : stop < radius ^ 2) :
    ContDiff ℝ ∞ (diskChartRoot center radius start stop) := by
  unfold diskChartRoot
  apply (contDiff_const.sub
    (contDiff_diskChartSafeSquare center start stop)).sqrt
  intro t
  exact (sub_pos.mpr
    ((diskChartSafeSquare_mem_Icc hstart hstartstop t).2.trans_lt hstop)).ne'

theorem diskChartRoot_sq_eq_actual
    {center radius start stop t : ℝ} (hradius : 0 < radius)
    (hstart : 0 ≤ start) (hstartstop : start < stop)
    (hstop : stop < radius ^ 2) (ht : (t - center) ^ 2 ≤ start) :
    diskChartRoot center radius start stop t ^ 2 =
      radius ^ 2 - (t - center) ^ 2 := by
  rw [diskChartRoot_sq hradius hstart hstartstop hstop,
    diskChartSafeSquare_eq_sq hstartstop ht]
/-- A `C²` graph on the positive coordinate branch of a positive-radius
circle has curvature `-1 / radius`.  The proof differentiates the literal
circle equation twice, so it is independent of the chosen smooth extension
outside the chart interval. -/
theorem graphCurvature_eq_neg_inv_of_positive_circle
    {f : ℝ → ℝ} {a b centerCoord centerGraph radius x : ℝ}
    (hf : ContDiff ℝ 2 f) (hradius : 0 < radius)
    (hcircle : ∀ t ∈ Ioo a b,
      (t - centerCoord) ^ 2 + (f t - centerGraph) ^ 2 = radius ^ 2)
    (hpositive : ∀ t ∈ Ioo a b, 0 < f t - centerGraph)
    (hx : x ∈ Ioo a b) :
    deriv (deriv f) x / √(1 + deriv f x ^ 2) ^ 3 = -(1 / radius) := by
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp hf).2.2
  have hfirst : ∀ t ∈ Ioo a b,
      (t - centerCoord) +
        (f t - centerGraph) * deriv f t = 0 := by
    intro t ht
    have hlocal :
        (fun z : ℝ =>
          (z - centerCoord) ^ 2 + (f z - centerGraph) ^ 2) =ᶠ[𝓝 t]
          (fun _ : ℝ => radius ^ 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with z hz
      exact hcircle z hz
    have hfAt : HasDerivAt f (deriv f t) t :=
      (hf.differentiable (by norm_num) t).hasDerivAt
    have hraw := (((hasDerivAt_id t).sub_const centerCoord).pow 2).add
      ((hfAt.sub_const centerGraph).pow 2)
    have hderiv :
        deriv
          (fun z : ℝ =>
            (z - centerCoord) ^ 2 + (f z - centerGraph) ^ 2) t =
          2 * (t - centerCoord) +
            2 * (f t - centerGraph) * deriv f t := by
      have hfun :
          (fun z : ℝ =>
            (z - centerCoord) ^ 2 + (f z - centerGraph) ^ 2) =
            ((fun z : ℝ => id z - centerCoord) ^ 2) +
              ((fun z : ℝ => f z - centerGraph) ^ 2) := by
        funext z
        rfl
      rw [hfun, hraw.deriv]
      dsimp only [id]
      ring
    have hzero : deriv
        (fun z : ℝ =>
          (z - centerCoord) ^ 2 + (f z - centerGraph) ^ 2) t = 0 := by
      rw [hlocal.deriv_eq, deriv_const]
    rw [hderiv] at hzero
    linarith
  have hsecond :
      1 + deriv f x ^ 2 +
        (f x - centerGraph) * deriv (deriv f) x = 0 := by
    have hlocal :
        (fun t : ℝ =>
          (t - centerCoord) +
            (f t - centerGraph) * deriv f t) =ᶠ[𝓝 x]
          (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      exact hfirst t ht
    have hfAt : HasDerivAt f (deriv f x) x :=
      (hf.differentiable (by norm_num) x).hasDerivAt
    have hf'At : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
      (hf'.differentiable (by norm_num) x).hasDerivAt
    have hraw := ((hasDerivAt_id x).sub_const centerCoord).add
      ((hfAt.sub_const centerGraph).mul hf'At)
    have hderiv :
        deriv
          (fun t : ℝ =>
            (t - centerCoord) +
              (f t - centerGraph) * deriv f t) x =
          1 + (deriv f x * deriv f x +
            (f x - centerGraph) * deriv (deriv f) x) := by
      have hfun :
          (fun t : ℝ =>
            (t - centerCoord) +
              (f t - centerGraph) * deriv f t) =
            (fun t : ℝ => id t - centerCoord) +
              (fun t : ℝ => f t - centerGraph) * deriv f := by
        funext t
        rfl
      rw [hfun, hraw.deriv]
    have hzero : deriv
        (fun t : ℝ =>
          (t - centerCoord) +
            (f t - centerGraph) * deriv f t) x = 0 := by
      rw [hlocal.deriv_eq, deriv_const]
    rw [hderiv] at hzero
    nlinarith
  have hy : 0 < f x - centerGraph := hpositive x hx
  have hcircleX := hcircle x hx
  have hfirstX := hfirst x hx
  have hfirstSq := congrArg (fun z : ℝ => z ^ 2) hfirstX
  have hnorm :
      (1 + deriv f x ^ 2) * (f x - centerGraph) ^ 2 = radius ^ 2 := by
    nlinarith
  have hspeedSq :
      √(1 + deriv f x ^ 2) ^ 2 =
        (radius / (f x - centerGraph)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp [hy.ne']
    exact hnorm
  have hspeed :
      √(1 + deriv f x ^ 2) =
        radius / (f x - centerGraph) := by
    exact (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg hradius.le hy.le)).mp hspeedSq
  rw [hspeed]
  have hsecondMul := congrArg
    (fun z : ℝ => z * (f x - centerGraph) ^ 2) hsecond
  field_simp [hradius.ne', hy.ne']
  nlinarith [hsecondMul, hnorm]

/-- Negative-coordinate counterpart of
`graphCurvature_eq_neg_inv_of_positive_circle`. -/
theorem graphCurvature_eq_inv_of_negative_circle
    {f : ℝ → ℝ} {a b centerCoord centerGraph radius x : ℝ}
    (hf : ContDiff ℝ 2 f) (hradius : 0 < radius)
    (hcircle : ∀ t ∈ Ioo a b,
      (t - centerCoord) ^ 2 + (f t - centerGraph) ^ 2 = radius ^ 2)
    (hnegative : ∀ t ∈ Ioo a b, f t - centerGraph < 0)
    (hx : x ∈ Ioo a b) :
    deriv (deriv f) x / √(1 + deriv f x ^ 2) ^ 3 = 1 / radius := by
  let g : ℝ → ℝ := fun t => 2 * centerGraph - f t
  have hg : ContDiff ℝ 2 g := contDiff_const.sub hf
  have hcircleG : ∀ t ∈ Ioo a b,
      (t - centerCoord) ^ 2 + (g t - centerGraph) ^ 2 = radius ^ 2 := by
    intro t ht
    dsimp only [g]
    nlinarith [hcircle t ht]
  have hpositiveG : ∀ t ∈ Ioo a b, 0 < g t - centerGraph := by
    intro t ht
    dsimp only [g]
    linarith [hnegative t ht]
  have hcurvG := graphCurvature_eq_neg_inv_of_positive_circle
    hg hradius hcircleG hpositiveG hx
  have hderivG : deriv g x = -deriv f x := by
    change deriv (fun t => 2 * centerGraph - f t) x = -deriv f x
    exact (((hasDerivAt_const x (2 * centerGraph)).sub
      ((hf.differentiable (by simp) x).hasDerivAt)).deriv).trans (by ring)
  have hderivDerivG :
      deriv (deriv g) x = -deriv (deriv f) x := by
    have hderivLocal :
        deriv g =ᶠ[𝓝 x] fun t => -deriv f t := by
      filter_upwards [] with t
      change deriv (fun z => 2 * centerGraph - f z) t = -deriv f t
      exact (((hasDerivAt_const t (2 * centerGraph)).sub
        ((hf.differentiable (by simp) t).hasDerivAt)).deriv).trans (by ring)
    rw [hderivLocal.deriv_eq]
    have hf' : ContDiff ℝ 1 (deriv f) :=
      (contDiff_succ_iff_deriv.mp hf).2.2
    exact ((hf'.differentiable (by norm_num) x).hasDerivAt.neg).deriv
  rw [hderivG, hderivDerivG, neg_sq] at hcurvG
  calc
    deriv (deriv f) x / √(1 + deriv f x ^ 2) ^ 3 =
        -(-deriv (deriv f) x / √(1 + deriv f x ^ 2) ^ 3) := by ring
    _ = -(-(1 / radius)) := by rw [hcurvG]
    _ = 1 / radius := by ring

theorem mem_capOpenRepresentative_iff_circleValue_neg
    (c : OneSidedCircularCap) (q : PlanePoint) :
    q ∈ capOpenRepresentative c ↔ circleValue c.center c.radius q < 0 := by
  rw [capOpenRepresentative, Set.mem_preimage, Metric.mem_ball,
    planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change √(dist q.1 c.center.1 ^ 2 + dist q.2 c.center.2 ^ 2) < c.radius ↔ _
  rw [Real.sqrt_lt' c.radius_pos, Real.dist_eq, Real.dist_eq,
    sq_abs, sq_abs]
  unfold circleValue
  constructor <;> intro h <;> linarith

def upperDiskVerticalStart (c : OneSidedCircularCap) : ℝ :=
  c.radius ^ 2 / 4

def upperDiskVerticalStop (c : OneSidedCircularCap) : ℝ :=
  c.radius ^ 2 / 2

def upperDiskVerticalGraph (c : OneSidedCircularCap) (x : ℝ) : ℝ :=
  c.center.2 +
    diskChartRoot c.center.1 c.radius
      (upperDiskVerticalStart c) (upperDiskVerticalStop c) x

private theorem upperDiskVertical_parameters
    (c : OneSidedCircularCap) :
    0 ≤ upperDiskVerticalStart c ∧
      upperDiskVerticalStart c < upperDiskVerticalStop c ∧
      upperDiskVerticalStop c < c.radius ^ 2 := by
  have hr : 0 < c.radius ^ 2 := sq_pos_of_pos c.radius_pos
  unfold upperDiskVerticalStart upperDiskVerticalStop
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

private theorem upperDiskVertical_offset_sq
    (c : OneSidedCircularCap) {x : ℝ}
    (hx : x ∈ Icc (c.center.1 - c.radius / 2)
      (c.center.1 + c.radius / 2)) :
    (x - c.center.1) ^ 2 ≤ upperDiskVerticalStart c := by
  have hproduct : 0 ≤
      (x - (c.center.1 - c.radius / 2)) *
        ((c.center.1 + c.radius / 2) - x) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  unfold upperDiskVerticalStart
  nlinarith

private theorem upperDiskVerticalGraph_circle
    (c : OneSidedCircularCap) {x : ℝ}
    (hx : x ∈ Icc (c.center.1 - c.radius / 2)
      (c.center.1 + c.radius / 2)) :
    (x - c.center.1) ^ 2 +
        (upperDiskVerticalGraph c x - c.center.2) ^ 2 =
      c.radius ^ 2 := by
  rcases upperDiskVertical_parameters c with ⟨hstart, hstartstop, hstop⟩
  unfold upperDiskVerticalGraph
  rw [show c.center.2 +
      diskChartRoot c.center.1 c.radius
        (upperDiskVerticalStart c) (upperDiskVerticalStop c) x -
      c.center.2 =
        diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x by ring]
  rw [diskChartRoot_sq_eq_actual c.radius_pos hstart hstartstop hstop
    (upperDiskVertical_offset_sq c hx)]
  ring

private theorem upperDiskVerticalGraph_above_one
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    {x : ℝ} (hx : x ∈ Icc (c.center.1 - c.radius / 2)
      (c.center.1 + c.radius / 2)) :
    1 < upperDiskVerticalGraph c x := by
  rcases upperDiskVertical_parameters c with ⟨hstart, hstartstop, hstop⟩
  have hroot := diskChartRoot_pos (center := c.center.1)
    c.radius_pos hstart hstartstop hstop x
  have hrootSq := diskChartRoot_sq_eq_actual c.radius_pos hstart
    hstartstop hstop (upperDiskVertical_offset_sq c hx)
  have hrSq : 0 < c.radius ^ 2 := sq_pos_of_pos c.radius_pos
  have hrootHalf :
      c.radius / 2 <
        diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x := by
    by_contra hnot
    have hoffset :
        (x - c.center.1) ^ 2 ≤ c.radius ^ 2 / 4 := by
      simpa [upperDiskVerticalStart] using
        (upperDiskVertical_offset_sq c hx)
    have hprod : 0 ≤
        (c.radius / 2 -
          diskChartRoot c.center.1 c.radius
            (upperDiskVerticalStart c) (upperDiskVerticalStop c) x) *
        (c.radius / 2 +
          diskChartRoot c.center.1 c.radius
            (upperDiskVerticalStart c) (upperDiskVerticalStop c) x) :=
      mul_nonneg (by linarith) (by linarith [c.radius_pos])
    nlinarith
  have hcenterY :
      c.center.2 = 1 - c.radius * Real.cos c.theta := by
    simp [OneSidedCircularCap.center, hside, hbase]
  rw [show upperDiskVerticalGraph c x =
      c.center.2 +
        diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x by rfl,
    hcenterY]
  nlinarith [mul_le_mul_of_nonneg_left hcos c.radius_pos.le]

private theorem upperDiskVerticalGraph_le_top
    (c : OneSidedCircularCap) (x : ℝ) :
    upperDiskVerticalGraph c x ≤ c.center.2 + c.radius := by
  rcases upperDiskVertical_parameters c with ⟨hstart, hstartstop, hstop⟩
  have hsafe :=
    (diskChartSafeSquare_mem_Icc (center := c.center.1)
      hstart hstartstop x).1
  have hroot := diskChartRoot_pos (center := c.center.1)
    c.radius_pos hstart hstartstop hstop x
  have hrootSq := diskChartRoot_sq (center := c.center.1)
    c.radius_pos hstart hstartstop hstop x
  rw [show upperDiskVerticalGraph c x =
      c.center.2 +
        diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x by rfl]
  by_contra hnot
  have hprod : 0 <
      (diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x -
        c.radius) *
      (diskChartRoot c.center.1 c.radius
          (upperDiskVerticalStart c) (upperDiskVerticalStop c) x +
        c.radius) :=
    mul_pos (by linarith) (by linarith [c.radius_pos])
  nlinarith

def upperDiskVerticalPatch
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    GraphPatch where
  a := c.center.1 - c.radius / 2
  b := c.center.1 + c.radius / 2
  base := 1
  graph := upperDiskVerticalGraph c
  lowerBound := 1
  upperBound := c.center.2 + c.radius
  zone := .exterior
  side := .below
  a_lt_b := by linarith [c.radius_pos]
  graph_contDiff := by
    have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      apply WithTop.coe_le_coe.mpr
      exact le_top
    exact (contDiff_const.add
      (contDiff_diskChartRoot c.radius_pos
        (upperDiskVertical_parameters c).1
        (upperDiskVertical_parameters c).2.1
        (upperDiskVertical_parameters c).2.2)).of_le hle
  base_order_graph := by
    intro x hx
    exact upperDiskVerticalGraph_above_one c hbase hside hcos
      ⟨hx.1.le, hx.2⟩
  lowerBound_le_base := le_rfl
  base_le_upperBound := by
    have hpole := upperDiskVerticalGraph_above_one c hbase hside hcos
      (show c.center.1 ∈ Icc
        (c.center.1 - c.radius / 2) (c.center.1 + c.radius / 2) by
          constructor <;> linarith [c.radius_pos])
    have htop := upperDiskVerticalGraph_le_top c c.center.1
    linarith
  graph_bounds := by
    intro x hx
    exact ⟨(upperDiskVerticalGraph_above_one c hbase hside hcos
      ⟨hx.1.le, hx.2⟩).le, upperDiskVerticalGraph_le_top c x⟩
  carrier_in_zone := by
    intro p hp
    change 1 < |p.2|
    have hpone : 1 < p.2 := hp.2.1
    rw [abs_of_pos (zero_lt_one.trans hpone)]
    exact hpone

def upperDiskHorizontalStart (c : OneSidedCircularCap) : ℝ :=
  49 * c.radius ^ 2 / 64

def upperDiskHorizontalStop (c : OneSidedCircularCap) : ℝ :=
  57 * c.radius ^ 2 / 64

def upperDiskHorizontalRoot (c : OneSidedCircularCap) (y : ℝ) : ℝ :=
  diskChartRoot c.center.2 c.radius
    (upperDiskHorizontalStart c) (upperDiskHorizontalStop c) y

def upperDiskRightGraph (c : OneSidedCircularCap) (y : ℝ) : ℝ :=
  c.center.1 + upperDiskHorizontalRoot c y

def upperDiskLeftGraph (c : OneSidedCircularCap) (y : ℝ) : ℝ :=
  c.center.1 - upperDiskHorizontalRoot c y

private theorem upperDiskHorizontal_parameters
    (c : OneSidedCircularCap) :
    0 ≤ upperDiskHorizontalStart c ∧
      upperDiskHorizontalStart c < upperDiskHorizontalStop c ∧
      upperDiskHorizontalStop c < c.radius ^ 2 := by
  have hr : 0 < c.radius ^ 2 := sq_pos_of_pos c.radius_pos
  unfold upperDiskHorizontalStart upperDiskHorizontalStop
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

private theorem upperDiskHorizontal_offset_sq
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    {y : ℝ} (hy : y ∈ Icc 1 (c.center.2 + 7 * c.radius / 8)) :
    (y - c.center.2) ^ 2 ≤ upperDiskHorizontalStart c := by
  have hcenterY :
      c.center.2 = 1 - c.radius * Real.cos c.theta := by
    simp [OneSidedCircularCap.center, hside, hbase]
  have hcosMul :=
    mul_le_mul_of_nonneg_left hcosLower c.radius_pos.le
  have hleft : c.center.2 - 7 * c.radius / 8 ≤ y := by
    rw [hcenterY]
    nlinarith [hy.1, c.radius_pos]
  have hproduct : 0 ≤
      (y - (c.center.2 - 7 * c.radius / 8)) *
        ((c.center.2 + 7 * c.radius / 8) - y) :=
    mul_nonneg (by linarith) (by linarith [hy.2])
  unfold upperDiskHorizontalStart
  nlinarith

private theorem upperDiskRightGraph_circle
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    {y : ℝ} (hy : y ∈ Icc 1 (c.center.2 + 7 * c.radius / 8)) :
    (upperDiskRightGraph c y - c.center.1) ^ 2 +
        (y - c.center.2) ^ 2 = c.radius ^ 2 := by
  rcases upperDiskHorizontal_parameters c with ⟨hstart, hstartstop, hstop⟩
  unfold upperDiskRightGraph upperDiskHorizontalRoot
  rw [show c.center.1 +
      diskChartRoot c.center.2 c.radius
        (upperDiskHorizontalStart c) (upperDiskHorizontalStop c) y -
      c.center.1 =
        diskChartRoot c.center.2 c.radius
          (upperDiskHorizontalStart c) (upperDiskHorizontalStop c) y by ring]
  rw [diskChartRoot_sq_eq_actual c.radius_pos hstart hstartstop hstop
    (upperDiskHorizontal_offset_sq c hbase hside hcosLower hy)]
  ring

private theorem upperDiskLeftGraph_circle
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    {y : ℝ} (hy : y ∈ Icc 1 (c.center.2 + 7 * c.radius / 8)) :
    (upperDiskLeftGraph c y - c.center.1) ^ 2 +
        (y - c.center.2) ^ 2 = c.radius ^ 2 := by
  rw [show upperDiskLeftGraph c y - c.center.1 =
      -(upperDiskRightGraph c y - c.center.1) by
        simp [upperDiskLeftGraph, upperDiskRightGraph]]
  rw [neg_sq]
  exact upperDiskRightGraph_circle c hbase hside hcosLower hy

private theorem upperDiskHorizontalRoot_pos
    (c : OneSidedCircularCap) (y : ℝ) :
    0 < upperDiskHorizontalRoot c y := by
  rcases upperDiskHorizontal_parameters c with ⟨hstart, hstartstop, hstop⟩
  exact diskChartRoot_pos (center := c.center.2)
    c.radius_pos hstart hstartstop hstop y

private theorem upperDiskHorizontalRoot_le_radius
    (c : OneSidedCircularCap) (y : ℝ) :
    upperDiskHorizontalRoot c y ≤ c.radius := by
  rcases upperDiskHorizontal_parameters c with ⟨hstart, hstartstop, hstop⟩
  have hsafe :=
    (diskChartSafeSquare_mem_Icc (center := c.center.2)
      hstart hstartstop y).1
  have hroot := diskChartRoot_pos (center := c.center.2)
    c.radius_pos hstart hstartstop hstop y
  have hrootSq := diskChartRoot_sq (center := c.center.2)
    c.radius_pos hstart hstartstop hstop y
  unfold upperDiskHorizontalRoot
  by_contra hnot
  have hprod : 0 <
      (diskChartRoot c.center.2 c.radius
          (upperDiskHorizontalStart c) (upperDiskHorizontalStop c) y -
        c.radius) *
      (diskChartRoot c.center.2 c.radius
          (upperDiskHorizontalStart c) (upperDiskHorizontalStop c) y +
        c.radius) :=
    mul_pos (by linarith) (by linarith [c.radius_pos])
  nlinarith

private theorem upperDiskHorizontal_contDiff
    (c : OneSidedCircularCap) :
    ContDiff ℝ 2 (upperDiskHorizontalRoot c) := by
  have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    apply WithTop.coe_le_coe.mpr
    exact le_top
  exact (contDiff_diskChartRoot c.radius_pos
    (upperDiskHorizontal_parameters c).1
    (upperDiskHorizontal_parameters c).2.1
    (upperDiskHorizontal_parameters c).2.2).of_le hle

def upperDiskRightPatch
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    CMVTransverseContactVariation.HorizontalGraphPatch where
  a := 1
  b := c.center.2 + 7 * c.radius / 8
  base := c.center.1
  graph := upperDiskRightGraph c
  lowerBound := c.center.1
  upperBound := c.center.1 + c.radius
  zone := .exterior
  side := .below
  a_lt_b := by
    have hcenterY :
        c.center.2 = 1 - c.radius * Real.cos c.theta := by
      simp [OneSidedCircularCap.center, hside, hbase]
    have hcosMul :=
      mul_le_mul_of_nonneg_left hcos c.radius_pos.le
    rw [hcenterY]
    linarith [c.radius_pos]
  graph_contDiff := contDiff_const.add (upperDiskHorizontal_contDiff c)
  base_order_graph := by
    intro y _
    unfold upperDiskRightGraph
    linarith [upperDiskHorizontalRoot_pos c y]
  lowerBound_le_base := le_rfl
  base_le_upperBound := by linarith [c.radius_pos]
  graph_bounds := by
    intro y _
    unfold upperDiskRightGraph
    exact ⟨by linarith [upperDiskHorizontalRoot_pos c y],
      by linarith [upperDiskHorizontalRoot_le_radius c y]⟩
  carrier_in_zone := by
    intro p hp
    simp only [CMVTransverseContactVariation.mem_horizontalRegionBetween,
      mem_Ioo] at hp
    change 1 < |p.2|
    rw [abs_of_pos (by linarith [hp.1.1])]
    exact hp.1.1

def upperDiskLeftPatch
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    CMVTransverseContactVariation.HorizontalGraphPatch where
  a := 1
  b := c.center.2 + 7 * c.radius / 8
  base := c.center.1
  graph := upperDiskLeftGraph c
  lowerBound := c.center.1 - c.radius
  upperBound := c.center.1
  zone := .exterior
  side := .above
  a_lt_b := by
    have hcenterY :
        c.center.2 = 1 - c.radius * Real.cos c.theta := by
      simp [OneSidedCircularCap.center, hside, hbase]
    have hcosMul :=
      mul_le_mul_of_nonneg_left hcos c.radius_pos.le
    rw [hcenterY]
    linarith [c.radius_pos]
  graph_contDiff := contDiff_const.sub (upperDiskHorizontal_contDiff c)
  base_order_graph := by
    intro y _
    unfold upperDiskLeftGraph
    linarith [upperDiskHorizontalRoot_pos c y]
  lowerBound_le_base := by linarith [c.radius_pos]
  base_le_upperBound := le_rfl
  graph_bounds := by
    intro y _
    unfold upperDiskLeftGraph
    exact ⟨by linarith [upperDiskHorizontalRoot_le_radius c y],
      by linarith [upperDiskHorizontalRoot_pos c y]⟩
  carrier_in_zone := by
    intro p hp
    simp only [CMVTransverseContactVariation.mem_horizontalRegionBetween,
      mem_Ioo] at hp
    change 1 < |p.2|
    rw [abs_of_pos (by linarith [hp.1.1])]
    exact hp.1.1

def upperDiskVerticalNeighborhood (c : OneSidedCircularCap) :
    Set PlanePoint :=
  Prod.fst ⁻¹' Ioo (c.center.1 - c.radius / 2)
      (c.center.1 + c.radius / 2) ∩
    Prod.snd ⁻¹' Ioi c.center.2

def upperDiskRightNeighborhood (c : OneSidedCircularCap) :
    Set PlanePoint :=
  Prod.snd ⁻¹' Ioo 1 (c.center.2 + 7 * c.radius / 8) ∩
    Prod.fst ⁻¹' Ioi c.center.1

def upperDiskLeftNeighborhood (c : OneSidedCircularCap) :
    Set PlanePoint :=
  Prod.snd ⁻¹' Ioo 1 (c.center.2 + 7 * c.radius / 8) ∩
    Prod.fst ⁻¹' Iio c.center.1

def upperDiskVerticalActualChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    ActualRegularGraphChart (capOpenRepresentative c) where
  patch := upperDiskVerticalPatch c hbase hside hcos
  neighborhood := upperDiskVerticalNeighborhood c
  neighborhood_open :=
    (isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_Ioi.preimage continuous_snd)
  local_frontier := by
    rw [frontier_capOpenRepresentative]
    ext q
    constructor
    · rintro ⟨hqCircle, hqx, hqy⟩
      refine ⟨q.1, hqx, ?_⟩
      apply Prod.ext
      · rfl
      · have hgraphCircle := upperDiskVerticalGraph_circle c
          ⟨hqx.1.le, hqx.2.le⟩
        have hgraphPos :
            0 < upperDiskVerticalGraph c q.1 - c.center.2 := by
          unfold upperDiskVerticalGraph
          linarith [diskChartRoot_pos (center := c.center.1)
            c.radius_pos (upperDiskVertical_parameters c).1
            (upperDiskVertical_parameters c).2.1
            (upperDiskVertical_parameters c).2.2 q.1]
        change circleValue c.center c.radius q = 0 at hqCircle
        unfold circleValue at hqCircle
        change c.center.2 < q.2 at hqy
        change upperDiskVerticalGraph c q.1 = q.2
        nlinarith
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, hx, ?_⟩
      · change circleValue c.center c.radius
          (x, upperDiskVerticalGraph c x) = 0
        unfold circleValue
        have hcircle := upperDiskVerticalGraph_circle c
          ⟨hx.1.le, hx.2.le⟩
        nlinarith
      · change c.center.2 < upperDiskVerticalGraph c x
        unfold upperDiskVerticalGraph
        linarith [diskChartRoot_pos (center := c.center.1)
          c.radius_pos (upperDiskVertical_parameters c).1
          (upperDiskVertical_parameters c).2.1
          (upperDiskVertical_parameters c).2.2 x]


def upperDiskRightActualChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    ActualRegularHorizontalGraphChart (capOpenRepresentative c) where
  patch := upperDiskRightPatch c hbase hside hcos
  neighborhood := upperDiskRightNeighborhood c
  neighborhood_open :=
    (isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_Ioi.preimage continuous_fst)
  local_frontier := by
    rw [frontier_capOpenRepresentative]
    ext q
    constructor
    · rintro ⟨hqCircle, hqy, hqx⟩
      refine ⟨q.2, hqy, ?_⟩
      apply Prod.ext
      · have hgraphCircle := upperDiskRightGraph_circle c hbase hside
          hcosLower ⟨hqy.1.le, hqy.2.le⟩
        have hgraphPos :
            0 < upperDiskRightGraph c q.2 - c.center.1 := by
          unfold upperDiskRightGraph
          linarith [upperDiskHorizontalRoot_pos c q.2]
        change circleValue c.center c.radius q = 0 at hqCircle
        unfold circleValue at hqCircle
        change c.center.1 < q.1 at hqx
        change upperDiskRightGraph c q.2 = q.1
        nlinarith
      · rfl
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, hy, ?_⟩
      · change circleValue c.center c.radius
          (upperDiskRightGraph c y, y) = 0
        unfold circleValue
        have hcircle := upperDiskRightGraph_circle c hbase hside
          hcosLower ⟨hy.1.le, hy.2.le⟩
        nlinarith
      · change c.center.1 < upperDiskRightGraph c y
        unfold upperDiskRightGraph
        linarith [upperDiskHorizontalRoot_pos c y]

def upperDiskLeftActualChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    ActualRegularHorizontalGraphChart (capOpenRepresentative c) where
  patch := upperDiskLeftPatch c hbase hside hcos
  neighborhood := upperDiskLeftNeighborhood c
  neighborhood_open :=
    (isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_Iio.preimage continuous_fst)
  local_frontier := by
    rw [frontier_capOpenRepresentative]
    ext q
    constructor
    · rintro ⟨hqCircle, hqy, hqx⟩
      refine ⟨q.2, hqy, ?_⟩
      apply Prod.ext
      · have hgraphCircle := upperDiskLeftGraph_circle c hbase hside
          hcosLower ⟨hqy.1.le, hqy.2.le⟩
        have hgraphNeg :
            upperDiskLeftGraph c q.2 - c.center.1 < 0 := by
          unfold upperDiskLeftGraph
          linarith [upperDiskHorizontalRoot_pos c q.2]
        change circleValue c.center c.radius q = 0 at hqCircle
        unfold circleValue at hqCircle
        change q.1 < c.center.1 at hqx
        change upperDiskLeftGraph c q.2 = q.1
        nlinarith
      · rfl
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, hy, ?_⟩
      · change circleValue c.center c.radius
          (upperDiskLeftGraph c y, y) = 0
        unfold circleValue
        have hcircle := upperDiskLeftGraph_circle c hbase hside
          hcosLower ⟨hy.1.le, hy.2.le⟩
        nlinarith
      · change upperDiskLeftGraph c y < c.center.1
        unfold upperDiskLeftGraph
        linarith [upperDiskHorizontalRoot_pos c y]

def upperDiskCurvature (c : OneSidedCircularCap) : ℝ :=
  -(1 / c.radius)

private theorem upperDiskVertical_occupiedGerm
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (x : ℝ) (hx : x ∈ Ioo
      (upperDiskVerticalPatch c hbase hside hcos).a
      (upperDiskVerticalPatch c hbase hside hcos).b) :
    ∀ᶠ q in 𝓝 ((upperDiskVerticalPatch c hbase hside hcos).graphTrace x),
      (q ∈ capOpenRepresentative c ↔
        q ∈ (upperDiskVerticalPatch c hbase hside hcos).occupiedGraphDomain
          (upperDiskVerticalPatch c hbase hside hcos).graph) := by
  let A := upperDiskVerticalActualChart c hbase hside hcos
  have htrace :
      (upperDiskVerticalPatch c hbase hside hcos).graphTrace x ∈
        upperDiskVerticalNeighborhood c :=
    A.graphTrace_mem_neighborhood hx
  filter_upwards [
    ((isOpen_Ioo.preimage continuous_fst).inter
      (isOpen_Ioi.preimage continuous_snd)).mem_nhds htrace] with q hq
  rw [mem_capOpenRepresentative_iff_circleValue_neg]
  simp only [GraphPatch.occupiedGraphDomain, upperDiskVerticalPatch,
    Set.mem_ofPred_eq]
  have hqx : q.1 ∈ Icc (c.center.1 - c.radius / 2)
      (c.center.1 + c.radius / 2) :=
    ⟨hq.1.1.le, hq.1.2.le⟩
  have hcircle := upperDiskVerticalGraph_circle c hqx
  have hgraphPos :
      0 < upperDiskVerticalGraph c q.1 - c.center.2 := by
    unfold upperDiskVerticalGraph
    linarith [diskChartRoot_pos (center := c.center.1)
      c.radius_pos (upperDiskVertical_parameters c).1
      (upperDiskVertical_parameters c).2.1
      (upperDiskVertical_parameters c).2.2 q.1]
  have hqPos : 0 < q.2 - c.center.2 := by
    have : c.center.2 < q.2 := hq.2
    linarith
  unfold circleValue
  constructor
  · intro hinside
    by_contra hnot
    have hprod : 0 ≤
        (q.2 - upperDiskVerticalGraph c q.1) *
          (q.2 + upperDiskVerticalGraph c q.1 - 2 * c.center.2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · intro hbelow
    have hprod : 0 <
        (upperDiskVerticalGraph c q.1 - q.2) *
          (upperDiskVerticalGraph c q.1 + q.2 - 2 * c.center.2) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

private theorem upperDiskRight_occupiedGerm
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    (y : ℝ) (hy : y ∈ Ioo
      (upperDiskRightPatch c hbase hside hcos).a
      (upperDiskRightPatch c hbase hside hcos).b) :
    ∀ᶠ q in 𝓝 ((upperDiskRightPatch c hbase hside hcos).graphTrace y),
      (q ∈ capOpenRepresentative c ↔
        q ∈ (upperDiskRightPatch c hbase hside hcos).occupiedGraphDomain) := by
  let A := upperDiskRightActualChart c hbase hside hcos hcosLower
  have htrace :
      (upperDiskRightPatch c hbase hside hcos).graphTrace y ∈
        upperDiskRightNeighborhood c :=
    A.graphTrace_mem_neighborhood hy
  filter_upwards [
    ((isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_Ioi.preimage continuous_fst)).mem_nhds htrace] with q hq
  rw [mem_capOpenRepresentative_iff_circleValue_neg]
  simp only [CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
    upperDiskRightPatch, Set.mem_ofPred_eq]
  have hqy : q.2 ∈ Icc 1 (c.center.2 + 7 * c.radius / 8) :=
    ⟨hq.1.1.le, hq.1.2.le⟩
  have hcircle :=
    upperDiskRightGraph_circle c hbase hside hcosLower hqy
  have hgraphPos :
      0 < upperDiskRightGraph c q.2 - c.center.1 := by
    unfold upperDiskRightGraph
    linarith [upperDiskHorizontalRoot_pos c q.2]
  have hqPos : 0 < q.1 - c.center.1 := by
    have : c.center.1 < q.1 := hq.2
    linarith
  unfold circleValue
  constructor
  · intro hinside
    by_contra hnot
    have hprod : 0 ≤
        (q.1 - upperDiskRightGraph c q.2) *
          (q.1 + upperDiskRightGraph c q.2 - 2 * c.center.1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · intro hleft
    have hprod : 0 <
        (upperDiskRightGraph c q.2 - q.1) *
          (upperDiskRightGraph c q.2 + q.1 - 2 * c.center.1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

private theorem upperDiskLeft_occupiedGerm
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    (y : ℝ) (hy : y ∈ Ioo
      (upperDiskLeftPatch c hbase hside hcos).a
      (upperDiskLeftPatch c hbase hside hcos).b) :
    ∀ᶠ q in 𝓝 ((upperDiskLeftPatch c hbase hside hcos).graphTrace y),
      (q ∈ capOpenRepresentative c ↔
        q ∈ (upperDiskLeftPatch c hbase hside hcos).occupiedGraphDomain) := by
  let A := upperDiskLeftActualChart c hbase hside hcos hcosLower
  have htrace :
      (upperDiskLeftPatch c hbase hside hcos).graphTrace y ∈
        upperDiskLeftNeighborhood c :=
    A.graphTrace_mem_neighborhood hy
  filter_upwards [
    ((isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_Iio.preimage continuous_fst)).mem_nhds htrace] with q hq
  rw [mem_capOpenRepresentative_iff_circleValue_neg]
  simp only [CMVTransverseContactVariation.HorizontalGraphPatch.occupiedGraphDomain,
    upperDiskLeftPatch, Set.mem_ofPred_eq]
  have hqy : q.2 ∈ Icc 1 (c.center.2 + 7 * c.radius / 8) :=
    ⟨hq.1.1.le, hq.1.2.le⟩
  have hcircle :=
    upperDiskLeftGraph_circle c hbase hside hcosLower hqy
  have hgraphNeg :
      upperDiskLeftGraph c q.2 - c.center.1 < 0 := by
    unfold upperDiskLeftGraph
    linarith [upperDiskHorizontalRoot_pos c q.2]
  have hqNeg : q.1 - c.center.1 < 0 := by
    have : q.1 < c.center.1 := hq.2
    linarith
  unfold circleValue
  constructor
  · intro hinside
    by_contra hnot
    have hprod : 0 ≤
        (upperDiskLeftGraph c q.2 - q.1) *
          (2 * c.center.1 -
            upperDiskLeftGraph c q.2 - q.1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · intro hright
    have hprod : 0 <
        (q.1 - upperDiskLeftGraph c q.2) *
          (2 * c.center.1 -
            upperDiskLeftGraph c q.2 - q.1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

def upperDiskVerticalRegularChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    RegularChart (capOpenRepresentative c) (upperDiskCurvature c) :=
  .vertical (upperDiskVerticalActualChart c hbase hside hcos)
    (by
      intro x hx
      unfold GraphPatch.orientedGraphCurvature
      simp only [upperDiskVerticalActualChart, upperDiskVerticalPatch,
        OccupiedSide.areaSign, one_mul, upperDiskCurvature]
      have hf : ContDiff ℝ 2 (upperDiskVerticalGraph c) :=
        (upperDiskVerticalPatch c hbase hside hcos).graph_contDiff
      apply graphCurvature_eq_neg_inv_of_positive_circle
        (f := upperDiskVerticalGraph c)
        (a := c.center.1 - c.radius / 2)
        (b := c.center.1 + c.radius / 2)
        (centerCoord := c.center.1) (centerGraph := c.center.2)
        hf c.radius_pos
      · intro t ht
        exact upperDiskVerticalGraph_circle c ⟨ht.1.le, ht.2.le⟩
      · intro t _
        unfold upperDiskVerticalGraph
        linarith [diskChartRoot_pos (center := c.center.1)
          c.radius_pos (upperDiskVertical_parameters c).1
          (upperDiskVertical_parameters c).2.1
          (upperDiskVertical_parameters c).2.2 t]
      · exact hx)
    (upperDiskVertical_occupiedGerm c hbase hside hcos)

def upperDiskRightRegularChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    RegularChart (capOpenRepresentative c) (upperDiskCurvature c) :=
  .horizontal (upperDiskRightActualChart c hbase hside hcos hcosLower)
    (by
      intro y hy
      unfold CMVTransverseContactVariation.HorizontalGraphPatch.orientedGraphCurvature
        CMVTransverseContactVariation.contactCurvature
      simp only [upperDiskRightActualChart, upperDiskRightPatch,
        OccupiedSide.areaSign, one_mul, upperDiskCurvature]
      have hf : ContDiff ℝ 2 (upperDiskRightGraph c) :=
        (upperDiskRightPatch c hbase hside hcos).graph_contDiff
      apply graphCurvature_eq_neg_inv_of_positive_circle
        (f := upperDiskRightGraph c)
        (a := 1) (b := c.center.2 + 7 * c.radius / 8)
        (centerCoord := c.center.2) (centerGraph := c.center.1)
        hf c.radius_pos
      · intro t ht
        have hcircle := upperDiskRightGraph_circle c hbase hside hcosLower
          ⟨ht.1.le, ht.2.le⟩
        nlinarith
      · intro t _
        unfold upperDiskRightGraph
        linarith [upperDiskHorizontalRoot_pos c t]
      · exact hy)
    (upperDiskRight_occupiedGerm c hbase hside hcos hcosLower)

def upperDiskLeftRegularChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    RegularChart (capOpenRepresentative c) (upperDiskCurvature c) :=
  .horizontal (upperDiskLeftActualChart c hbase hside hcos hcosLower)
    (by
      intro y hy
      unfold CMVTransverseContactVariation.HorizontalGraphPatch.orientedGraphCurvature
        CMVTransverseContactVariation.contactCurvature
      simp only [upperDiskLeftActualChart, upperDiskLeftPatch,
        OccupiedSide.areaSign, neg_mul, one_mul, upperDiskCurvature]
      apply neg_inj.mp
      simp only [neg_neg]
      have hf : ContDiff ℝ 2 (upperDiskLeftGraph c) :=
        (upperDiskLeftPatch c hbase hside hcos).graph_contDiff
      apply graphCurvature_eq_inv_of_negative_circle
        (f := upperDiskLeftGraph c)
        (a := 1) (b := c.center.2 + 7 * c.radius / 8)
        (centerCoord := c.center.2) (centerGraph := c.center.1)
        hf c.radius_pos
      · intro t ht
        have hcircle := upperDiskLeftGraph_circle c hbase hside hcosLower
          ⟨ht.1.le, ht.2.le⟩
        nlinarith
      · intro t _
        unfold upperDiskLeftGraph
        linarith [upperDiskHorizontalRoot_pos c t]
      · exact hy)
    (upperDiskLeft_occupiedGerm c hbase hside hcos hcosLower)



abbrev upperDiskExteriorLocus (c : OneSidedCircularCap) : Set PlanePoint :=
  frontier (capOpenRepresentative c) ∩ {q | 1 < q.2}

def upperDiskSelectedChart
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    (p : upperDiskExteriorLocus c) :
    RegularChart (capOpenRepresentative c) (upperDiskCurvature c) :=
  if c.center.2 + 13 * c.radius / 15 < p.1.2 then
    upperDiskVerticalRegularChart c hbase hside hcos
  else if c.center.1 < p.1.1 then
    upperDiskRightRegularChart c hbase hside hcos hcosLower
  else
    upperDiskLeftRegularChart c hbase hside hcos hcosLower

private theorem upperDiskVertical_window_subset_locus
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    frontier (capOpenRepresentative c) ∩
        (upperDiskVerticalRegularChart c hbase hside hcos).neighborhood ⊆
      upperDiskExteriorLocus c := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  have htrace :
      q ∈ (upperDiskVerticalRegularChart c hbase hside hcos).trace ''
        (upperDiskVerticalRegularChart c hbase hside hcos).parameterInterval := by
    rw [← (upperDiskVerticalRegularChart c hbase hside hcos).local_frontier]
    exact hq
  rcases htrace with ⟨x, hx, rfl⟩
  change 1 < upperDiskVerticalGraph c x
  exact upperDiskVerticalGraph_above_one c hbase hside hcos
    ⟨hx.1.le, hx.2.le⟩

private theorem upperDiskRight_window_subset_locus
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    frontier (capOpenRepresentative c) ∩
        (upperDiskRightRegularChart c hbase hside hcos hcosLower).neighborhood ⊆
      upperDiskExteriorLocus c := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact hq.2.1.1

private theorem upperDiskLeft_window_subset_locus
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    frontier (capOpenRepresentative c) ∩
        (upperDiskLeftRegularChart c hbase hside hcos hcosLower).neighborhood ⊆
      upperDiskExteriorLocus c := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact hq.2.1.1




private theorem upperDiskSelectedChart_base
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta)
    (p : upperDiskExteriorLocus c) :
    (upperDiskSelectedChart c hbase hside hcos hcosLower p).parameter p.1 ∈
        (upperDiskSelectedChart c hbase hside hcos hcosLower p).parameterInterval ∧
      (upperDiskSelectedChart c hbase hside hcos hcosLower p).trace
          ((upperDiskSelectedChart c hbase hside hcos hcosLower p).parameter p.1) =
        p.1 := by
  have hpCircle : circleValue c.center c.radius p.1 = 0 := by
    have hpFrontier := p.2.1
    rw [frontier_capOpenRepresentative] at hpFrontier
    exact hpFrontier
  unfold circleValue at hpCircle
  have hpAbove : 1 < p.1.2 := p.2.2
  have hcenterY :
      c.center.2 = 1 - c.radius * Real.cos c.theta := by
    simp [OneSidedCircularCap.center, hside, hbase]
  by_cases htop : c.center.2 + 13 * c.radius / 15 < p.1.2
  · rw [upperDiskSelectedChart, if_pos htop]
    apply
      (upperDiskVerticalRegularChart c hbase hside hcos).parameter_interior_and_trace_eq_of_mem
    refine ⟨p.2.1, ?_⟩
    change p.1.1 ∈ Ioo (c.center.1 - c.radius / 2)
        (c.center.1 + c.radius / 2) ∧ c.center.2 < p.1.2
    have hdyProd : 0 <
        (p.1.2 - c.center.2 - 13 * c.radius / 15) *
          (p.1.2 - c.center.2 + 13 * c.radius / 15) :=
      mul_pos (by linarith) (by linarith [c.radius_pos])
    have hdxSq :
        (p.1.1 - c.center.1) ^ 2 < c.radius ^ 2 / 4 := by
      nlinarith
    constructor
    · constructor
      · by_contra hnot
        have hprod : 0 ≤
            (c.center.1 - p.1.1 - c.radius / 2) *
              (c.center.1 - p.1.1 + c.radius / 2) :=
          mul_nonneg (by linarith) (by linarith [c.radius_pos])
        nlinarith
      · by_contra hnot
        have hprod : 0 ≤
            (p.1.1 - c.center.1 - c.radius / 2) *
              (p.1.1 - c.center.1 + c.radius / 2) :=
          mul_nonneg (by linarith) (by linarith [c.radius_pos])
        nlinarith
    · linarith [c.radius_pos]
  · by_cases hright : c.center.1 < p.1.1
    · rw [upperDiskSelectedChart, if_neg htop, if_pos hright]
      let C := upperDiskRightRegularChart c hbase hside hcos hcosLower
      apply C.parameter_interior_and_trace_eq_of_mem
      refine ⟨p.2.1, ?_⟩
      change p.1.2 ∈ Ioo 1 (c.center.2 + 7 * c.radius / 8) ∧
        c.center.1 < p.1.1
      exact ⟨⟨hpAbove, by
        have := le_of_not_gt htop
        linarith [c.radius_pos]⟩, hright⟩
    · rw [upperDiskSelectedChart, if_neg htop, if_neg hright]
      let C := upperDiskLeftRegularChart c hbase hside hcos hcosLower
      apply C.parameter_interior_and_trace_eq_of_mem
      refine ⟨p.2.1, ?_⟩
      change p.1.2 ∈ Ioo 1 (c.center.2 + 7 * c.radius / 8) ∧
        p.1.1 < c.center.1
      have hcosMul :=
        mul_le_mul_of_nonneg_left hcosLower c.radius_pos.le
      have hdyLower : -c.radius < p.1.2 - c.center.2 := by
        rw [hcenterY]
        nlinarith
      have hdyUpper : p.1.2 - c.center.2 < c.radius := by
        have := le_of_not_gt htop
        linarith [c.radius_pos]
      have hxne : p.1.1 ≠ c.center.1 := by
        intro hx
        have hprod : 0 <
            (c.radius - (p.1.2 - c.center.2)) *
              (c.radius + (p.1.2 - c.center.2)) :=
          mul_pos (by linarith) (by linarith)
        nlinarith
      exact ⟨⟨hpAbove, by
        have := le_of_not_gt htop
        linarith [c.radius_pos]⟩,
        lt_of_le_of_ne (le_of_not_gt hright) hxne⟩

def upperDiskMixedAtlas
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    BranchNeutralMixedGraphAtlas
      (capOpenRepresentative c) (upperDiskExteriorLocus c)
      (upperDiskCurvature c) where
  locus_subset_frontier := by
    intro p hp
    exact hp.1
  chart := upperDiskSelectedChart c hbase hside hcos hcosLower
  chart_window_subset_locus := by
    intro p
    unfold upperDiskSelectedChart
    split_ifs
    · exact upperDiskVertical_window_subset_locus c hbase hside hcos
    · exact upperDiskRight_window_subset_locus c hbase hside hcos hcosLower
    · exact upperDiskLeft_window_subset_locus c hbase hside hcos hcosLower
  base_interior := by
    intro p
    exact (upperDiskSelectedChart_base c hbase hside hcos hcosLower p).1
  base_eq := by
    intro p
    exact (upperDiskSelectedChart_base c hbase hside hcos hcosLower p).2

theorem deriv_upperDiskVerticalGraph_center
    (c : OneSidedCircularCap) :
    deriv (upperDiskVerticalGraph c) c.center.1 = 0 := by
  have hf : ContDiff ℝ 2 (upperDiskVerticalGraph c) := by
    have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      apply WithTop.coe_le_coe.mpr
      exact le_top
    exact (contDiff_const.add
      (contDiff_diskChartRoot c.radius_pos
        (upperDiskVertical_parameters c).1
        (upperDiskVertical_parameters c).2.1
        (upperDiskVertical_parameters c).2.2)).of_le hle
  have hx : c.center.1 ∈ Ioo
      (c.center.1 - c.radius / 2) (c.center.1 + c.radius / 2) := by
    constructor <;> linarith [c.radius_pos]
  have hlocal :
      (fun z : ℝ =>
        (z - c.center.1) ^ 2 +
          (upperDiskVerticalGraph c z - c.center.2) ^ 2) =ᶠ[𝓝 c.center.1]
        (fun _ : ℝ => c.radius ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact upperDiskVerticalGraph_circle c ⟨hz.1.le, hz.2.le⟩
  have hfAt : HasDerivAt (upperDiskVerticalGraph c)
      (deriv (upperDiskVerticalGraph c) c.center.1) c.center.1 :=
    (hf.differentiable (by norm_num) c.center.1).hasDerivAt
  have hraw :=
    (((hasDerivAt_id c.center.1).sub_const c.center.1).pow 2).add
      ((hfAt.sub_const c.center.2).pow 2)
  have hderiv :
      deriv
        (fun z : ℝ =>
          (z - c.center.1) ^ 2 +
            (upperDiskVerticalGraph c z - c.center.2) ^ 2)
          c.center.1 =
        2 * (c.center.1 - c.center.1) +
          2 * (upperDiskVerticalGraph c c.center.1 - c.center.2) *
            deriv (upperDiskVerticalGraph c) c.center.1 := by
    have hfun :
        (fun z : ℝ =>
          (z - c.center.1) ^ 2 +
            (upperDiskVerticalGraph c z - c.center.2) ^ 2) =
          ((fun z : ℝ => id z - c.center.1) ^ 2) +
            ((fun z : ℝ => upperDiskVerticalGraph c z - c.center.2) ^ 2) := by
      funext z
      rfl
    rw [hfun, hraw.deriv]
    dsimp only [id]
    ring
  have hzero :
      deriv
        (fun z : ℝ =>
          (z - c.center.1) ^ 2 +
            (upperDiskVerticalGraph c z - c.center.2) ^ 2)
          c.center.1 = 0 := by
    rw [hlocal.deriv_eq, deriv_const]
  have hgraphPos :
      0 < upperDiskVerticalGraph c c.center.1 - c.center.2 := by
    unfold upperDiskVerticalGraph
    linarith [diskChartRoot_pos (center := c.center.1)
      c.radius_pos (upperDiskVertical_parameters c).1
      (upperDiskVertical_parameters c).2.1
      (upperDiskVertical_parameters c).2.2 c.center.1]
  rw [hderiv] at hzero
  nlinarith

private theorem upperDiskVerticalGraph_center_value
    (c : OneSidedCircularCap) :
    upperDiskVerticalGraph c c.center.1 = c.center.2 + c.radius := by
  have hcircle := upperDiskVerticalGraph_circle c
    (show c.center.1 ∈ Icc
      (c.center.1 - c.radius / 2) (c.center.1 + c.radius / 2) by
        constructor <;> linarith [c.radius_pos])
  have hpos :
      0 < upperDiskVerticalGraph c c.center.1 - c.center.2 := by
    unfold upperDiskVerticalGraph
    linarith [diskChartRoot_pos (center := c.center.1)
      c.radius_pos (upperDiskVertical_parameters c).1
      (upperDiskVertical_parameters c).2.1
      (upperDiskVertical_parameters c).2.2 c.center.1]
  nlinarith [c.radius_pos]





private theorem capParam_zero_strict_upper
    (c : OneSidedCircularCap) (hside : c.side = .upper) :
    c.baseY < (capParam c 0).2 := by
  have hcosne : Real.cos c.theta ≠ 1 := by
    intro hcos
    have hthetaZero := (Real.cos_eq_one_iff_of_lt_of_lt
      (by nlinarith [c.theta_pos, Real.pi_pos])
      (by nlinarith [c.theta_lt_pi, Real.pi_pos])).mp hcos
    linarith [c.theta_pos]
  have hcos : Real.cos c.theta < 1 :=
    lt_of_le_of_ne (Real.cos_le_one _) hcosne
  simp only [capParam, OneSidedCircularCap.arcPoint, hside, zero_div,
    Real.sin_zero, Real.cos_zero, mul_zero, add_zero]
  nlinarith [c.radius_pos]

private theorem capParam_zero_strict_lower
    (c : OneSidedCircularCap) (hside : c.side = .lower) :
    (capParam c 0).2 < c.baseY := by
  have hcosne : Real.cos c.theta ≠ 1 := by
    intro hcos
    have hthetaZero := (Real.cos_eq_one_iff_of_lt_of_lt
      (by nlinarith [c.theta_pos, Real.pi_pos])
      (by nlinarith [c.theta_lt_pi, Real.pi_pos])).mp hcos
    linarith [c.theta_pos]
  have hcos : Real.cos c.theta < 1 :=
    lt_of_le_of_ne (Real.cos_le_one _) hcosne
  simp only [capParam, OneSidedCircularCap.arcPoint, hside, zero_div,
    Real.sin_zero, Real.cos_zero, mul_zero, add_zero]
  nlinarith [c.radius_pos]

theorem minor_cos_theta : Real.cos minor.theta = 1 / 2 := by
  simp [minor, Real.cos_pi_div_three]

theorem major_cos_theta : Real.cos major.theta = -(1 / 2) := by
  change Real.cos (2 * Real.pi / 3) = -(1 / 2)
  rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
    Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num
/-- Concrete mixed-coordinate atlas for the independently defined minor
bounded-open cap disk. -/
def minorMixedGraphAtlas :
    BranchNeutralMixedGraphAtlas
      (capOpenRepresentative minor)
      (frontier (capOpenRepresentative minor) ∩
        {q : PlanePoint | 1 < q.2})
      (upperDiskCurvature minor) := by
  simpa [upperDiskExteriorLocus] using
    upperDiskMixedAtlas minor rfl rfl
      (by rw [minor_cos_theta])
      (by rw [minor_cos_theta]; norm_num)

/-- Concrete mixed-coordinate atlas for the independently defined major
bounded-open cap disk.  Its horizontal charts cover both equators. -/
def majorMixedGraphAtlas :
    BranchNeutralMixedGraphAtlas
      (capOpenRepresentative major)
      (frontier (capOpenRepresentative major) ∩
        {q : PlanePoint | 1 < q.2})
      (upperDiskCurvature major) := by
  simpa [upperDiskExteriorLocus] using
    upperDiskMixedAtlas major rfl rfl
      (by rw [major_cos_theta]; norm_num)
      (by rw [major_cos_theta])


private theorem capParam_zero_eq_upperPole
    (c : OneSidedCircularCap) (hside : c.side = .upper) :
    capParam c 0 = (c.center.1, c.center.2 + c.radius) := by
  simp [capParam, OneSidedCircularCap.arcPoint,
    OneSidedCircularCap.center, hside]
  ring

def upperDiskAtlasPole
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2) :
    upperDiskExteriorLocus c := by
  refine ⟨capParam c 0, ?_, ?_⟩
  · rw [frontier_capOpenRepresentative]
    change circleValue c.center c.radius (capParam c 0) = 0
    rw [capParam_zero_eq_upperPole c hside]
    unfold circleValue
    ring
  · change 1 < (capParam c 0).2
    rw [capParam_zero_eq_upperPole c hside]
    have hcenterY :
        c.center.2 = 1 - c.radius * Real.cos c.theta := by
      simp [OneSidedCircularCap.center, hside, hbase]
    have hcosMul :=
      mul_le_mul_of_nonneg_left hcos c.radius_pos.le
    rw [hcenterY]
    nlinarith [c.radius_pos]

private theorem upperDiskAtlasPole_selected_vertical
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    (upperDiskMixedAtlas c hbase hside hcos hcosLower).chart
        (upperDiskAtlasPole c hbase hside hcos) =
      upperDiskVerticalRegularChart c hbase hside hcos := by
  change upperDiskSelectedChart c hbase hside hcos hcosLower
      (upperDiskAtlasPole c hbase hside hcos) =
    upperDiskVerticalRegularChart c hbase hside hcos
  unfold upperDiskSelectedChart
  rw [if_pos]
  change c.center.2 + 13 * c.radius / 15 <
    (capParam c 0).2
  rw [capParam_zero_eq_upperPole c hside]
  dsimp only
  linarith [c.radius_pos]

theorem upperDiskAtlasPole_supportingCenter
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    (upperDiskMixedAtlas c hbase hside hcos hcosLower).supportingCenterAt
        (upperDiskAtlasPole c hbase hside hcos) =
      c.center := by
  unfold BranchNeutralMixedGraphAtlas.supportingCenterAt
  rw [upperDiskAtlasPole_selected_vertical c hbase hside hcos hcosLower]
  simp only [upperDiskVerticalRegularChart, upperDiskVerticalActualChart]
  have hpoleFst :
      (upperDiskAtlasPole c hbase hside hcos).1.1 = c.center.1 := by
    change (capParam c 0).1 = c.center.1
    rw [capParam_zero_eq_upperPole c hside]
  rw [hpoleFst]
  change
    (upperDiskVerticalPatch c hbase hside hcos).supportingCenter
        (upperDiskCurvature c) c.center.1 =
      c.center
  unfold GraphPatch.supportingCenter
    CMVCurvatureIntegration.centerInvariant
    CMVCurvatureIntegration.normalizedTangent
    CMVCurvatureIntegration.euclideanSpeed
    GraphPatch.graphTrace GraphPatch.graphVelocity
  simp only [upperDiskVerticalPatch, deriv_upperDiskVerticalGraph_center,
    upperDiskVerticalGraph_center_value]
  unfold upperDiskCurvature
  apply Prod.ext <;> dsimp only
  · norm_num
  · norm_num [OccupiedSide.areaSign]

theorem upperDiskCurvature_ne_zero (c : OneSidedCircularCap) :
    upperDiskCurvature c ≠ 0 := by
  unfold upperDiskCurvature
  exact neg_ne_zero.mpr (one_div_ne_zero c.radius_pos.ne')

theorem abs_one_div_upperDiskCurvature (c : OneSidedCircularCap) :
    |1 / upperDiskCurvature c| = c.radius := by
  have hr : c.radius ≠ 0 := c.radius_pos.ne'
  have hfrac : 1 / upperDiskCurvature c = -c.radius := by
    unfold upperDiskCurvature
    field_simp [hr]
  rw [hfrac, abs_neg, abs_of_pos c.radius_pos]

/-- Component saturation obtained from the concrete mixed atlas, not from the
standalone preconnectedness proof for a circle clip. -/
theorem upperDisk_atlas_component_eq
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    connectedComponentIn
        (frontier (capOpenRepresentative c) ∩
          {q : PlanePoint | 1 < q.2})
        (upperDiskAtlasPole c hbase hside hcos).1 =
      {q : PlanePoint | circleValue c.center c.radius q = 0} ∩
        {q : PlanePoint | 1 < q.2} := by
  have hsat :=
    upperExterior_connectedComponentIn_eq_supportAt
      (upperDiskMixedAtlas c hbase hside hcos hcosLower)
      (upperDiskAtlasPole c hbase hside hcos)
  have hsupport :=
    (upperDiskMixedAtlas c hbase hside hcos hcosLower).supportAt_eq_circleValue_zero
      (upperDiskAtlasPole c hbase hside hcos)
      (upperDiskCurvature_ne_zero c)
  rw [hsupport] at hsat
  rw [abs_one_div_upperDiskCurvature c] at hsat
  have hsupportSet :
      {q : PlanePoint |
          circleValue
            ((upperDiskMixedAtlas c hbase hside hcos hcosLower).supportingCenterAt
              (upperDiskAtlasPole c hbase hside hcos))
            c.radius q = 0} =
        {q : PlanePoint | circleValue c.center c.radius q = 0} := by
    ext q
    rw [upperDiskAtlasPole_supportingCenter c hbase hside hcos hcosLower]
  rw [hsupportSet] at hsat
  exact hsat

/-- The concrete bounded-open cap atlas exercises the source-derived curvature
sign theorem; no `UpperPoleGeometry` value or occupied-side premise is passed
to the consumer. -/
theorem upperDisk_atlas_curvature_neg
    (c : OneSidedCircularCap) (hbase : c.baseY = 1)
    (hside : c.side = .upper) (hcos : Real.cos c.theta ≤ 1 / 2)
    (hcosLower : -(1 / 2 : ℝ) ≤ Real.cos c.theta) :
    upperDiskCurvature c < 0 :=
  commonCurvature_neg_of_bounded_upperExterior
    (upperDiskMixedAtlas c hbase hside hcos hcosLower)
    (capOpenRepresentative_isBounded c)
    (upperDiskAtlasPole c hbase hside hcos)


/-- The exterior frontier component of every upper bounded-open cap
representative is exactly its derived circular half-plane portion. -/
theorem upperCap_openRepresentative_component_eq
    (c : OneSidedCircularCap) (hside : c.side = .upper) :
    connectedComponentIn
        (frontier (capOpenRepresentative c) ∩
          {q : PlanePoint | c.baseY < q.2}) (capParam c 0) =
      {q : PlanePoint | circleValue c.center c.radius q = 0} ∩
        {q : PlanePoint | c.baseY < q.2} := by
  rw [frontier_capOpenRepresentative]
  apply connectedComponentIn_eq_self_of_isPreconnected
  · constructor
    · have hpArc : capParam c 0 ∈ c.arcTrace := by
        rw [← capParam_image_Icc_eq_arcTrace]
        refine ⟨0, ?_, rfl⟩
        constructor <;> dsimp [capStart, capEnd] <;>
          nlinarith [c.radius_pos, c.theta_pos]
      have hcircle := hpArc.1
      change circleValue c.center c.radius (capParam c 0) = 0
      unfold circleValue
      unfold OneSidedCircularCap.radiusSquaredAt at hcircle
      nlinarith
    · exact capParam_zero_strict_upper c hside
  · exact circleValue_zero_inter_upper_isPreconnected c.radius_pos

/-- Lower reflected counterpart of exact bounded-open cap saturation. -/
theorem lowerCap_openRepresentative_component_eq
    (c : OneSidedCircularCap) (hside : c.side = .lower) :
    connectedComponentIn
        (frontier (capOpenRepresentative c) ∩
          {q : PlanePoint | q.2 < c.baseY}) (capParam c 0) =
      {q : PlanePoint | circleValue c.center c.radius q = 0} ∩
        {q : PlanePoint | q.2 < c.baseY} := by
  rw [frontier_capOpenRepresentative]
  apply connectedComponentIn_eq_self_of_isPreconnected
  · constructor
    · have hpArc : capParam c 0 ∈ c.arcTrace := by
        rw [← capParam_image_Icc_eq_arcTrace]
        refine ⟨0, ?_, rfl⟩
        constructor <;> dsimp [capStart, capEnd] <;>
          nlinarith [c.radius_pos, c.theta_pos]
      have hcircle := hpArc.1
      change circleValue c.center c.radius (capParam c 0) = 0
      unfold circleValue
      unfold OneSidedCircularCap.radiusSquaredAt at hcircle
      nlinarith
    · exact capParam_zero_strict_lower c hside
  · exact circleValue_zero_inter_lower_isPreconnected c.radius_pos

/-- Independent bounded-open minor representative application. -/
theorem minor_openRepresentative_component_eq :
    connectedComponentIn
        (frontier (capOpenRepresentative minor) ∩
          {q : PlanePoint | 1 < q.2}) (capParam minor 0) =
      {q : PlanePoint | circleValue minor.center minor.radius q = 0} ∩
        {q : PlanePoint | 1 < q.2} :=
  upperDisk_atlas_component_eq minor rfl rfl
    (by rw [minor_cos_theta])
    (by rw [minor_cos_theta]; norm_num)

/-- Independent bounded-open major representative application. -/
theorem major_openRepresentative_component_eq :
    connectedComponentIn
        (frontier (capOpenRepresentative major) ∩
          {q : PlanePoint | 1 < q.2}) (capParam major 0) =
      {q : PlanePoint | circleValue major.center major.radius q = 0} ∩
        {q : PlanePoint | 1 < q.2} :=
  upperDisk_atlas_component_eq major rfl rfl
    (by rw [major_cos_theta]; norm_num)
    (by rw [major_cos_theta])
private theorem major_rightEquator_mem_interval :
    major.radius * (Real.pi / 2) ∈
      Icc (capStart major) (capEnd major) := by
  have hproduct : 0 < major.radius * Real.pi :=
    mul_pos major.radius_pos Real.pi_pos
  constructor
  · change -major.radius * (2 * Real.pi / 3) ≤
      major.radius * (Real.pi / 2)
    nlinarith
  · change major.radius * (Real.pi / 2) ≤
      major.radius * (2 * Real.pi / 3)
    nlinarith

private theorem major_leftEquator_mem_interval :
    -(major.radius * (Real.pi / 2)) ∈
      Icc (capStart major) (capEnd major) := by
  have hproduct : 0 < major.radius * Real.pi :=
    mul_pos major.radius_pos Real.pi_pos
  constructor
  · change -major.radius * (2 * Real.pi / 3) ≤
      -(major.radius * (Real.pi / 2))
    nlinarith
  · change -(major.radius * (Real.pi / 2)) ≤
      major.radius * (2 * Real.pi / 3)
    nlinarith

/-- The exact major-cap component crosses both vertical-coordinate tangencies,
at angular parameters `-pi/2` and `pi/2`; neither point is lost at a chart
switch. -/
theorem major_equator_points_mem_complete_component :
    capParam major (-(major.radius * (Real.pi / 2))) ∈
        connectedComponentIn major.arcTrace (capParam major 0) ∧
      capParam major (major.radius * (Real.pi / 2)) ∈
        connectedComponentIn major.arcTrace (capParam major 0) := by
  rw [cap_connectedComponentIn_eq_arcTrace]
  constructor
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨_, major_leftEquator_mem_interval, rfl⟩
  · rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨_, major_rightEquator_mem_interval, rfl⟩

private theorem major_equator_mem_exteriorClip
    {s : ℝ} (hs : s ∈ Icc (capStart major) (capEnd major))
    (hangle : s / major.radius = Real.pi / 2 ∨
      s / major.radius = -(Real.pi / 2)) :
    capParam major s ∈
      {q : PlanePoint | circleValue major.center major.radius q = 0} ∩
        {q : PlanePoint | 1 < q.2} := by
  have hpArc : capParam major s ∈ major.arcTrace := by
    rw [← capParam_image_Icc_eq_arcTrace]
    exact ⟨s, hs, rfl⟩
  have hcircle :
      circleValue major.center major.radius (capParam major s) = 0 := by
    have h := hpArc.1
    change circleValue major.center major.radius (capParam major s) = 0
    unfold circleValue
    unfold OneSidedCircularCap.radiusSquaredAt at h
    nlinarith
  have hcosTheta : Real.cos major.theta < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · dsimp only [major]
      nlinarith [Real.pi_pos]
    · dsimp only [major]
      nlinarith [Real.pi_pos]
  refine ⟨hcircle, ?_⟩
  rcases hangle with hangle | hangle
  · unfold capParam OneSidedCircularCap.arcPoint
    rw [show major.side = .upper from rfl]
    simp only [Set.mem_ofPred_eq]
    change 1 < 1 + major.radius *
      (Real.cos (s / major.radius) - Real.cos major.theta)
    rw [hangle, Real.cos_pi_div_two]
    nlinarith [major.radius_pos]
  · unfold capParam OneSidedCircularCap.arcPoint
    rw [show major.side = .upper from rfl]
    simp only [Set.mem_ofPred_eq]
    change 1 < 1 + major.radius *
      (Real.cos (s / major.radius) - Real.cos major.theta)
    rw [hangle, Real.cos_neg, Real.cos_pi_div_two]
    nlinarith [major.radius_pos]

/-- The bounded-open major representative's actual exterior-frontier
component contains both vertical-coordinate tangencies. -/
theorem major_equator_points_mem_openRepresentative_component :
    capParam major (-(major.radius * (Real.pi / 2))) ∈
        connectedComponentIn
          (frontier (capOpenRepresentative major) ∩
            {q : PlanePoint | 1 < q.2}) (capParam major 0) ∧
      capParam major (major.radius * (Real.pi / 2)) ∈
        connectedComponentIn
          (frontier (capOpenRepresentative major) ∩
            {q : PlanePoint | 1 < q.2}) (capParam major 0) := by
  rw [major_openRepresentative_component_eq]
  have hradius : major.radius ≠ 0 := major.radius_pos.ne'
  constructor
  · apply major_equator_mem_exteriorClip major_leftEquator_mem_interval
    right
    field_simp
  · apply major_equator_mem_exteriorClip major_rightEquator_mem_interval
    left
    field_simp

/-- Minor, major, reflected, and translated cap representatives all satisfy
complete component saturation. -/
theorem complete_component_saturation :
    connectedComponentIn minor.arcTrace (capParam minor 0) = minor.arcTrace ∧
      connectedComponentIn major.arcTrace (capParam major 0) = major.arcTrace ∧
      connectedComponentIn reflectedMajor.arcTrace
          (capParam reflectedMajor 0) = reflectedMajor.arcTrace ∧
      connectedComponentIn translatedMinor.arcTrace
          (capParam translatedMinor 0) = translatedMinor.arcTrace :=
  ⟨cap_connectedComponentIn_eq_arcTrace minor,
    cap_connectedComponentIn_eq_arcTrace major,
    cap_connectedComponentIn_eq_arcTrace reflectedMajor,
    cap_connectedComponentIn_eq_arcTrace translatedMinor⟩

end CapApplications

end CMVExteriorMaximalArc
