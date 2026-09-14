import CMVRegularGermExtension

/-!
# Regular-germ interface-extension splice

This module transports the reference `interfaceExtendedOpenCorner` through the
actual corner chart.  The source hypotheses describe only the unchanged
representative, the signed physical continuation of its interface germ, and the
physical phase reached on the incident side.  The replacement, collar,
frontier, cost, and area estimates are derived below.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

/-- The chart's signed interface axis remains on the same physical strip
interface.  This is geometry of the unchanged source chart, not a supplied
replacement trace. -/
structure SignedInterfaceApplicability (A : RegularCornerChartApplicability C) : Prop where
  signed_interface_on_strip :
    ∀ t ∈ Icc (-A.localRadius) A.localRadius,
      (A.chart (0, t)).2 = side.height

/-- The physical constant-density phase on the full signed incident-side
sector needed by the extension connector.  Unlike `PhysicalPhaseApplicability`,
the second coordinate may be negative. -/
structure SignedIncidentPhaseApplicability
    (A : RegularCornerChartApplicability C) where
  phase : LocalTracePhase
  signed_right_sector_phase :
    ∀ q ∈ openLocalizationSquare (0, 0) A.localRadius,
      0 < q.1 → phase.Contains (A.chart q)

/-- Region where the extension model and the old quadrant agree. -/
def extensionInactiveRegion (r : ℝ) : Set PlanePoint :=
  {q | q.1 < 0} ∪ {q | r < q.1} ∪ {q | 0 < q.2} ∪ {q | q.2 < -r}

lemma isOpen_extensionInactiveRegion (r : ℝ) :
    IsOpen (extensionInactiveRegion r) := by
  exact (((isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_const continuous_fst)).union
      (isOpen_lt continuous_const continuous_snd)).union
        (isOpen_lt continuous_snd continuous_const)

lemma extensionFloor_self {r u : ℝ} (hr : 0 < r) :
    extensionFloor r r u = min (u - r) 0 := by
  rw [extensionFloor, div_self hr.ne']
  congr 1
  ring

/-- On the inactive region the reference extension is literally the unchanged
open quadrant. -/
theorem openCorner_inter_extensionInactiveRegion {r : ℝ} (hr : 0 < r) :
    openCorner ∩ extensionInactiveRegion r =
      interfaceExtendedOpenCorner r r ∩ extensionInactiveRegion r := by
  ext q
  simp only [mem_inter_iff, extensionInactiveRegion, mem_union, mem_ofPred_eq,
    openCorner, mem_interfaceExtendedOpenCorner]
  constructor
  · rintro ⟨hq, hinactive⟩
    refine ⟨⟨hq.1, ?_⟩, hinactive⟩
    exact lt_of_le_of_lt (min_le_right _ _) hq.2
  · rintro ⟨hq, hinactive⟩
    refine ⟨⟨hq.1, ?_⟩, hinactive⟩
    rcases hinactive with ((hneg | hright) | hup) | hdown
    · exact (not_lt_of_ge hq.1.le hneg).elim
    · rw [extensionFloor_eq_zero hr hr.le hright.le] at hq
      exact hq.2
    · exact hup
    · have hlower : -r ≤ extensionFloor r r q.1 := by
        rw [extensionFloor_self hr]
        exact le_min (by linarith [hq.1]) (neg_nonpos.mpr hr.le)
      linarith

/-- Actual open local extension model. -/
def extensionLocalModel (r : ℝ) : Set PlanePoint :=
  A.chart '' interfaceExtendedOpenCorner r r

/-- Derived collar on which the old and new local models agree. -/
def extensionCollar (r : ℝ) : Set PlanePoint :=
  A.chart ''
    (openLocalizationSquare (0, 0) A.localRadius ∩
      extensionInactiveRegion r)

/-- Same-representative localized interface-extension competitor. -/
def extensionCompetitor (r : ℝ) : Set PlanePoint :=
  localizedCompetitor C.representative (A.extensionLocalModel r) (A.window r)

lemma isOpen_extensionLocalModel (r : ℝ) : IsOpen (A.extensionLocalModel r) :=
  A.chart.isOpenMap _ (isOpen_interfaceExtendedOpenCorner r r)

lemma isOpen_extensionCollar (r : ℝ) : IsOpen (A.extensionCollar r) :=
  A.chart.isOpenMap _
    ((isOpen_openLocalizationSquare (0, 0) A.localRadius).inter
      (isOpen_extensionInactiveRegion r))

/-- Every localization-boundary point lies in the derived agreement collar. -/
theorem frontier_window_subset_extensionCollar {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.window r) ⊆ A.extensionCollar r := by
  rw [window, ← A.chart.image_frontier]
  rintro _ ⟨q, hq, rfl⟩
  have hqClosed : q ∈ A.coordinateWindow r :=
    (by
      exact (isClosed_Icc.prod isClosed_Icc).frontier_subset hq)
  have hqOpen :
      q ∈ openLocalizationSquare (0, 0) A.localRadius := by
    rw [coordinateWindow, closedCutRectangle] at hqClosed
    simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
    rcases hqClosed with ⟨hx, hy⟩
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hy with ⟨hylo, hyhi⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  refine ⟨q, ⟨hqOpen, ?_⟩, rfl⟩
  change (((q.1 < 0 ∨ r < q.1) ∨ 0 < q.2) ∨ q.2 < -r)
  have hfaces := frontier_closedCutRectangle_subset_lines
    (by linarith : -2 * r < 2 * r) (by linarith : -2 * r < 2 * r) hq
  rcases hfaces with ((hxneg | hxpos) | hyneg) | hypos
  · left; left; left
    have hx : q.1 = -2 * r := by simpa [verticalLine] using hxneg
    linarith
  · left; left; right
    have hx : q.1 = 2 * r := by simpa [verticalLine] using hxpos
    linarith
  · right
    have hy : q.2 = -2 * r := by simpa [horizontalLine] using hyneg
    linarith
  · left; right
    have hy : q.2 = 2 * r := by simpa [horizontalLine] using hypos
    linarith

/-- Collar agreement follows from the unchanged representative's occupied
quadrant and the constructed extension model. -/
theorem representative_inter_extensionCollar_eq_extensionLocalModel
    {r : ℝ} (hr : 0 < r) :
    C.representative ∩ A.extensionCollar r =
      A.extensionLocalModel r ∩ A.extensionCollar r := by
  ext p
  constructor
  · rintro ⟨hpU, q, hq, rfl⟩
    have hqOld : q ∈ openCorner :=
      (A.representative_local q hq.1).mp hpU
    have hqNew : q ∈ interfaceExtendedOpenCorner r r := by
      have hmem : q ∈ openCorner ∩ extensionInactiveRegion r := ⟨hqOld, hq.2⟩
      rw [openCorner_inter_extensionInactiveRegion hr] at hmem
      exact hmem.1
    exact ⟨⟨q, hqNew, rfl⟩, ⟨q, hq, rfl⟩⟩
  · rintro ⟨⟨q, hqNew, hqp⟩, ⟨z, hz, hzp⟩⟩
    have hqz : q = z := A.chart.injective (hqp.trans hzp.symm)
    subst z
    subst p
    have hmem : q ∈ interfaceExtendedOpenCorner r r ∩
        extensionInactiveRegion r := ⟨hqNew, hz.2⟩
    rw [← openCorner_inter_extensionInactiveRegion hr] at hmem
    exact ⟨(A.representative_local q hz.1).mpr hmem.1, ⟨q, hz, rfl⟩⟩

/-- Coordinate pieces of the extension frontier inside the scale window. -/
def extensionRetainedIncidentPiece (r : ℝ) : Set PlanePoint :=
  {q | r ≤ q.1 ∧ q.1 < 2 * r ∧ q.2 = 0}

def extensionPositiveInterfacePiece (r : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ 0 ≤ q.2 ∧ q.2 < 2 * r}

private theorem frontier_extension_inter_coordinateWindow {r : ℝ} (hr : 0 < r) :
    frontier (interfaceExtendedOpenCorner r r) ∩ interior (A.coordinateWindow r) =
      extensionRetainedIncidentPiece r ∪ extensionPositiveInterfacePiece r ∪
        negativeInterfaceSegment r ∪ extensionConnector r r := by
  rw [frontier_interfaceExtendedOpenCorner_four_pieces hr hr]
  ext q
  rw [coordinateWindow, closedCutRectangle, interior_prod_eq]
  simp only [interior_Icc, mem_inter_iff, mem_union, mem_prod, mem_Ioo,
    retainedIncidentRay, retainedInterfaceRay, negativeInterfaceSegment,
    extensionConnector, extensionRetainedIncidentPiece,
    extensionPositiveInterfacePiece, mem_ofPred_eq]
  constructor
  · rintro ⟨((hincident | hpositive) | hnegative) | hconnector, hx, hy⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hincident.1, hx.2, hincident.2⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hpositive.1, hpositive.2, hy.2⟩))
    · exact Or.inl (Or.inr hnegative)
    · exact Or.inr hconnector
  · rintro (((hincident | hpositive) | hnegative) | hconnector)
    · refine ⟨Or.inl (Or.inl (Or.inl ⟨hincident.1, hincident.2.2⟩)),
        ⟨by linarith [hr, hincident.1], hincident.2.1⟩, ?_⟩
      rw [hincident.2.2]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨Or.inl (Or.inl (Or.inr ⟨hpositive.1, hpositive.2.1⟩)), ?_,
        ⟨by linarith [hr, hpositive.2.1], hpositive.2.2⟩⟩
      rw [hpositive.1]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨Or.inl (Or.inr hnegative), ?_, ?_⟩
      · rw [hnegative.1]
        exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith [hnegative.2.1], by linarith [hnegative.2.2]⟩
    · rcases hconnector with ⟨hu0, hur, hv⟩
      have hdiv : r / r = (1 : ℝ) := div_self hr.ne'
      refine ⟨Or.inr ⟨hu0, hur, hv⟩, ?_, ?_⟩
      · exact ⟨by linarith, by linarith⟩
      · rw [hdiv] at hv
        exact ⟨by nlinarith, by nlinarith⟩

/-- Actual retained incident germ. -/
def extensionRetainedIncidentTrace
    (_A : RegularCornerChartApplicability C) (r : ℝ) : Set PlanePoint :=
  C.incident.curve '' Ico r (2 * r)

/-- The unchanged positive interface germ. -/
def extensionPositiveInterfaceTrace
    (_A : RegularCornerChartApplicability C) (r : ℝ) : Set PlanePoint :=
  C.interface.curve '' Ico 0 (2 * r)

/-- Newly exposed signed continuation of the interface. -/
def extensionNegativeInterfaceTrace (r : ℝ) : Set PlanePoint :=
  A.chart '' negativeInterfaceSegment r

/-- Inserted joining trace. -/
def extensionConnectorTrace (r : ℝ) : Set PlanePoint :=
  A.chart '' extensionConnector r r

private theorem image_extensionRetainedIncidentPiece {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' extensionRetainedIncidentPiece r =
      A.extensionRetainedIncidentTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.1, ⟨hq.1, hq.2.1⟩, ?_⟩
    calc
      C.incident.curve q.1 = A.chart (q.1, 0) :=
        (A.incident_axis q.1 ⟨by linarith [hr, hq.1],
          hq.2.1.le.trans hlocal.le⟩).symm
      _ = A.chart q := by congr 1; exact Prod.ext rfl hq.2.2.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t, 0), ⟨ht.1, ht.2, rfl⟩, ?_⟩
    exact A.incident_axis t ⟨by linarith [hr, ht.1], ht.2.le.trans hlocal.le⟩

private theorem image_extensionPositiveInterfacePiece {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' extensionPositiveInterfacePiece r =
      A.extensionPositiveInterfaceTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, ⟨hq.2.1, hq.2.2⟩, ?_⟩
    calc
      C.interface.curve q.2 = A.chart (0, q.2) :=
        (A.interface_axis q.2 ⟨hq.2.1, hq.2.2.le.trans hlocal.le⟩).symm
      _ = A.chart q := by congr 1; exact Prod.ext hq.1.symm rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(0, t), ⟨rfl, ht.1, ht.2⟩, ?_⟩
    exact A.interface_axis t ⟨ht.1, ht.2.le.trans hlocal.le⟩

/-- Complete inserted and retained frontier of the actual extension model. -/
theorem extensionLocalModel_frontier_inside_window {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.extensionLocalModel r) ∩ interior (A.window r) =
      A.extensionRetainedIncidentTrace r ∪
        A.extensionPositiveInterfaceTrace r ∪
          A.extensionNegativeInterfaceTrace r ∪ A.extensionConnectorTrace r := by
  calc
    frontier (A.extensionLocalModel r) ∩ interior (A.window r) =
        A.chart '' (frontier (interfaceExtendedOpenCorner r r) ∩
          interior (A.coordinateWindow r)) := by
      rw [extensionLocalModel, window, ← A.chart.image_frontier,
        ← A.chart.image_interior, ← Set.image_inter A.chart.injective]
    _ = A.chart '' (extensionRetainedIncidentPiece r ∪
        extensionPositiveInterfacePiece r ∪ negativeInterfaceSegment r ∪
          extensionConnector r r) := by
      rw [A.frontier_extension_inter_coordinateWindow hr]
    _ = _ := by
      rw [image_union, image_union, image_union,
        A.image_extensionRetainedIncidentPiece hr hlocal,
        A.image_extensionPositiveInterfacePiece hr hlocal]
      rfl

lemma isOpen_extensionCompetitor (r : ℝ) : IsOpen (A.extensionCompetitor r) :=
  localizedCompetitor_isOpen _ _ _

lemma isBounded_extensionCompetitor (r : ℝ) :
    Bornology.IsBounded (A.extensionCompetitor r) :=
  localizedCompetitor_isBounded C.representative_isBounded (A.isBounded_window r)

/-- Complete frontier accounting for the actual localized extension splice. -/
theorem extensionCompetitor_frontier {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.extensionCompetitor r) =
      (A.extensionRetainedIncidentTrace r ∪
        A.extensionPositiveInterfaceTrace r ∪
          A.extensionNegativeInterfaceTrace r ∪ A.extensionConnectorTrace r) ∪
        (frontier C.representative ∩ (interior (A.window r))ᶜ) := by
  rw [extensionCompetitor]
  have h := localizedCompetitor_frontier_eq_piecewise
    C.representative_isOpen (A.isOpen_extensionLocalModel r) (A.isClosed_window r)
    (A.closure_interior_window hr) (A.isOpen_extensionCollar r)
    (A.frontier_window_subset_extensionCollar hr hlocal)
    (A.representative_inter_extensionCollar_eq_extensionLocalModel hr)
  rw [A.extensionLocalModel_frontier_inside_window hr hlocal] at h
  exact h

/-- Exact complete-cost decomposition of the actual localized extension. -/
theorem extensionCompetitor_complete_cost (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    smoothCost lam (A.extensionCompetitor r) =
      smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) +
        smoothCostOn lam C.representative (interior (A.window r))ᶜ := by
  exact localizedCompetitor_complete_cost lam C.representative_isOpen
    (A.isOpen_extensionLocalModel r) (A.isClosed_window r)
    (A.closure_interior_window hr) (A.isOpen_extensionCollar r)
    (A.frontier_window_subset_extensionCollar hr hlocal)
    (A.representative_inter_extensionCollar_eq_extensionLocalModel hr)

/-- Exact exterior agreement; all changes are localized in the existing
window. -/
theorem extensionCompetitor_agrees_outside {r : ℝ} :
    A.extensionCompetitor r ∩ (A.window r)ᶜ =
        C.representative ∩ (A.window r)ᶜ ∧
      frontier (A.extensionCompetitor r) ∩ interior (A.window r)ᶜ =
        frontier C.representative ∩ interior (A.window r)ᶜ :=
  localizedCompetitor_agrees_outside C.representative_isOpen
    (A.isOpen_extensionLocalModel r) (A.isClosed_window r)

/-- The extension splice has a finite, scale-independent quadratic signed
weighted-area bound. -/
theorem extensionCompetitor_weightedArea_defect_le {lam r : ℝ}
    (hlam : 1 ≤ lam) (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    |WeightedArea lam (A.extensionCompetitor r) -
        WeightedArea lam C.representative| ≤
      4 * lam * (4 * A.coordinateBound) ^ 2 * r ^ 2 := by
  exact localizedCompetitor_weightedArea_defect_le hlam
    (mul_nonneg (by norm_num) A.coordinateBound_pos.le) hr.le
    C.representative_isOpen (A.isOpen_extensionLocalModel r) (A.isClosed_window r)
    C.representative_isBounded (A.isBounded_window r)
    (A.window_subset_localizationSquare hlocal)

end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison

namespace CMVRelaxation.RegularTraceCornerComparison
namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

namespace SignedIncidentPhaseApplicability

/-- Forgetting the signed-coordinate strengthening recovers the retained
positive-sector phase interface. -/
def toPhysical (P : SignedIncidentPhaseApplicability A) :
    PhysicalPhaseApplicability A where
  phase := P.phase
  chart_sector_phase := by
    intro q hq hqFirst _hqSecond
    exact P.signed_right_sector_phase q hq hqFirst

end SignedIncidentPhaseApplicability

/-- Parameterization of the newly exposed interface continuation. -/
def extensionNegativeInterfaceParam (r t : ℝ) : PlanePoint :=
  A.chart (0, -t)

/-- Parameterization of the joining trace from the negative interface endpoint
to the retained incident endpoint. -/
def extensionConnectorParam (r t : ℝ) : PlanePoint :=
  A.chart (t, t - r)

lemma continuous_extensionNegativeInterfaceParam (r : ℝ) :
    Continuous (A.extensionNegativeInterfaceParam r) :=
  A.chart.continuous.comp (continuous_const.prodMk continuous_id.neg)

lemma continuous_extensionConnectorParam (r : ℝ) :
    Continuous (A.extensionConnectorParam r) :=
  A.chart.continuous.comp (continuous_id.prodMk (continuous_id.sub continuous_const))

theorem extensionNegativeInterfaceTrace_eq_image_Icc {r : ℝ} (hr : 0 ≤ r) :
    A.extensionNegativeInterfaceTrace r =
      A.extensionNegativeInterfaceParam r '' Icc 0 r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨-q.2, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩, ?_⟩
    unfold extensionNegativeInterfaceParam
    congr 1
    apply Prod.ext hq.1.symm
    simp
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(0, -t), ⟨rfl, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩

theorem extensionConnectorTrace_eq_image_Icc {r : ℝ} (hr : 0 < r) :
    A.extensionConnectorTrace r =
      A.extensionConnectorParam r '' Icc 0 r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.1, ⟨hq.1, hq.2.1⟩, ?_⟩
    unfold extensionConnectorParam
    congr 1
    simp only [extensionConnector, mem_ofPred_eq] at hq
    apply Prod.ext
    · rfl
    · rw [div_self hr.ne'] at hq
      linarith [hq.2.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t, t - r), ⟨ht.1, ht.2, ?_⟩, rfl⟩
    rw [div_self hr.ne']
    ring

lemma measurableSet_extensionNegativeInterfaceTrace {r : ℝ} (hr : 0 ≤ r) :
    MeasurableSet (A.extensionNegativeInterfaceTrace r) := by
  rw [A.extensionNegativeInterfaceTrace_eq_image_Icc hr]
  exact (isCompact_Icc.image
    (A.continuous_extensionNegativeInterfaceParam r)).measurableSet

lemma measurableSet_extensionConnectorTrace {r : ℝ} (hr : 0 < r) :
    MeasurableSet (A.extensionConnectorTrace r) := by
  rw [A.extensionConnectorTrace_eq_image_Icc hr]
  exact (isCompact_Icc.image
    (A.continuous_extensionConnectorParam r)).measurableSet

private theorem retainedIncident_inter_positiveInterface_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.extensionRetainedIncidentTrace r ∩
      A.extensionPositiveInterfaceTrace r).Finite := by
  rw [← A.image_extensionRetainedIncidentPiece hr hlocal,
    ← A.image_extensionPositiveInterfacePiece hr hlocal,
    ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply Set.finite_empty.subset
  rintro q ⟨hqI, hqF⟩
  exfalso
  linarith [hqI.1, hqF.1]

private theorem retainedIncident_inter_negativeInterface_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.extensionRetainedIncidentTrace r ∩
      A.extensionNegativeInterfaceTrace r).Finite := by
  rw [← A.image_extensionRetainedIncidentPiece hr hlocal,
    extensionNegativeInterfaceTrace, ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply Set.finite_empty.subset
  rintro q ⟨hqI, hqN⟩
  exfalso
  linarith [hqI.1, hqN.1]

private theorem positiveInterface_inter_negativeInterface_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.extensionPositiveInterfaceTrace r ∩
      A.extensionNegativeInterfaceTrace r).Finite := by
  rw [← A.image_extensionPositiveInterfacePiece hr hlocal,
    extensionNegativeInterfaceTrace, ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply (Set.finite_singleton ((0, 0) : PlanePoint)).subset
  rintro q ⟨hqP, hqN⟩
  rw [mem_singleton_iff]
  apply Prod.ext hqP.1
  linarith [hqP.2.1, hqN.2.2]

private theorem retainedIncident_inter_extensionConnector_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.extensionRetainedIncidentTrace r ∩
      A.extensionConnectorTrace r).Finite := by
  rw [← A.image_extensionRetainedIncidentPiece hr hlocal,
    extensionConnectorTrace, ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply (Set.finite_singleton ((r, 0) : PlanePoint)).subset
  rintro q ⟨hqI, hqK⟩
  rw [mem_singleton_iff]
  simp only [extensionConnector, mem_ofPred_eq] at hqK
  rw [div_self hr.ne'] at hqK
  apply Prod.ext
  · linarith [hqI.2.2, hqK.2.2]
  · exact hqI.2.2

private theorem positiveInterface_inter_extensionConnector_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.extensionPositiveInterfaceTrace r ∩
      A.extensionConnectorTrace r).Finite := by
  rw [← A.image_extensionPositiveInterfacePiece hr hlocal,
    extensionConnectorTrace, ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply Set.finite_empty.subset
  rintro q ⟨hqP, hqK⟩
  simp only [extensionConnector, mem_ofPred_eq] at hqK
  rw [div_self hr.ne'] at hqK
  exfalso
  linarith [hqP.1, hqP.2.1, hqK.2.2]

private theorem negativeInterface_inter_extensionConnector_finite
    {r : ℝ} (hr : 0 < r) :
    (A.extensionNegativeInterfaceTrace r ∩
      A.extensionConnectorTrace r).Finite := by
  rw [extensionNegativeInterfaceTrace, extensionConnectorTrace,
    ← Set.image_inter A.chart.injective]
  apply Set.Finite.image
  apply (Set.finite_singleton ((0, -r) : PlanePoint)).subset
  rintro q ⟨hqN, hqK⟩
  rw [mem_singleton_iff]
  simp only [extensionConnector, mem_ofPred_eq] at hqK
  rw [div_self hr.ne'] at hqK
  apply Prod.ext hqN.1
  have hqFirst : q.1 = 0 := hqN.1
  rw [hqFirst] at hqK
  norm_num at hqK
  exact hqK.2

/-- Exact local cost as the four derived extension-frontier traces. -/
theorem extensionLocalModel_inside_cost_eq_trace_sum
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) =
      weightedTraceCost lam (A.extensionRetainedIncidentTrace r) +
        weightedTraceCost lam (A.extensionPositiveInterfaceTrace r) +
          weightedTraceCost lam (A.extensionNegativeInterfaceTrace r) +
            weightedTraceCost lam (A.extensionConnectorTrace r) := by
  rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam (A.extensionLocalModel r) isOpen_interior.measurableSet,
    A.extensionLocalModel_frontier_inside_window hr hlocal]
  have hRP := A.retainedIncident_inter_positiveInterface_finite hr hlocal
  have hmeasR : MeasurableSet (A.extensionRetainedIncidentTrace r) := by
    simpa [extensionRetainedIncidentTrace, retainedIncidentTrace] using
      A.measurableSet_retainedIncidentTrace hr.le hlocal.le
  have hmeasP : MeasurableSet (A.extensionPositiveInterfaceTrace r) := by
    simpa [extensionPositiveInterfaceTrace, oldInterfaceTrace] using
      A.measurableSet_oldInterfaceTrace hr.le hlocal.le
  have hRPN :
      ((A.extensionRetainedIncidentTrace r ∪
        A.extensionPositiveInterfaceTrace r) ∩
          A.extensionNegativeInterfaceTrace r).Finite := by
    rw [union_inter_distrib_right]
    exact (A.retainedIncident_inter_negativeInterface_finite hr hlocal).union
      (A.positiveInterface_inter_negativeInterface_finite hr hlocal)
  have hRPNK :
      (((A.extensionRetainedIncidentTrace r ∪
        A.extensionPositiveInterfaceTrace r) ∪
          A.extensionNegativeInterfaceTrace r) ∩
            A.extensionConnectorTrace r).Finite := by
    rw [union_inter_distrib_right, union_inter_distrib_right]
    exact ((A.retainedIncident_inter_extensionConnector_finite hr hlocal).union
      (A.positiveInterface_inter_extensionConnector_finite hr hlocal)).union
        (A.negativeInterface_inter_extensionConnector_finite hr)
  rw [CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      ((hmeasR.union hmeasP).union
          (A.measurableSet_extensionNegativeInterfaceTrace hr.le))
      (A.measurableSet_extensionConnectorTrace hr) hRPNK,
    CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      (hmeasR.union hmeasP)
      (A.measurableSet_extensionNegativeInterfaceTrace hr.le) hRPN,
    CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      hmeasR hmeasP hRP,
    add_assoc]

/-- Differential data needed for the two literal extension traces. -/
structure ExtensionMetricApplicability
    (A : RegularCornerChartApplicability C) : Prop where
  chart_contDiff : ContDiff ℝ 1 A.chart
  fderiv_incident :
    fderiv ℝ A.chart (0, 0) (1, 0) = C.incident.velocity
  fderiv_interface :
    fderiv ℝ A.chart (0, 0) (0, 1) = C.interface.velocity
  connectorVelocitySum_ne :
    (C.incident.velocity.1 + C.interface.velocity.1,
      C.incident.velocity.2 + C.interface.velocity.2) ≠ (0, 0)

namespace ExtensionMetricApplicability

variable (M : ExtensionMetricApplicability A)

def negativeInterfaceSpeedAt
    (_M : ExtensionMetricApplicability A) (q : PlanePoint) : ℝ :=
  Real.sqrt (((fderiv ℝ A.chart q (0, -1)).1) ^ 2 +
    ((fderiv ℝ A.chart q (0, -1)).2) ^ 2)

def extensionConnectorSpeedAt
    (_M : ExtensionMetricApplicability A) (q : PlanePoint) : ℝ :=
  Real.sqrt (((fderiv ℝ A.chart q (1, 1)).1) ^ 2 +
    ((fderiv ℝ A.chart q (1, 1)).2) ^ 2)

def negativeInterfaceArcLength
    (_M : ExtensionMetricApplicability A) (r : ℝ) : ℝ :=
  ∫ t in 0..r, euclideanParametricSpeed
    (A.extensionNegativeInterfaceParam r) t

def extensionConnectorArcLength
    (_M : ExtensionMetricApplicability A) (r : ℝ) : ℝ :=
  ∫ t in 0..r, euclideanParametricSpeed
    (A.extensionConnectorParam r) t

lemma negativeInterfaceParam_contDiff
    (M : ExtensionMetricApplicability A) (r : ℝ) :
    ContDiff ℝ 1 (A.extensionNegativeInterfaceParam r) :=
  (ExtensionMetricApplicability.chart_contDiff M).comp
    (contDiff_const.prodMk contDiff_id.neg)

lemma extensionConnectorParam_contDiff
    (M : ExtensionMetricApplicability A) (r : ℝ) :
    ContDiff ℝ 1 (A.extensionConnectorParam r) :=
  (ExtensionMetricApplicability.chart_contDiff M).comp
    (contDiff_id.prodMk (contDiff_id.sub contDiff_const))

lemma negativeInterfaceParam_hasDerivAt
    (M : ExtensionMetricApplicability A) (r t : ℝ) :
    HasDerivAt (A.extensionNegativeInterfaceParam r)
      (fderiv ℝ A.chart (0, -t) (0, -1)) t := by
  have hin : HasDerivAt
      (fun s : ℝ => ((0 : ℝ), -s)) ((0, -1) : PlanePoint) t := by
    convert (hasDerivAt_const (x := t) (c := (0 : ℝ))).prodMk
      (hasDerivAt_id t).neg using 1 <;> norm_num [Pi.neg_apply, id_eq]
  exact
    ((ExtensionMetricApplicability.chart_contDiff M).differentiable
      (by norm_num) (0, -t)).hasFDerivAt.comp_hasDerivAt t hin

lemma extensionConnectorParam_hasDerivAt
    (M : ExtensionMetricApplicability A) (r t : ℝ) :
    HasDerivAt (A.extensionConnectorParam r)
      (fderiv ℝ A.chart (t, t - r) (1, 1)) t := by
  have hin : HasDerivAt (fun s : ℝ => (s, s - r)) (1, 1) t := by
    convert (hasDerivAt_id t).prodMk
      ((hasDerivAt_id t).sub_const r) using 1 <;> norm_num [Pi.sub_apply, id_eq]
  exact
    ((ExtensionMetricApplicability.chart_contDiff M).differentiable
      (by norm_num) (t, t - r)).hasFDerivAt.comp_hasDerivAt t hin

lemma euclideanParametricSpeed_negativeInterfaceParam (r t : ℝ) :
    euclideanParametricSpeed (A.extensionNegativeInterfaceParam r) t =
      M.negativeInterfaceSpeedAt (0, -t) := by
  have h := M.negativeInterfaceParam_hasDerivAt r t
  have hx : deriv (fun s => (A.extensionNegativeInterfaceParam r s).1) t =
      (fderiv ℝ A.chart (0, -t) (0, -1)).1 := by
    simpa using h.hasFDerivAt.fst.hasDerivAt.deriv
  have hy : deriv (fun s => (A.extensionNegativeInterfaceParam r s).2) t =
      (fderiv ℝ A.chart (0, -t) (0, -1)).2 := by
    simpa using h.hasFDerivAt.snd.hasDerivAt.deriv
  unfold euclideanParametricSpeed negativeInterfaceSpeedAt
  rw [hx, hy]

lemma euclideanParametricSpeed_extensionConnectorParam (r t : ℝ) :
    euclideanParametricSpeed (A.extensionConnectorParam r) t =
      M.extensionConnectorSpeedAt (t, t - r) := by
  have h := M.extensionConnectorParam_hasDerivAt r t
  have hx : deriv (fun s => (A.extensionConnectorParam r s).1) t =
      (fderiv ℝ A.chart (t, t - r) (1, 1)).1 := by
    simpa using h.hasFDerivAt.fst.hasDerivAt.deriv
  have hy : deriv (fun s => (A.extensionConnectorParam r s).2) t =
      (fderiv ℝ A.chart (t, t - r) (1, 1)).2 := by
    simpa using h.hasFDerivAt.snd.hasDerivAt.deriv
  unfold euclideanParametricSpeed extensionConnectorSpeedAt
  rw [hx, hy]

lemma continuous_negativeInterfaceSpeedAt :
    Continuous M.negativeInterfaceSpeedAt := by
  have hD : Continuous (fun q => fderiv ℝ A.chart q (0, -1)) :=
    ((ExtensionMetricApplicability.chart_contDiff M).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  exact ((hD.fst.pow 2).add (hD.snd.pow 2)).sqrt

lemma continuous_extensionConnectorSpeedAt :
    Continuous M.extensionConnectorSpeedAt := by
  have hD : Continuous (fun q => fderiv ℝ A.chart q (1, 1)) :=
    ((ExtensionMetricApplicability.chart_contDiff M).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  exact ((hD.fst.pow 2).add (hD.snd.pow 2)).sqrt

lemma fderiv_negativeInterface_zero
    (M : ExtensionMetricApplicability A) :
    fderiv ℝ A.chart (0, 0) (0, -1) =
      (-C.interface.velocity.1, -C.interface.velocity.2) := by
  have hv : ((0, -1) : PlanePoint) = -((0, 1) : PlanePoint) := by ext <;> norm_num
  rw [hv, map_neg, ExtensionMetricApplicability.fderiv_interface M]
  rfl

lemma fderiv_extensionConnector_zero
    (M : ExtensionMetricApplicability A) :
    fderiv ℝ A.chart (0, 0) (1, 1) =
      (C.incident.velocity.1 + C.interface.velocity.1,
        C.incident.velocity.2 + C.interface.velocity.2) := by
  have hv : ((1, 1) : PlanePoint) =
      ((1, 0) : PlanePoint) + (0, 1) := by ext <;> norm_num
  rw [hv, map_add, ExtensionMetricApplicability.fderiv_incident M,
    ExtensionMetricApplicability.fderiv_interface M]
  rfl

lemma negativeInterfaceSpeedAt_zero :
    M.negativeInterfaceSpeedAt (0, 0) =
      euclideanSpeed C.interface.velocity := by
  rw [negativeInterfaceSpeedAt, M.fderiv_negativeInterface_zero]
  unfold euclideanSpeed complexVector
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma extensionConnectorSpeedAt_zero :
    M.extensionConnectorSpeedAt (0, 0) =
      euclideanSpeed
        (C.incident.velocity.1 + C.interface.velocity.1,
          C.incident.velocity.2 + C.interface.velocity.2) := by
  rw [extensionConnectorSpeedAt, M.fderiv_extensionConnector_zero]
  unfold euclideanSpeed complexVector
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma negativeInterfaceSpeedAt_zero_pos :
    0 < M.negativeInterfaceSpeedAt (0, 0) := by
  rw [M.negativeInterfaceSpeedAt_zero]
  exact euclideanSpeed_pos C.interface.velocity_ne

lemma extensionConnectorSpeedAt_zero_pos :
    0 < M.extensionConnectorSpeedAt (0, 0) := by
  rw [M.extensionConnectorSpeedAt_zero]
  exact euclideanSpeed_pos
    (ExtensionMetricApplicability.connectorVelocitySum_ne M)

theorem exists_extensionMetricRadius
    (M : ExtensionMetricApplicability A) :
    ∃ ρ > 0, ∀ r ∈ Ioc 0 ρ,
      (∀ t ∈ Icc 0 r,
        0 < euclideanParametricSpeed (A.extensionNegativeInterfaceParam r) t) ∧
      (∀ t ∈ Icc 0 r,
        0 < euclideanParametricSpeed (A.extensionConnectorParam r) t) := by
  have hneg : ∀ᶠ q in 𝓝 ((0, 0) : PlanePoint),
      0 < M.negativeInterfaceSpeedAt q :=
    M.continuous_negativeInterfaceSpeedAt.continuousAt.eventually
      (Ioi_mem_nhds M.negativeInterfaceSpeedAt_zero_pos)
  have hconn : ∀ᶠ q in 𝓝 ((0, 0) : PlanePoint),
      0 < M.extensionConnectorSpeedAt q :=
    M.continuous_extensionConnectorSpeedAt.continuousAt.eventually
      (Ioi_mem_nhds M.extensionConnectorSpeedAt_zero_pos)
  rw [Metric.eventually_nhds_iff] at hneg hconn
  obtain ⟨εn, hεn, hn⟩ := hneg
  obtain ⟨εc, hεc, hc⟩ := hconn
  let ρ := min εn εc / 2
  have hρ : 0 < ρ := half_pos (lt_min hεn hεc)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr
  have hρn : ρ < εn := by
    exact (half_lt_self (lt_min hεn hεc)).trans_le (min_le_left εn εc)
  have hρc : ρ < εc := by
    exact (half_lt_self (lt_min hεn hεc)).trans_le (min_le_right εn εc)
  have hrn : r < εn := hr.2.trans_lt hρn
  have hrc : r < εc := hr.2.trans_lt hρc
  constructor
  · intro t ht
    rw [M.euclideanParametricSpeed_negativeInterfaceParam]
    apply hn
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    simp only [sub_zero, abs_zero, abs_neg]
    have habst : |t| ≤ r := (abs_le).2 ⟨by linarith [ht.1, hr.1], ht.2⟩
    exact ⟨hεn, habst.trans_lt hrn⟩
  · intro t ht
    rw [M.euclideanParametricSpeed_extensionConnectorParam]
    apply hc
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    simp only [sub_zero]
    have habst : |t| ≤ r := (abs_le).2 ⟨by linarith [ht.1, hr.1], ht.2⟩
    have hrt : |t - r| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact ⟨habst.trans_lt hrc, hrt.trans_lt hrc⟩

theorem exists_extension_trace_hausdorff_eq_arclength :
    ∃ ρ > 0, ∀ r ∈ Ioc 0 ρ,
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionNegativeInterfaceTrace r) =
          ENNReal.ofReal (M.negativeInterfaceArcLength r) ∧
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionConnectorTrace r) =
          ENNReal.ofReal (M.extensionConnectorArcLength r) := by
  obtain ⟨ρ, hρ, hregular⟩ := M.exists_extensionMetricRadius
  refine ⟨ρ, hρ, ?_⟩
  intro r hr
  constructor
  · rw [A.extensionNegativeInterfaceTrace_eq_image_Icc hr.1.le]
    unfold negativeInterfaceArcLength
    exact hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
      (M.negativeInterfaceParam_contDiff r) hr.1.le
      (by
        intro s _hs t _ht hst
        have hpair : ((0, -s) : PlanePoint) = (0, -t) :=
          A.chart.injective hst
        have := congrArg Prod.snd hpair
        linarith)
      (hregular r hr).1
  · rw [A.extensionConnectorTrace_eq_image_Icc hr.1]
    unfold extensionConnectorArcLength
    exact hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
      (M.extensionConnectorParam_contDiff r) hr.1.le
      (by
        intro s _hs t _ht hst
        exact congrArg Prod.fst (A.chart.injective hst))
      (hregular r hr).2

end ExtensionMetricApplicability
end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison

namespace CMVRelaxation.RegularTraceCornerComparison
namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

namespace ExtensionMetricApplicability

variable (M : ExtensionMetricApplicability A)

private lemma negativeInterfaceArcLength_rescale {r : ℝ} (hr : r ≠ 0) :
    M.negativeInterfaceArcLength r / r =
      ∫ s in 0..1, M.negativeInterfaceSpeedAt (0, -(r * s)) := by
  let f : ℝ → ℝ := fun t => M.negativeInterfaceSpeedAt (0, -t)
  have hchange := intervalIntegral.integral_comp_mul_left f hr
    (a := 0) (b := 1)
  have harc : M.negativeInterfaceArcLength r = ∫ t in 0..r, f t := by
    unfold negativeInterfaceArcLength
    apply intervalIntegral.integral_congr
    intro t _ht
    exact M.euclideanParametricSpeed_negativeInterfaceParam r t
  rw [harc]
  rw [show r * 0 = 0 by ring, show r * 1 = r by ring] at hchange
  simpa only [f, smul_eq_mul, div_eq_inv_mul] using hchange.symm

private lemma extensionConnectorArcLength_rescale {r : ℝ} (hr : r ≠ 0) :
    M.extensionConnectorArcLength r / r =
      ∫ s in 0..1, M.extensionConnectorSpeedAt
        (r * s, r * (s - 1)) := by
  let f : ℝ → ℝ := fun t => M.extensionConnectorSpeedAt (t, t - r)
  have hchange := intervalIntegral.integral_comp_mul_left f hr
    (a := 0) (b := 1)
  have hrewrite :
      (∫ s in 0..1, f (r * s)) =
        ∫ s in 0..1, M.extensionConnectorSpeedAt
          (r * s, r * (s - 1)) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    dsimp [f]
    congr 2
    ring
  rw [hrewrite] at hchange
  have harc : M.extensionConnectorArcLength r = ∫ t in 0..r, f t := by
    unfold extensionConnectorArcLength
    apply intervalIntegral.integral_congr
    intro t _ht
    exact M.euclideanParametricSpeed_extensionConnectorParam r t
  rw [harc]
  rw [show r * 0 = 0 by ring, show r * 1 = r by ring] at hchange
  simpa only [smul_eq_mul, div_eq_inv_mul] using hchange.symm

theorem tendsto_negativeInterfaceArcLength_div :
    Tendsto (fun r => M.negativeInterfaceArcLength r / r) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed C.interface.velocity)) := by
  let F : ℝ → ℝ → ℝ := fun r s =>
    M.negativeInterfaceSpeedAt (0, -(r * s))
  have hF : Continuous F.uncurry := by
    apply M.continuous_negativeInterfaceSpeedAt.comp
    fun_prop
  have hI : Continuous (fun r => ∫ s in 0..1, F r s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hzero : (∫ s in 0..1, F 0 s) =
      euclideanSpeed C.interface.velocity := by
    simp [F, M.negativeInterfaceSpeedAt_zero]
  have hlim : Tendsto (fun r => ∫ s in 0..1, F r s) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed C.interface.velocity)) := by
    rw [← hzero]
    exact hI.continuousAt.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (M.negativeInterfaceArcLength_rescale hr.ne').symm

theorem tendsto_extensionConnectorArcLength_div :
    Tendsto (fun r => M.extensionConnectorArcLength r / r) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed
        (C.incident.velocity.1 + C.interface.velocity.1,
          C.incident.velocity.2 + C.interface.velocity.2))) := by
  let F : ℝ → ℝ → ℝ := fun r s =>
    M.extensionConnectorSpeedAt (r * s, r * (s - 1))
  have hF : Continuous F.uncurry := by
    apply M.continuous_extensionConnectorSpeedAt.comp
    fun_prop
  have hI : Continuous (fun r => ∫ s in 0..1, F r s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hzero : (∫ s in 0..1, F 0 s) =
      euclideanSpeed
        (C.incident.velocity.1 + C.interface.velocity.1,
          C.incident.velocity.2 + C.interface.velocity.2) := by
    simp [F, M.extensionConnectorSpeedAt_zero]
  have hlim : Tendsto (fun r => ∫ s in 0..1, F r s) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed
        (C.incident.velocity.1 + C.interface.velocity.1,
          C.incident.velocity.2 + C.interface.velocity.2))) := by
    rw [← hzero]
    exact hI.continuousAt.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (M.extensionConnectorArcLength_rescale hr.ne').symm

/-- Actual removed incident arclength minus the two inserted arclengths. -/
def extensionMetricTraceGain (w r : ℝ) : ℝ :=
  w * C.incident.arcLength r - M.negativeInterfaceArcLength r -
    w * M.extensionConnectorArcLength r

/-- First-order coefficient of the literal extension splice. -/
def extensionMetricTangentCoefficient
    (_M : ExtensionMetricApplicability A) (w : ℝ) : ℝ :=
  w * euclideanSpeed C.incident.velocity -
    euclideanSpeed C.interface.velocity -
      w * euclideanSpeed
        (C.incident.velocity.1 + C.interface.velocity.1,
          C.incident.velocity.2 + C.interface.velocity.2)

theorem tendsto_extensionMetricTraceGain_div (w : ℝ) :
    Tendsto (fun r => M.extensionMetricTraceGain w r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 (M.extensionMetricTangentCoefficient w)) := by
  have hi := C.incident.tendsto_arcLength_div.const_mul w
  have hf := M.tendsto_negativeInterfaceArcLength_div
  have hk := M.tendsto_extensionConnectorArcLength_div.const_mul w
  convert (hi.sub hf).sub hk using 1 <;>
    simp [extensionMetricTraceGain, extensionMetricTangentCoefficient,
      sub_div, mul_div_assoc]

theorem eventually_extensionMetricTraceGain_pos (w : ℝ)
    (hgain : 0 < M.extensionMetricTangentCoefficient w) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < M.extensionMetricTraceGain w r := by
  have hquot := (M.tendsto_extensionMetricTraceGain_div w).eventually
    (eventually_gt_nhds hgain)
  filter_upwards [hquot, self_mem_nhdsWithin] with r hq hr
  rcases (div_pos_iff.mp hq) with h | h
  · exact h.1
  · exact (not_lt_of_ge hr.le h.2).elim

end ExtensionMetricApplicability

namespace SignedInterfaceApplicability

variable (S : SignedInterfaceApplicability A)

theorem negativeInterface_stripDensity_eq_one
    (S : SignedInterfaceApplicability A)
    (lam : ℝ) {r t : ℝ} (hr : 0 ≤ r) (hlocal : r ≤ A.localRadius)
    (ht : t ∈ Icc 0 r) :
    StripDensity lam (A.extensionNegativeInterfaceParam r t) = 1 := by
  have hsigned : -t ∈ Icc (-A.localRadius) A.localRadius := by
    constructor <;> linarith [ht.1, ht.2, hlocal, A.localRadius_pos]
  unfold extensionNegativeInterfaceParam
  unfold StripDensity
  rw [S.signed_interface_on_strip (-t) hsigned]
  cases side <;> simp [StripInterface.height]

theorem weightedTraceCost_negativeInterface_eq_hausdorff
    (S : SignedInterfaceApplicability A)
    (lam : ℝ) {r : ℝ} (hr : 0 ≤ r) (hlocal : r ≤ A.localRadius) :
    weightedTraceCost lam (A.extensionNegativeInterfaceTrace r) =
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.extensionNegativeInterfaceTrace r) := by
  rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam 1 (A.measurableSet_extensionNegativeInterfaceTrace hr)]
  · simp
  · rintro _ ⟨q, hq, rfl⟩
    have hsigned : q.2 ∈ Icc (-A.localRadius) A.localRadius := by
      exact ⟨by linarith [hq.2.1, hlocal], by linarith [hq.2.2, hlocal]⟩
    unfold StripDensity
    have hqeq : q = (0, q.2) := Prod.ext hq.1 rfl
    rw [hqeq]
    rw [S.signed_interface_on_strip q.2 hsigned]
    cases side <;> simp [StripInterface.height]

end SignedInterfaceApplicability

namespace SignedIncidentPhaseApplicability

variable (P : SignedIncidentPhaseApplicability A)

theorem extensionConnector_stripDensity_eq_weight
    (lam : ℝ) {r t : ℝ} (hr : 0 < r) (hlocal : r < A.localRadius)
    (ht : t ∈ Ioc 0 r) :
    StripDensity lam (A.extensionConnectorParam r t) = P.phase.weight lam := by
  have hq : (t, t - r) ∈
      openLocalizationSquare (0, 0) A.localRadius := by
    simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
    constructor
    · constructor <;> linarith [A.localRadius_pos, ht.1, ht.2, hlocal]
    · constructor <;> linarith [A.localRadius_pos, ht.1, ht.2, hlocal]
  exact P.phase.stripDensity_eq_weight lam
    (P.signed_right_sector_phase (t, t - r) hq ht.1)

theorem weightedTraceCost_extensionConnector_eq_phase_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r) (hlocal : r < A.localRadius) :
    weightedTraceCost lam (A.extensionConnectorTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionConnectorTrace r) := by
  apply weightedTraceCost_eq_const_mul_hausdorff_except_point
    lam (P.phase.weight lam) (A.measurableSet_extensionConnectorTrace hr)
      (A.extensionConnectorParam r 0)
  rintro _ hq hne
  rw [A.extensionConnectorTrace_eq_image_Icc hr] at hq
  rcases hq with ⟨t, ht, rfl⟩
  apply P.extensionConnector_stripDensity_eq_weight lam hr hlocal
  have htne : t ≠ 0 := by
    intro ht0
    apply hne
    rw [ht0]
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm htne), ht.2⟩

end SignedIncidentPhaseApplicability

namespace ExtensionMetricApplicability

variable (M : ExtensionMetricApplicability A)

private lemma endpointArcLength_nonneg
    {junction : PlanePoint} (T : RegularEndpointTrace junction)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ T.arcLength r := by
  unfold RegularEndpointTrace.arcLength
  exact intervalIntegral.integral_nonneg hr (fun _ _ => norm_nonneg _)

private lemma endpointArcLength_two_sub_nonneg
    {junction : PlanePoint} (T : RegularEndpointTrace junction)
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ T.arcLength (2 * r) - T.arcLength r := by
  rw [RegularEndpointTrace.arcLength, RegularEndpointTrace.arcLength,
    intervalIntegral.integral_interval_sub_left
      (T.speed_continuous.intervalIntegrable 0 (2 * r))
      (T.speed_continuous.intervalIntegrable 0 r)]
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => norm_nonneg _)

private lemma negativeInterfaceArcLength_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ M.negativeInterfaceArcLength r := by
  unfold negativeInterfaceArcLength
  exact intervalIntegral.integral_nonneg hr
    (fun _ _ => Real.sqrt_nonneg _)

private lemma extensionConnectorArcLength_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ M.extensionConnectorArcLength r := by
  unfold extensionConnectorArcLength
  exact intervalIntegral.integral_nonneg hr
    (fun _ _ => Real.sqrt_nonneg _)

/-- Fixed-scale cost comparison for the literal four-trace extension frontier. -/
theorem local_inside_cost_lt_of_extensionMetricTraceGain_pos
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    {lam r : ℝ} (hlam : 1 ≤ lam) (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t)
    (hmass :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionNegativeInterfaceTrace r) =
          ENNReal.ofReal (M.negativeInterfaceArcLength r) ∧
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionConnectorTrace r) =
          ENNReal.ofReal (M.extensionConnectorArcLength r))
    (hgain : 0 < M.extensionMetricTraceGain (P.phase.weight lam) r) :
    smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) <
      smoothCostOn lam C.representative (interior (A.window r)) := by
  let P0 := P.toPhysical
  have hretained :
      weightedTraceCost lam (A.extensionRetainedIncidentTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal
            (C.incident.arcLength (2 * r) - C.incident.arcLength r) := by
    simpa [extensionRetainedIncidentTrace, retainedIncidentTrace, P0,
      SignedIncidentPhaseApplicability.toPhysical] using
        PhysicalPhaseApplicability.weightedTraceCost_retainedIncident_eq_phase_arcLength_sub
          A P0 lam hr hlocal hincidentRegular
  have hpositive :
      weightedTraceCost lam (A.extensionPositiveInterfaceTrace r) =
        ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
    simpa [extensionPositiveInterfaceTrace, oldInterfaceTrace] using
      A.weightedTraceCost_oldInterface_eq_arcLength lam hr hlocal htrace
        hinterfaceRegular
  have hnegative :
      weightedTraceCost lam (A.extensionNegativeInterfaceTrace r) =
        ENNReal.ofReal (M.negativeInterfaceArcLength r) := by
    rw [S.weightedTraceCost_negativeInterface_eq_hausdorff
      lam hr.le (by nlinarith [hr, hlocal]), hmass.1]
  have hconnector :
      weightedTraceCost lam (A.extensionConnectorTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (M.extensionConnectorArcLength r) := by
    rw [P.weightedTraceCost_extensionConnector_eq_phase_hausdorff
      lam hr (by linarith), hmass.2]
  have hold :
      smoothCostOn lam C.representative (interior (A.window r)) =
        ENNReal.ofReal (P.phase.weight lam) *
            ENNReal.ofReal (C.incident.arcLength (2 * r)) +
          ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
    simpa [P0, SignedIncidentPhaseApplicability.toPhysical] using
      PhysicalPhaseApplicability.representative_inside_cost_eq_phase_arcLengths
        A P0 lam hr hlocal htrace hincidentRegular hinterfaceRegular
  rw [A.extensionLocalModel_inside_cost_eq_trace_sum lam hr hlocal,
    hretained, hpositive, hnegative, hconnector, hold]
  have hw : 0 ≤ P.phase.weight lam := by
    cases hphase : P.phase
    · simp [LocalTracePhase.weight]
    · simpa [LocalTracePhase.weight] using
        (show (0 : ℝ) ≤ lam from le_trans (by norm_num) hlam)
  have hi : 0 ≤ C.incident.arcLength (2 * r) :=
    endpointArcLength_nonneg C.incident (by linarith)
  have hiDiff : 0 ≤ C.incident.arcLength (2 * r) -
      C.incident.arcLength r :=
    endpointArcLength_two_sub_nonneg C.incident hr.le
  have hn := M.negativeInterfaceArcLength_nonneg hr.le
  have hk := M.extensionConnectorArcLength_nonneg hr.le
  rw [← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul hw]
  rw [show
      ENNReal.ofReal
            (P.phase.weight lam *
              (C.incident.arcLength (2 * r) - C.incident.arcLength r)) +
          ENNReal.ofReal (C.interface.arcLength (2 * r)) +
        ENNReal.ofReal (M.negativeInterfaceArcLength r) +
      ENNReal.ofReal
        (P.phase.weight lam * M.extensionConnectorArcLength r) =
      (ENNReal.ofReal
            (P.phase.weight lam *
              (C.incident.arcLength (2 * r) - C.incident.arcLength r)) +
        ENNReal.ofReal (M.negativeInterfaceArcLength r) +
        ENNReal.ofReal
          (P.phase.weight lam * M.extensionConnectorArcLength r)) +
      ENNReal.ofReal (C.interface.arcLength (2 * r)) by ac_rfl]
  rw [← ENNReal.ofReal_add (mul_nonneg hw hiDiff) hn,
    ← ENNReal.ofReal_add
      (add_nonneg (mul_nonneg hw hiDiff) hn) (mul_nonneg hw hk)]
  apply ENNReal.add_lt_add_right (by simp)
  apply (ENNReal.ofReal_lt_ofReal_iff ?_).2
  · unfold extensionMetricTraceGain at hgain
    linarith
  · unfold extensionMetricTraceGain at hgain
    nlinarith [mul_nonneg hw hiDiff, hn, mul_nonneg hw hk]

/-- Exact local-cost identity for the metric extension: the old local frontier
equals the new four-trace frontier plus the real metric trace gain. -/
theorem local_inside_cost_add_extensionMetricTraceGain
    (M : ExtensionMetricApplicability A)
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    {lam r : ℝ} (hlam : 1 ≤ lam) (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular : ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular : ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t)
    (hmass :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionNegativeInterfaceTrace r) =
          ENNReal.ofReal (M.negativeInterfaceArcLength r) ∧
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.extensionConnectorTrace r) =
          ENNReal.ofReal (M.extensionConnectorArcLength r))
    (hgain : 0 ≤ M.extensionMetricTraceGain (P.phase.weight lam) r) :
    smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) +
        ENNReal.ofReal (M.extensionMetricTraceGain (P.phase.weight lam) r) =
      smoothCostOn lam C.representative (interior (A.window r)) := by
  let P0 := P.toPhysical
  have hretained :
      weightedTraceCost lam (A.extensionRetainedIncidentTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (C.incident.arcLength (2 * r) - C.incident.arcLength r) := by
    simpa [extensionRetainedIncidentTrace, retainedIncidentTrace, P0,
      SignedIncidentPhaseApplicability.toPhysical] using
      PhysicalPhaseApplicability.weightedTraceCost_retainedIncident_eq_phase_arcLength_sub
        A P0 lam hr hlocal hincidentRegular
  have hpositive :
      weightedTraceCost lam (A.extensionPositiveInterfaceTrace r) =
        ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
    simpa [extensionPositiveInterfaceTrace, oldInterfaceTrace] using
      A.weightedTraceCost_oldInterface_eq_arcLength lam hr hlocal htrace
        hinterfaceRegular
  have hnegative :
      weightedTraceCost lam (A.extensionNegativeInterfaceTrace r) =
        ENNReal.ofReal (M.negativeInterfaceArcLength r) := by
    rw [S.weightedTraceCost_negativeInterface_eq_hausdorff
      lam hr.le (by nlinarith [hr, hlocal]), hmass.1]
  have hconnector :
      weightedTraceCost lam (A.extensionConnectorTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (M.extensionConnectorArcLength r) := by
    rw [P.weightedTraceCost_extensionConnector_eq_phase_hausdorff
      lam hr (by linarith), hmass.2]
  have hold :
      smoothCostOn lam C.representative (interior (A.window r)) =
        ENNReal.ofReal (P.phase.weight lam) *
            ENNReal.ofReal (C.incident.arcLength (2 * r)) +
          ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
    simpa [P0, SignedIncidentPhaseApplicability.toPhysical] using
      PhysicalPhaseApplicability.representative_inside_cost_eq_phase_arcLengths
        A P0 lam hr hlocal htrace hincidentRegular hinterfaceRegular
  rw [A.extensionLocalModel_inside_cost_eq_trace_sum lam hr hlocal,
    hretained, hpositive, hnegative, hconnector, hold]
  have hw : 0 ≤ P.phase.weight lam := by
    cases hphase : P.phase
    · simp [LocalTracePhase.weight]
    · simpa [LocalTracePhase.weight] using
        (show (0 : ℝ) ≤ lam from le_trans (by norm_num) hlam)
  have hi : 0 ≤ C.incident.arcLength (2 * r) := by
    unfold RegularEndpointTrace.arcLength
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => norm_nonneg _)
  have hiDiff : 0 ≤ C.incident.arcLength (2 * r) -
      C.incident.arcLength r := by
    rw [RegularEndpointTrace.arcLength, RegularEndpointTrace.arcLength,
      intervalIntegral.integral_interval_sub_left
        (C.incident.speed_continuous.intervalIntegrable 0 (2 * r))
        (C.incident.speed_continuous.intervalIntegrable 0 r)]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => norm_nonneg _)
  have hf : 0 ≤ C.interface.arcLength (2 * r) := by
    unfold RegularEndpointTrace.arcLength
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => norm_nonneg _)
  have hn : 0 ≤ M.negativeInterfaceArcLength r := by
    unfold negativeInterfaceArcLength
    exact intervalIntegral.integral_nonneg hr.le
      (fun _ _ => Real.sqrt_nonneg _)
  have hk : 0 ≤ M.extensionConnectorArcLength r := by
    unfold extensionConnectorArcLength
    exact intervalIntegral.integral_nonneg hr.le
      (fun _ _ => Real.sqrt_nonneg _)
  rw [← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul hw]
  rw [← ENNReal.ofReal_add (mul_nonneg hw hiDiff) hf,
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hw hiDiff) hf) hn,
    ← ENNReal.ofReal_add
      (add_nonneg (add_nonneg (mul_nonneg hw hiDiff) hf) hn)
      (mul_nonneg hw hk),
    ← ENNReal.ofReal_add
      (add_nonneg
        (add_nonneg (add_nonneg (mul_nonneg hw hiDiff) hf) hn)
        (mul_nonneg hw hk)) hgain,
    ← ENNReal.ofReal_add (mul_nonneg hw hi) hf]
  congr 1
  unfold extensionMetricTraceGain
  ring

/-- Reattaching the unchanged exterior turns the exact local gain identity into
an exact complete-frontier cost identity. -/
theorem extensionCompetitor_complete_cost_add_gain_eq
    {lam r gain : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius)
    (hinside :
      smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) +
          ENNReal.ofReal gain =
        smoothCostOn lam C.representative (interior (A.window r))) :
    smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal gain =
      smoothCost lam C.representative := by
  rw [A.extensionCompetitor_complete_cost lam hr hlocal,
    ← smoothCostOn_add_compl lam C.representative
      isOpen_interior.measurableSet, ← hinside]
  ac_rfl

/-- A strict local extension descent shortens the actual complete competitor
whenever the unchanged exterior cost is finite. -/
theorem extensionCompetitor_complete_cost_lt_of_local_inside_cost_lt
    {lam r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius)
    (hinside :
      smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) <
        smoothCostOn lam C.representative (interior (A.window r)))
    (houtside :
      smoothCostOn lam C.representative (interior (A.window r))ᶜ ≠ ⊤) :
    smoothCost lam (A.extensionCompetitor r) <
      smoothCost lam C.representative := by
  rw [A.extensionCompetitor_complete_cost lam hr hlocal,
    ← smoothCostOn_add_compl lam C.representative
      isOpen_interior.measurableSet]
  exact ENNReal.add_lt_add_of_lt_of_le houtside hinside le_rfl

/-- Positive first-order extension gain gives actual local frontier descent for
all sufficiently small scales. -/
theorem eventually_extension_local_inside_cost_lt
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hgain : 0 < M.extensionMetricTangentCoefficient (P.phase.weight lam)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCostOn lam (A.extensionLocalModel r) (interior (A.window r)) <
        smoothCostOn lam C.representative (interior (A.window r)) := by
  obtain ⟨ρt, hρt, hρtLocal, hiRegular, hfRegular⟩ :=
    A.exists_traceMetricRadius
  obtain ⟨ρe, hρe, hmass⟩ :=
    exists_extension_trace_hausdorff_eq_arclength M
  have hmetric := M.eventually_extensionMetricTraceGain_pos
    (P.phase.weight lam) hgain
  have hsmallTrace : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρt :=
    ((eventually_lt_nhds (half_pos hρt)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallSource : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < C.radius :=
    ((eventually_lt_nhds (half_pos C.radius_pos)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallMass : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ ρe :=
    ((eventually_lt_nhds hρe).filter_mono inf_le_left).mono
      (fun _ hr => hr.le)
  filter_upwards [self_mem_nhdsWithin, hmetric, hsmallTrace,
    hsmallSource, hsmallMass] with r hr hrGain hrTrace hrSource hrMass
  apply M.local_inside_cost_lt_of_extensionMetricTraceGain_pos
    S P hlam hr (hrTrace.trans_le hρtLocal) hrSource.le
  · intro t ht
    exact hiRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩
  · intro t ht
    exact hfRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩
  · exact hmass r ⟨hr, hrMass⟩
  · exact hrGain

/-- A positive tangent coefficient gives a uniform linear complete-cost gain
for the actual extension family at every sufficiently small positive scale. -/
theorem eventually_extension_complete_cost_add_linear_le
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hgain : 0 < M.extensionMetricTangentCoefficient (P.phase.weight lam)) :
    ∃ k > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal (k * r) ≤
        smoothCost lam C.representative := by
  let k := M.extensionMetricTangentCoefficient (P.phase.weight lam) / 2
  have hk : 0 < k := half_pos hgain
  refine ⟨k, hk, ?_⟩
  obtain ⟨ρt, hρt, hρtLocal, hiRegular, hfRegular⟩ :=
    A.exists_traceMetricRadius
  obtain ⟨ρe, hρe, hmass⟩ :=
    exists_extension_trace_hausdorff_eq_arclength M
  have hquot := (M.tendsto_extensionMetricTraceGain_div
    (P.phase.weight lam)).eventually (eventually_gt_nhds
      (show k < M.extensionMetricTangentCoefficient (P.phase.weight lam) by
        dsimp [k]
        linarith))
  have hsmallTrace : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρt :=
    ((eventually_lt_nhds (half_pos hρt)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallSource : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < C.radius :=
    ((eventually_lt_nhds (half_pos C.radius_pos)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallMass : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ ρe :=
    ((eventually_lt_nhds hρe).filter_mono inf_le_left).mono
      (fun _ hr => hr.le)
  filter_upwards [self_mem_nhdsWithin, hquot, hsmallTrace,
    hsmallSource, hsmallMass] with r hr hquot hrTrace hrSource hrMass
  have hkr : k * r <
      M.extensionMetricTraceGain (P.phase.weight lam) r :=
    (lt_div_iff₀ hr).mp hquot
  have hmetricNonneg :
      0 ≤ M.extensionMetricTraceGain (P.phase.weight lam) r := by
    exact (mul_pos hk hr).trans hkr |>.le
  have hinside := M.local_inside_cost_add_extensionMetricTraceGain
    S P hlam hr (hrTrace.trans_le hρtLocal) hrSource.le
      (fun t ht => hiRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩)
      (fun t ht => hfRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩)
      (hmass r ⟨hr, hrMass⟩) hmetricNonneg
  have hcomplete := extensionCompetitor_complete_cost_add_gain_eq
    (A := A) hr (hrTrace.trans_le hρtLocal) hinside
  calc
    smoothCost lam (A.extensionCompetitor r) + ENNReal.ofReal (k * r) ≤
        smoothCost lam (A.extensionCompetitor r) +
          ENNReal.ofReal
            (M.extensionMetricTraceGain (P.phase.weight lam) r) :=
      add_le_add_right (ENNReal.ofReal_le_ofReal hkr.le) _
    _ = smoothCost lam C.representative := hcomplete

end ExtensionMetricApplicability
end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison

namespace CMVRelaxation.RegularTraceCornerComparison
namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

/-- The strict violating endpoint ratio is smaller than one; this also rules
out degeneration of the normalized velocity sum. -/
lemma extensionEndpointRatio_lt_one {w c : ℝ} (hw : 1 < w)
    (hcLower : -1 ≤ c) :
    extensionEndpointRatio w c < 1 := by
  have hwpos : 0 < w := zero_lt_one.trans hw
  have hden : 0 < w ^ 2 - 1 := by nlinarith
  rw [extensionEndpointRatio]
  apply (div_lt_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hcLower hwpos.le
  nlinarith

namespace SignedInterfaceApplicability

/-- Signed interface geometry survives independent positive endpoint
normalization. -/
def positiveDiagonalReparam
    (S : SignedInterfaceApplicability A)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    SignedInterfaceApplicability (A.positiveDiagonalReparam a b ha hb) where
  signed_interface_on_strip := by
    intro t ht
    have hab : 0 < a + b := add_pos ha hb
    have hscale : b * (A.localRadius / (a + b)) ≤ A.localRadius := by
      calc
        b * (A.localRadius / (a + b)) ≤
            (a + b) * (A.localRadius / (a + b)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha.le)
            (div_nonneg A.localRadius_pos.le hab.le)
        _ = A.localRadius := by field_simp [hab.ne']
    have hbt : b * t ∈ Icc (-A.localRadius) A.localRadius := by
      dsimp [RegularCornerChartApplicability.positiveDiagonalReparam] at ht
      simp only [mem_Icc] at ht
      constructor
      · have h := mul_le_mul_of_nonneg_left ht.1 hb.le
        nlinarith
      · exact (mul_le_mul_of_nonneg_left ht.2 hb.le).trans hscale
    change (A.chart (a * 0, b * t)).2 = side.height
    simpa using S.signed_interface_on_strip (b * t) hbt

end SignedInterfaceApplicability

namespace SignedIncidentPhaseApplicability

/-- Signed incident-phase geometry survives independent positive endpoint
normalization. -/
def positiveDiagonalReparam
    (P : SignedIncidentPhaseApplicability A)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    SignedIncidentPhaseApplicability (A.positiveDiagonalReparam a b ha hb) where
  phase := P.phase
  signed_right_sector_phase := by
    intro q hq hqFirst
    change q ∈ openLocalizationSquare (0, 0)
      (A.localRadius / (a + b)) at hq
    have hab : 0 < a + b := add_pos ha hb
    have hscaled :
        (a * q.1, b * q.2) ∈
          openLocalizationSquare (0, 0) A.localRadius := by
      simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
        at hq ⊢
      rcases hq with ⟨hx, hy⟩
      have hLa : a * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          a * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_right a hb)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      have hLb : b * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          b * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_left b ha)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      constructor
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hx.1 ha,
          mul_lt_mul_of_pos_left hx.2 ha]
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hy.1 hb,
          mul_lt_mul_of_pos_left hy.2 hb]
    change P.phase.Contains (A.chart (a * q.1, b * q.2))
    exact P.signed_right_sector_phase (a * q.1, b * q.2) hscaled
      (mul_pos ha hqFirst)

end SignedIncidentPhaseApplicability

namespace ExtensionMetricApplicability

/-- Reuse the checked `C¹` chart transport while replacing the trimming
velocity-difference regularity by the extension velocity-sum regularity. -/
def positiveDiagonalReparamFromMetric
    (M : MetricApplicability A)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hdiff : (a * C.incident.velocity.1 - b * C.interface.velocity.1,
      a * C.incident.velocity.2 - b * C.interface.velocity.2) ≠ (0, 0))
    (hsum : (a * C.incident.velocity.1 + b * C.interface.velocity.1,
      a * C.incident.velocity.2 + b * C.interface.velocity.2) ≠ (0, 0)) :
    ExtensionMetricApplicability (A.positiveDiagonalReparam a b ha hb) := by
  let M' := M.positiveDiagonalReparam_metric a b ha hb hdiff
  refine
    { chart_contDiff := MetricApplicability.chart_contDiff M'
      fderiv_incident := MetricApplicability.fderiv_incident M'
      fderiv_interface := MetricApplicability.fderiv_interface M'
      connectorVelocitySum_ne := ?_ }
  simpa [ActualRegularTraceCorner.positiveDiagonalReparam,
    RegularEndpointTrace.positiveReparam] using hsum

end ExtensionMetricApplicability

/-- Positive source scale making the incident endpoint velocity unit speed. -/
def normalizedExtensionIncidentScale (C : ActualRegularTraceCorner side) : ℝ :=
  C.incident.unitScale

/-- Positive source scale realizing the selected physical interface endpoint
ratio. -/
def normalizedExtensionInterfaceScale
    (C : ActualRegularTraceCorner side) (w : ℝ) : ℝ :=
  extensionEndpointRatio w
      (planeInner C.incidentConormal C.interfaceConormal) *
    C.interface.unitScale

lemma normalizedExtensionIncidentScale_pos :
    0 < normalizedExtensionIncidentScale C :=
  C.incident.unitScale_pos

lemma normalizedExtensionInterfaceScale_pos {w : ℝ} (hw : 1 < w)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / w) :
    0 < normalizedExtensionInterfaceScale C w :=
  mul_pos (extensionEndpointRatio_pos hw hc) C.interface.unitScale_pos

private lemma normalizedExtension_velocityDifference_ne
    {w : ℝ} (hw : 1 < w)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / w) :
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C w
    (a * C.incident.velocity.1 - b * C.interface.velocity.1,
      a * C.incident.velocity.2 - b * C.interface.velocity.2) ≠ (0, 0) := by
  dsimp only
  let c := planeInner C.incidentConormal C.interfaceConormal
  let t := extensionEndpointRatio w c
  let a := normalizedExtensionIncidentScale C
  let b := normalizedExtensionInterfaceScale C w
  have ht : 0 < t := extensionEndpointRatio_pos hw hc
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := by
    dsimp [b, normalizedExtensionInterfaceScale]
    exact mul_pos ht C.interface.unitScale_pos
  have haSpeed : a * euclideanSpeed C.incident.velocity = 1 := by
    dsimp [a, normalizedExtensionIncidentScale, RegularEndpointTrace.unitScale]
    exact inv_mul_cancel₀ (ne_of_gt (euclideanSpeed_pos C.incident.velocity_ne))
  have hbSpeed : b * euclideanSpeed C.interface.velocity = t := by
    dsimp [b, normalizedExtensionInterfaceScale, RegularEndpointTrace.unitScale,
      t, c]
    rw [mul_assoc, inv_mul_cancel₀
      (ne_of_gt (euclideanSpeed_pos C.interface.velocity_ne)), mul_one]
  intro hzero
  have hnorm :
      ‖complexVector (C.incident.positiveReparam a ha).velocity -
        complexVector (C.interface.positiveReparam b hb).velocity‖ = 0 := by
    have hv :
        complexVector (C.incident.positiveReparam a ha).velocity -
            complexVector (C.interface.positiveReparam b hb).velocity = 0 := by
      apply Complex.ext
      · simpa [RegularEndpointTrace.positiveReparam, complexVector] using
          congrArg Prod.fst hzero
      · simpa [RegularEndpointTrace.positiveReparam, complexVector] using
          congrArg Prod.snd hzero
    rw [hv, norm_zero]
  have hsq := positiveReparam_velocityDifference_norm_sq
    C.incident C.interface a b ha hb
  rw [haSpeed, hbSpeed, hnorm] at hsq
  norm_num at hsq
  have hcEq :
      planeInner (endpointConormal .initial C.incident.velocity)
        (endpointConormal .initial C.interface.velocity) = c := rfl
  rw [hcEq] at hsq
  have hwpos : 0 < w := zero_lt_one.trans hw
  have hcneg : c < 0 := by
    dsimp [c]
    exact hc.trans_le
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hwpos.le)
  nlinarith

private lemma normalizedExtension_velocitySum_ne
    {w : ℝ} (hw : 1 < w)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / w) :
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C w
    (a * C.incident.velocity.1 + b * C.interface.velocity.1,
      a * C.incident.velocity.2 + b * C.interface.velocity.2) ≠ (0, 0) := by
  dsimp only
  let c := planeInner C.incidentConormal C.interfaceConormal
  let t := extensionEndpointRatio w c
  let a := normalizedExtensionIncidentScale C
  let b := normalizedExtensionInterfaceScale C w
  have ht : 0 < t := extensionEndpointRatio_pos hw hc
  have hcLower : -1 ≤ c := C.conormal_inner_ge_neg_one
  have htOne : t < 1 := extensionEndpointRatio_lt_one hw hcLower
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := by
    dsimp [b, normalizedExtensionInterfaceScale]
    exact mul_pos ht C.interface.unitScale_pos
  have haSpeed : a * euclideanSpeed C.incident.velocity = 1 := by
    dsimp [a, normalizedExtensionIncidentScale, RegularEndpointTrace.unitScale]
    exact inv_mul_cancel₀ (ne_of_gt (euclideanSpeed_pos C.incident.velocity_ne))
  have hbSpeed : b * euclideanSpeed C.interface.velocity = t := by
    dsimp [b, normalizedExtensionInterfaceScale, RegularEndpointTrace.unitScale,
      t, c]
    rw [mul_assoc, inv_mul_cancel₀
      (ne_of_gt (euclideanSpeed_pos C.interface.velocity_ne)), mul_one]
  intro hzero
  have hnorm :
      ‖complexVector (C.incident.positiveReparam a ha).velocity +
        complexVector (C.interface.positiveReparam b hb).velocity‖ = 0 := by
    have hv :
        complexVector (C.incident.positiveReparam a ha).velocity +
            complexVector (C.interface.positiveReparam b hb).velocity = 0 := by
      apply Complex.ext
      · simpa [RegularEndpointTrace.positiveReparam, complexVector] using
          congrArg Prod.fst hzero
      · simpa [RegularEndpointTrace.positiveReparam, complexVector] using
          congrArg Prod.snd hzero
    rw [hv, norm_zero]
  have hsq := positiveReparam_velocitySum_norm_sq
    C.incident C.interface a b ha hb
  rw [haSpeed, hbSpeed, hnorm] at hsq
  norm_num at hsq
  have hcEq :
      planeInner (endpointConormal .initial C.incident.velocity)
        (endpointConormal .initial C.interface.velocity) = c := rfl
  rw [hcEq] at hsq
  have hcTerm := mul_le_mul_of_nonneg_left hcLower (by positivity : 0 ≤ 2 * t)
  nlinarith [sq_nonneg (1 - t)]

private theorem normalizedExtension_tangentCoefficient_eq
    (M : MetricApplicability A) {w : ℝ} (hw : 1 < w)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / w) :
    let c := planeInner C.incidentConormal C.interfaceConormal
    let t := extensionEndpointRatio w c
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C w
    let A' := A.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos hw hc)
    let M' := ExtensionMetricApplicability.positiveDiagonalReparamFromMetric M
      a b normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos hw hc)
      (normalizedExtension_velocityDifference_ne hw hc)
      (normalizedExtension_velocitySum_ne hw hc)
    M'.extensionMetricTangentCoefficient w =
      extensionTangentGain w 1 t c := by
  dsimp only
  let c := planeInner C.incidentConormal C.interfaceConormal
  let t := extensionEndpointRatio w c
  let a := normalizedExtensionIncidentScale C
  let b := normalizedExtensionInterfaceScale C w
  have ht : 0 < t := extensionEndpointRatio_pos hw hc
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := normalizedExtensionInterfaceScale_pos hw hc
  have haScale : a * euclideanSpeed C.incident.velocity = 1 := by
    dsimp [a, normalizedExtensionIncidentScale, RegularEndpointTrace.unitScale]
    exact inv_mul_cancel₀ (ne_of_gt (euclideanSpeed_pos C.incident.velocity_ne))
  have hbScale : b * euclideanSpeed C.interface.velocity = t := by
    dsimp [b, normalizedExtensionInterfaceScale, RegularEndpointTrace.unitScale,
      t, c]
    rw [mul_assoc, inv_mul_cancel₀
      (ne_of_gt (euclideanSpeed_pos C.interface.velocity_ne)), mul_one]
  have haSpeed :
      euclideanSpeed (C.incident.positiveReparam a ha).velocity = 1 := by
    rw [C.incident.positiveReparam_euclideanSpeed a ha, haScale]
  have hbSpeed :
      euclideanSpeed (C.interface.positiveReparam b hb).velocity = t := by
    rw [C.interface.positiveReparam_euclideanSpeed b hb, hbScale]
  let C' := C.positiveDiagonalReparam a b ha hb
  have hsumSq := positiveReparam_velocitySum_norm_sq
    C.incident C.interface a b ha hb
  rw [haScale, hbScale] at hsumSq
  have hcEq :
      planeInner (endpointConormal .initial C.incident.velocity)
        (endpointConormal .initial C.interface.velocity) = c := rfl
  rw [hcEq] at hsumSq
  let Q := 1 + t ^ 2 + 2 * 1 * t * c
  have hQ : 0 ≤ Q := by
    have hcLower : -1 ≤ c := C.conormal_inner_ge_neg_one
    have hcTerm := mul_le_mul_of_nonneg_left hcLower
      (by positivity : 0 ≤ 2 * t)
    dsimp [Q]
    nlinarith [sq_nonneg (1 - t)]
  have hsum :
      euclideanSpeed
          (C'.incident.velocity.1 + C'.interface.velocity.1,
            C'.incident.velocity.2 + C'.interface.velocity.2) =
        Real.sqrt Q := by
    have hleft :
        euclideanSpeed
            (C'.incident.velocity.1 + C'.interface.velocity.1,
              C'.incident.velocity.2 + C'.interface.velocity.2) =
          ‖complexVector (C.incident.positiveReparam a ha).velocity +
            complexVector (C.interface.positiveReparam b hb).velocity‖ := by
      unfold euclideanSpeed
      congr 1
      apply Complex.ext <;>
        simp [C', ActualRegularTraceCorner.positiveDiagonalReparam,
          RegularEndpointTrace.positiveReparam, complexVector]
    rw [hleft]
    have hnorm0 := norm_nonneg
      (complexVector (C.incident.positiveReparam a ha).velocity +
        complexVector (C.interface.positiveReparam b hb).velocity)
    have hsqrt0 := Real.sqrt_nonneg Q
    have hsqrtSq := Real.sq_sqrt hQ
    have hsquare :
        ‖complexVector (C.incident.positiveReparam a ha).velocity +
          complexVector (C.interface.positiveReparam b hb).velocity‖ ^ 2 = Q := by
      simpa [Q] using hsumSq
    nlinarith
  unfold ExtensionMetricApplicability.extensionMetricTangentCoefficient
  change w * euclideanSpeed (C.incident.positiveReparam a ha).velocity -
      euclideanSpeed (C.interface.positiveReparam b hb).velocity -
        w * euclideanSpeed
          ((C.incident.positiveReparam a ha).velocity.1 +
              (C.interface.positiveReparam b hb).velocity.1,
            (C.incident.positiveReparam a ha).velocity.2 +
              (C.interface.positiveReparam b hb).velocity.2) =
      extensionTangentGain w 1 t c
  rw [haSpeed, hbSpeed]
  have hsum' :
      euclideanSpeed
          ((C.incident.positiveReparam a ha).velocity.1 +
              (C.interface.positiveReparam b hb).velocity.1,
            (C.incident.positiveReparam a ha).velocity.2 +
              (C.interface.positiveReparam b hb).velocity.2) =
        Real.sqrt Q := by
    simpa [C', ActualRegularTraceCorner.positiveDiagonalReparam] using hsum
  rw [hsum']
  simp [extensionTangentGain, Q]

/-- A genuine strict exterior conormal violation constructs positive endpoint
normalizations and an actual same-representative extension family whose local
weighted frontier is strictly shorter at every sufficiently small scale. -/
theorem eventually_normalizedExtension_local_inside_cost_lt_of_conormal_lt
    (M : MetricApplicability A)
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    (lam : ℝ) (hlam : 1 < lam) (hphase : P.phase = .exterior)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / lam) :
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C lam
    let A' := A.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos hlam hc)
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCostOn lam (A'.extensionLocalModel r) (interior (A'.window r)) <
        smoothCostOn lam C.representative (interior (A'.window r)) := by
  dsimp only
  let c := planeInner C.incidentConormal C.interfaceConormal
  let t := extensionEndpointRatio lam c
  let a := normalizedExtensionIncidentScale C
  let b := normalizedExtensionInterfaceScale C lam
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := normalizedExtensionInterfaceScale_pos hlam hc
  let A' := A.positiveDiagonalReparam a b ha hb
  let M' := ExtensionMetricApplicability.positiveDiagonalReparamFromMetric M
    a b ha hb (normalizedExtension_velocityDifference_ne hlam hc)
      (normalizedExtension_velocitySum_ne hlam hc)
  let S' := S.positiveDiagonalReparam a b ha hb
  let P' := P.positiveDiagonalReparam a b ha hb
  have hcoef : 0 < M'.extensionMetricTangentCoefficient (P'.phase.weight lam) := by
    have heq := normalizedExtension_tangentCoefficient_eq M hlam hc
    have hsign := C.extensionTangentGain_pos_of_conormal_lt hlam hc
    have hweight : P'.phase.weight lam = lam := by
      simp [P', SignedIncidentPhaseApplicability.positiveDiagonalReparam,
        hphase, LocalTracePhase.weight]
    rw [hweight, heq]
    exact hsign
  have hactual := M'.eventually_extension_local_inside_cost_lt
    S' P' lam hlam.le hcoef
  simpa [A', ActualRegularTraceCorner.positiveDiagonalReparam] using hactual

/-- A strict exterior conormal violation yields a uniform linear
complete-frontier gain for the endpoint-normalized extension family. -/
theorem eventually_normalizedExtension_complete_cost_add_linear_le_of_conormal_lt
    (M : MetricApplicability A)
    (S : SignedInterfaceApplicability A)
    (P : SignedIncidentPhaseApplicability A)
    (lam : ℝ) (hlam : 1 < lam) (hphase : P.phase = .exterior)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / lam) :
    let a := normalizedExtensionIncidentScale C
    let b := normalizedExtensionInterfaceScale C lam
    let A' := A.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos hlam hc)
    ∃ k > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost lam (A'.extensionCompetitor r) + ENNReal.ofReal (k * r) ≤
        smoothCost lam C.representative := by
  dsimp only
  let a := normalizedExtensionIncidentScale C
  let b := normalizedExtensionInterfaceScale C lam
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := normalizedExtensionInterfaceScale_pos hlam hc
  let A' := A.positiveDiagonalReparam a b ha hb
  let M' := ExtensionMetricApplicability.positiveDiagonalReparamFromMetric M
    a b ha hb (normalizedExtension_velocityDifference_ne hlam hc)
      (normalizedExtension_velocitySum_ne hlam hc)
  let S' := S.positiveDiagonalReparam a b ha hb
  let P' := P.positiveDiagonalReparam a b ha hb
  have hcoef : 0 < M'.extensionMetricTangentCoefficient (P'.phase.weight lam) := by
    have heq := normalizedExtension_tangentCoefficient_eq M hlam hc
    have hsign := C.extensionTangentGain_pos_of_conormal_lt hlam hc
    have hweight : P'.phase.weight lam = lam := by
      simp [P', SignedIncidentPhaseApplicability.positiveDiagonalReparam,
        hphase, LocalTracePhase.weight]
    rw [hweight, heq]
    exact hsign
  have hactual := M'.eventually_extension_complete_cost_add_linear_le
    S' P' lam hlam.le hcoef
  simpa [A', ActualRegularTraceCorner.positiveDiagonalReparam] using hactual

end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison
