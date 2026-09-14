import CMVRegularTraceCornerComparison

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

/-- The occupied reference quadrant in local corner coordinates. -/
def openCorner : Set PlanePoint := {q | 0 < q.1 ∧ 0 < q.2}

/-- The reference corner after removing the triangle below the joining chord. -/
def trimmedOpenCorner (r : ℝ) : Set PlanePoint :=
  {q | 0 < q.1 ∧ 0 < q.2 ∧ r < q.1 + q.2}

/-- The retained part of the first coordinate ray. -/
def retainedIncidentRay (r : ℝ) : Set PlanePoint :=
  {q | r ≤ q.1 ∧ q.2 = 0}

/-- The retained part of the second coordinate ray. -/
def retainedInterfaceRay (r : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ r ≤ q.2}

/-- The inserted joining segment in local corner coordinates. -/
def cornerConnector (r : ℝ) : Set PlanePoint :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = r}

lemma isOpen_openCorner : IsOpen openCorner := by
  exact (isOpen_lt
    (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
    continuous_fst).inter
      (isOpen_lt
        (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
        continuous_snd)

lemma isOpen_trimmedOpenCorner (r : ℝ) : IsOpen (trimmedOpenCorner r) := by
  exact (isOpen_lt
    (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
    continuous_fst).inter
      ((isOpen_lt
        (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
        continuous_snd).inter
          (isOpen_lt
            (continuous_const : Continuous (fun _ : PlanePoint => r))
            (continuous_fst.add continuous_snd)))

private def closedTrimmedCorner (r : ℝ) : Set PlanePoint :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ r ≤ q.1 + q.2}

private lemma isClosed_closedTrimmedCorner (r : ℝ) :
    IsClosed (closedTrimmedCorner r) := by
  exact (isClosed_le
    (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
    continuous_fst).inter
      ((isClosed_le
        (continuous_const : Continuous (fun _ : PlanePoint => (0 : ℝ)))
        continuous_snd).inter
          (isClosed_le
            (continuous_const : Continuous (fun _ : PlanePoint => r))
            (continuous_fst.add continuous_snd)))

lemma closure_trimmedOpenCorner (r : ℝ) :
    closure (trimmedOpenCorner r) = closedTrimmedCorner r := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro q hq
      exact ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
    · exact isClosed_closedTrimmedCorner r
  · intro q hq
    rw [mem_closure_iff_seq_limit]
    let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    refine ⟨fun n => (q.1 + e n, q.2 + e n), ?_, ?_⟩
    · intro n
      have he : 0 < e n := by
        dsimp [e]
        positivity
      exact ⟨by linarith [hq.1], by linarith [hq.2.1], by linarith [hq.2.2]⟩
    · have he : Tendsto e atTop (𝓝 0) := by
        simpa [e] using
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
      simpa using (tendsto_const_nhds.add he).prodMk_nhds
        (tendsto_const_nhds.add he)

/-- Exact complete frontier of the reference trimmed quadrant. -/
theorem frontier_trimmedOpenCorner {r : ℝ} (hr : 0 < r) :
    frontier (trimmedOpenCorner r) =
      retainedIncidentRay r ∪ retainedInterfaceRay r ∪ cornerConnector r := by
  rw [(isOpen_trimmedOpenCorner r).frontier_eq, closure_trimmedOpenCorner]
  ext q
  change
    ((0 ≤ q.1 ∧ 0 ≤ q.2 ∧ r ≤ q.1 + q.2) ∧
        ¬(0 < q.1 ∧ 0 < q.2 ∧ r < q.1 + q.2)) ↔
      ((r ≤ q.1 ∧ q.2 = 0) ∨ (q.1 = 0 ∧ r ≤ q.2)) ∨
        (0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = r)
  constructor
  · rintro ⟨hq, hnot⟩
    rcases hq with ⟨hx, hy, hsum⟩
    by_cases hx0 : q.1 = 0
    · exact Or.inl (Or.inr ⟨hx0, by linarith⟩)
    by_cases hy0 : q.2 = 0
    · exact Or.inl (Or.inl ⟨by linarith, hy0⟩)
    right
    refine ⟨hx, hy, ?_⟩
    by_contra hne
    have hlt : r < q.1 + q.2 := lt_of_le_of_ne hsum (Ne.symm hne)
    exact hnot ⟨lt_of_le_of_ne hx (Ne.symm hx0),
      lt_of_le_of_ne hy (Ne.symm hy0), hlt⟩
  · intro hq
    refine ⟨?_, ?_⟩
    · rcases hq with (hincident | hinterface) | hconnector
      · exact ⟨by linarith [hr, hincident.1], le_of_eq hincident.2.symm,
          by simpa [hincident.2] using hincident.1⟩
      · exact ⟨le_of_eq hinterface.1.symm, by linarith [hr, hinterface.2],
          by simpa [hinterface.1] using hinterface.2⟩
      · exact ⟨hconnector.1, hconnector.2.1, hconnector.2.2.symm.le⟩
    · intro hopen
      rcases hq with (hincident | hinterface) | hconnector
      · linarith [hopen.2.1, hincident.2]
      · linarith [hopen.1, hinterface.1]
      · linarith [hopen.2.2, hconnector.2.2]


/-- Every actual interface germ has literal density price one.  Incident and
connector prices are deliberately not inferred from the membership-only corner
record. -/
theorem ActualRegularTraceCorner.interface_stripDensity_eq_one
    {side : StripInterface} (C : ActualRegularTraceCorner side) (lam : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 C.radius) :
    StripDensity lam (C.interface.curve t) = 1 := by
  unfold StripDensity
  rw [C.interface_on_strip t ht]
  cases side <;> simp [StripInterface.height]
/-- A single exceptional physical point does not affect a constant-density
trace cost because Euclidean `H¹` has no atoms. -/
lemma weightedTraceCost_eq_const_mul_hausdorff_except_point
    (lam w : ℝ) {S : Set PlanePoint} (hS : MeasurableSet S)
    (p : PlanePoint)
    (hdensity : ∀ q ∈ S, q ≠ p → StripDensity lam q = w) :
    weightedTraceCost lam S = ENNReal.ofReal w *
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' S) := by
  unfold weightedTraceCost
  have hmeas : MeasurableSet (planeEuclideanHomeomorph '' S) :=
    (planeEuclideanHomeomorph.continuous.measurableEmbedding
      planeEuclideanHomeomorph.injective).measurableSet_image' hS
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  calc
    (∫⁻ z in planeEuclideanHomeomorph '' S,
        ENNReal.ofReal (euclideanStripDensity lam z)
        ∂(μH[1] : Measure EuclideanPlane)) =
        ∫⁻ _z in planeEuclideanHomeomorph '' S, ENNReal.ofReal w
          ∂(μH[1] : Measure EuclideanPlane) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hmeas,
        ae_restrict_of_ae
          (Measure.ae_ne (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph p))] with z hz hzne
      rcases hz with ⟨q, hq, rfl⟩
      have hqp : q ≠ p :=
        fun h => hzne (congrArg planeEuclideanHomeomorph h)
      change ENNReal.ofReal
        (StripDensity lam
          (planeEuclideanHomeomorph.symm (planeEuclideanHomeomorph q))) =
        ENNReal.ofReal w
      rw [planeEuclideanHomeomorph.symm_apply_apply, hdensity q hq hqp]
    _ = _ := by simp


/-! ## Source-geometric chart and the constructed splice -/

/-- Open axis-aligned coordinate neighborhood. -/
def openLocalizationSquare (center : PlanePoint) (radius : ℝ) :
    Set PlanePoint :=
  Ioo (center.1 - radius) (center.1 + radius) ×ˢ
    Ioo (center.2 - radius) (center.2 + radius)

lemma isOpen_openLocalizationSquare (center : PlanePoint) (radius : ℝ) :
    IsOpen (openLocalizationSquare center radius) :=
  isOpen_Ioo.prod isOpen_Ioo


/-- Coordinates on which the triangular cut is inactive.  This is source-side
geometry; it mentions neither a competitor nor collar agreement. -/
def inactiveCornerRegion (r : ℝ) : Set PlanePoint :=
  {q | q.1 < 0} ∪ {q | q.2 < 0} ∪ {q | r < q.1 + q.2}

lemma isOpen_inactiveCornerRegion (r : ℝ) :
    IsOpen (inactiveCornerRegion r) := by
  exact ((isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_snd continuous_const)).union
      (isOpen_lt
        (continuous_const : Continuous (fun _ : PlanePoint => r))
        (continuous_fst.add continuous_snd))

/-- Additional upstream geometry needed beyond membership of two regular
frontier germs.  A common corner chart gives local embeddedness, complete local
frontier coverage, and the occupied sector of the unchanged representative.
The linear coordinate bound is a local regularity estimate.  No replacement
set, replacement frontier, collar agreement, comparison cost, or contact law is
a field. -/
structure RegularCornerChartApplicability {side : StripInterface}
    (C : ActualRegularTraceCorner side) where
  chart : PlanePoint ≃ₜ PlanePoint
  localRadius : ℝ
  localRadius_pos : 0 < localRadius
  chart_zero : chart (0, 0) = C.junction
  incident_axis :
    ∀ t ∈ Icc 0 localRadius, chart (t, 0) = C.incident.curve t
  interface_axis :
    ∀ t ∈ Icc 0 localRadius, chart (0, t) = C.interface.curve t
  representative_local :
    ∀ q ∈ openLocalizationSquare (0, 0) localRadius,
      (chart q ∈ C.representative ↔ q ∈ openCorner)
  coordinateBound : ℝ
  coordinateBound_pos : 0 < coordinateBound
  chart_coordinate_bound :
    ∀ q ∈ localizationSquare (0, 0) localRadius,
      |(chart q).1 - C.junction.1| ≤
          coordinateBound * (|q.1| + |q.2|) ∧
        |(chart q).2 - C.junction.2| ≤
          coordinateBound * (|q.1| + |q.2|)

namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    (A : RegularCornerChartApplicability C)

/-- Coordinate window used by the scale-`r` replacement. -/
def coordinateWindow (_A : RegularCornerChartApplicability C) (r : ℝ) :
    Set PlanePoint :=
  closedCutRectangle (-2 * r) (2 * r) (-2 * r) (2 * r)

/-- Actual closed localization window in source coordinates. -/
def window (r : ℝ) : Set PlanePoint := A.chart '' A.coordinateWindow r

/-- Actual open local model, constructed by applying the common corner chart
to the trimmed reference quadrant. -/
def localModel (r : ℝ) : Set PlanePoint :=
  A.chart '' trimmedOpenCorner r

/-- Derived open collar around the localization boundary. -/
def collar (r : ℝ) : Set PlanePoint :=
  A.chart ''
    (openLocalizationSquare (0, 0) A.localRadius ∩ inactiveCornerRegion r)

/-- The actual same-representative localized competitor. -/
def competitor (r : ℝ) : Set PlanePoint :=
  localizedCompetitor C.representative (A.localModel r) (A.window r)

lemma isOpen_localModel (r : ℝ) : IsOpen (A.localModel r) :=
  A.chart.isOpenMap _ (isOpen_trimmedOpenCorner r)

lemma isOpen_collar (r : ℝ) : IsOpen (A.collar r) :=
  A.chart.isOpenMap _
    ((isOpen_openLocalizationSquare (0, 0) A.localRadius).inter
      (isOpen_inactiveCornerRegion r))

lemma isClosed_window (r : ℝ) : IsClosed (A.window r) := by
  exact A.chart.isClosedMap _ (by
    exact (isClosed_Icc : IsClosed (Icc (-2 * r) (2 * r))).prod
      (isClosed_Icc : IsClosed (Icc (-2 * r) (2 * r))))

lemma isBounded_window (r : ℝ) : Bornology.IsBounded (A.window r) := by
  exact ((isCompact_Icc.prod isCompact_Icc).image A.chart.continuous).isBounded

lemma closure_interior_window {r : ℝ} (hr : 0 < r) :
    closure (interior (A.window r)) = A.window r := by
  rw [window, ← A.chart.image_interior, ← A.chart.image_closure]
  exact congrArg (fun S => A.chart '' S)
    (closure_interior_closedCutRectangle
      (by linarith : -2 * r < 2 * r) (by linarith : -2 * r < 2 * r))

private lemma coordinateWindow_subset_localSquare {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    A.coordinateWindow r ⊆ localizationSquare (0, 0) A.localRadius := by
  intro q hq
  rcases hq with ⟨hx, hy⟩
  constructor <;> constructor <;> norm_num at hx hy ⊢ <;> linarith

private lemma coordinateWindow_subset_openLocalSquare {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    A.coordinateWindow r ⊆ openLocalizationSquare (0, 0) A.localRadius := by
  intro q hq
  rcases hq with ⟨hx, hy⟩
  constructor <;> constructor <;> norm_num at hx hy ⊢ <;> linarith

lemma frontier_window_subset_collar {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.window r) ⊆ A.collar r := by
  rw [window, ← A.chart.image_frontier]
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨q, ⟨?_, ?_⟩, rfl⟩
  · exact A.coordinateWindow_subset_openLocalSquare hlocal
      ((isClosed_Icc.prod isClosed_Icc).frontier_subset hq)
  · change (q.1 < 0 ∨ q.2 < 0) ∨ r < q.1 + q.2
    have hfaces := frontier_closedCutRectangle_subset_lines
      (by linarith : -2 * r < 2 * r) (by linarith : -2 * r < 2 * r) hq
    rcases hfaces with ((hxneg | hxpos) | hyneg) | hypos
    · left
      left
      have hx : q.1 = -2 * r := by simpa [verticalLine] using hxneg
      linarith
    · by_cases hy : q.2 < 0
      · exact Or.inl (Or.inr hy)
      · exact Or.inr (by
          have hx : q.1 = 2 * r := by simpa [verticalLine] using hxpos
          have hy0 : 0 ≤ q.2 := le_of_not_gt hy
          linarith)
    · left
      right
      have hy : q.2 = -2 * r := by simpa [horizontalLine] using hyneg
      linarith
    · by_cases hx : q.1 < 0
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (by
          have hy : q.2 = 2 * r := by simpa [horizontalLine] using hypos
          have hx0 : 0 ≤ q.1 := le_of_not_gt hx
          linarith)

/-- Collar agreement is derived from the unchanged representative's occupied
quadrant and the explicitly constructed trim. -/
lemma representative_inter_collar_eq_localModel {r : ℝ} :
    C.representative ∩ A.collar r = A.localModel r ∩ A.collar r := by
  ext p
  constructor
  · rintro ⟨hpU, q, hq, rfl⟩
    have hqCorner : q ∈ openCorner :=
      (A.representative_local q hq.1).mp hpU
    have hsum : r < q.1 + q.2 := by
      rcases hq.2 with (hx | hy) | hsum
      · exact (not_lt_of_ge hqCorner.1.le hx).elim
      · exact (not_lt_of_ge hqCorner.2.le hy).elim
      · exact hsum
    exact ⟨⟨q, ⟨hqCorner.1, hqCorner.2, hsum⟩, rfl⟩,
      ⟨q, hq, rfl⟩⟩
  · rintro ⟨⟨q, hqTrim, hqp⟩, ⟨z, hz, hzp⟩⟩
    have hqz : q = z := A.chart.injective (hqp.trans hzp.symm)
    subst z
    subst p
    exact ⟨(A.representative_local q hz.1).mpr ⟨hqTrim.1, hqTrim.2.1⟩,
      ⟨q, hz, rfl⟩⟩

/-- The chart's scale-independent local bound places the whole actual window
inside a physical square of radius `4*K*r`. -/
lemma window_subset_localizationSquare {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    A.window r ⊆
      localizationSquare C.junction (4 * A.coordinateBound * r) := by
  rintro p ⟨q, hq, rfl⟩
  have hqLocal := A.coordinateWindow_subset_localSquare hlocal hq
  have hbound := A.chart_coordinate_bound q hqLocal
  rcases hq with ⟨hx, hy⟩
  norm_num at hx hy
  have habsx : |q.1| ≤ 2 * r := (abs_le).2 ⟨by linarith, by linarith⟩
  have habsy : |q.2| ≤ 2 * r := (abs_le).2 ⟨by linarith, by linarith⟩
  have hK : 0 ≤ A.coordinateBound := A.coordinateBound_pos.le
  have hxy :
      A.coordinateBound * (|q.1| + |q.2|) ≤
        4 * A.coordinateBound * r := by
    nlinarith
  constructor <;> constructor <;>
    nlinarith [le_trans hbound.1 hxy, le_trans hbound.2 hxy,
      neg_abs_le ((A.chart q).1 - C.junction.1),
      le_abs_self ((A.chart q).1 - C.junction.1),
      neg_abs_le ((A.chart q).2 - C.junction.2),
      le_abs_self ((A.chart q).2 - C.junction.2)]



/-- Old incident-axis piece visible in the scale window. -/
def oldIncidentPiece (r : ℝ) : Set PlanePoint :=
  {q | 0 ≤ q.1 ∧ q.1 < 2 * r ∧ q.2 = 0}

/-- Old interface-axis piece visible in the scale window. -/
def oldInterfacePiece (r : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ 0 ≤ q.2 ∧ q.2 < 2 * r}

/-- Retained incident-axis piece after the triangular cut. -/
def retainedIncidentPiece (r : ℝ) : Set PlanePoint :=
  {q | r ≤ q.1 ∧ q.1 < 2 * r ∧ q.2 = 0}

/-- Retained interface-axis piece after the triangular cut. -/
def retainedInterfacePiece (r : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ r ≤ q.2 ∧ q.2 < 2 * r}

private theorem frontier_trimmed_inter_coordinateWindow {r : ℝ} (hr : 0 < r) :
    frontier (trimmedOpenCorner r) ∩ interior (A.coordinateWindow r) =
      retainedIncidentPiece r ∪ retainedInterfacePiece r ∪ cornerConnector r := by
  rw [frontier_trimmedOpenCorner hr]
  ext q
  simp only [mem_inter_iff, mem_union]
  rw [coordinateWindow, closedCutRectangle, interior_prod_eq]
  simp only [interior_Icc, mem_prod, mem_Ioo, retainedIncidentRay,
    retainedInterfaceRay, cornerConnector, retainedIncidentPiece,
    retainedInterfacePiece, mem_ofPred_eq]
  change
    ((((r ≤ q.1 ∧ q.2 = 0) ∨ (q.1 = 0 ∧ r ≤ q.2)) ∨
        (0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = r)) ∧
          (-2 * r < q.1 ∧ q.1 < 2 * r) ∧
          (-2 * r < q.2 ∧ q.2 < 2 * r)) ↔
      (((r ≤ q.1 ∧ q.1 < 2 * r ∧ q.2 = 0) ∨
        (q.1 = 0 ∧ r ≤ q.2 ∧ q.2 < 2 * r)) ∨
          (0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 = r))
  constructor
  · rintro ⟨(hincident | hinterface) | hconnector, hx, hy⟩
    · exact Or.inl (Or.inl ⟨hincident.1, hx.2, hincident.2⟩)
    · exact Or.inl (Or.inr ⟨hinterface.1, hinterface.2, hy.2⟩)
    · exact Or.inr hconnector
  · rintro ((hincident | hinterface) | hconnector)
    · refine ⟨Or.inl (Or.inl ⟨hincident.1, hincident.2.2⟩),
        ⟨by linarith [hincident.1, hr], hincident.2.1⟩, ?_⟩
      rw [hincident.2.2]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨Or.inl (Or.inr ⟨hinterface.1, hinterface.2.1⟩),
        ?_, ⟨by linarith [hinterface.2.1, hr], hinterface.2.2⟩⟩
      rw [hinterface.1]
      exact ⟨by linarith, by linarith⟩
    · rcases hconnector with ⟨hx, hy, hsum⟩
      have hxle : q.1 ≤ r := by linarith
      have hyle : q.2 ≤ r := by linarith
      exact ⟨Or.inr ⟨hx, hy, hsum⟩,
        ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem frontier_openCorner :
    frontier openCorner =
      {q : PlanePoint | 0 ≤ q.1 ∧ q.2 = 0} ∪
        {q : PlanePoint | q.1 = 0 ∧ 0 ≤ q.2} := by
  change frontier (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = _
  rw [frontier_prod_eq, closure_Ioi, frontier_Ioi]
  ext q
  simp

private theorem frontier_openCorner_inter_coordinateWindow {r : ℝ} (hr : 0 < r) :
    frontier openCorner ∩ interior (A.coordinateWindow r) =
      oldIncidentPiece r ∪ oldInterfacePiece r := by
  rw [frontier_openCorner]
  ext q
  rw [coordinateWindow, closedCutRectangle, interior_prod_eq]
  simp only [interior_Icc, mem_inter_iff, mem_union, mem_prod, mem_Ioo,
    oldIncidentPiece, oldInterfacePiece, mem_ofPred_eq]
  change
    (((0 ≤ q.1 ∧ q.2 = 0) ∨ (q.1 = 0 ∧ 0 ≤ q.2)) ∧
        (-2 * r < q.1 ∧ q.1 < 2 * r) ∧
        (-2 * r < q.2 ∧ q.2 < 2 * r)) ↔
      ((0 ≤ q.1 ∧ q.1 < 2 * r ∧ q.2 = 0) ∨
        (q.1 = 0 ∧ 0 ≤ q.2 ∧ q.2 < 2 * r))
  constructor
  · rintro ⟨hincident | hinterface, hx, hy⟩
    · exact Or.inl ⟨hincident.1, hx.2, hincident.2⟩
    · exact Or.inr ⟨hinterface.1, hinterface.2, hy.2⟩
  · rintro (hincident | hinterface)
    · exact ⟨Or.inl ⟨hincident.1, hincident.2.2⟩,
        ⟨by linarith, hincident.2.1⟩, by simp [hincident.2.2, hr]⟩
    · exact ⟨Or.inr ⟨hinterface.1, hinterface.2.1⟩,
        by simp [hinterface.1, hr],
        ⟨by linarith, hinterface.2.2⟩⟩


/-- Actual retained incident trace in the scale window. -/
def retainedIncidentTrace (_A : RegularCornerChartApplicability C) (r : ℝ) :
    Set PlanePoint :=
  C.incident.curve '' Ico r (2 * r)

/-- Actual retained interface trace in the scale window. -/
def retainedInterfaceTrace (_A : RegularCornerChartApplicability C) (r : ℝ) :
    Set PlanePoint :=
  C.interface.curve '' Ico r (2 * r)

/-- Actual inserted connector, constructed in the common corner chart. -/
def connectorTrace (r : ℝ) : Set PlanePoint :=
  A.chart '' cornerConnector r

/-- The complete old incident trace visible in the scale window. -/
def oldIncidentTrace (_A : RegularCornerChartApplicability C) (r : ℝ) :
    Set PlanePoint :=
  C.incident.curve '' Ico 0 (2 * r)

/-- The complete old interface trace visible in the scale window. -/
def oldInterfaceTrace (_A : RegularCornerChartApplicability C) (r : ℝ) :
    Set PlanePoint :=
  C.interface.curve '' Ico 0 (2 * r)

private lemma image_retainedIncidentPiece {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' retainedIncidentPiece r = A.retainedIncidentTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqeq : q = (q.1, 0) := Prod.ext rfl hq.2.2
    refine ⟨q.1, ⟨hq.1, hq.2.1⟩, ?_⟩
    calc
      C.incident.curve q.1 = A.chart (q.1, 0) :=
        (A.incident_axis q.1 ⟨by linarith [hr, hq.1],
          hq.2.1.le.trans hlocal.le⟩).symm
      _ = A.chart q := congrArg A.chart hqeq.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t, 0), ⟨ht.1, ht.2, rfl⟩, ?_⟩
    exact A.incident_axis t ⟨by linarith [hr, ht.1],
      ht.2.le.trans hlocal.le⟩

private lemma image_retainedInterfacePiece {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' retainedInterfacePiece r = A.retainedInterfaceTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqeq : q = (0, q.2) := Prod.ext hq.1 rfl
    refine ⟨q.2, ⟨hq.2.1, hq.2.2⟩, ?_⟩
    calc
      C.interface.curve q.2 = A.chart (0, q.2) :=
        (A.interface_axis q.2 ⟨by linarith [hr, hq.2.1],
          hq.2.2.le.trans hlocal.le⟩).symm
      _ = A.chart q := congrArg A.chart hqeq.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(0, t), ⟨rfl, ht.1, ht.2⟩, ?_⟩
    exact A.interface_axis t ⟨by linarith [hr, ht.1],
      ht.2.le.trans hlocal.le⟩

private lemma image_oldIncidentPiece {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' oldIncidentPiece r = A.oldIncidentTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqeq : q = (q.1, 0) := Prod.ext rfl hq.2.2
    refine ⟨q.1, ⟨hq.1, hq.2.1⟩, ?_⟩
    calc
      C.incident.curve q.1 = A.chart (q.1, 0) :=
        (A.incident_axis q.1
          ⟨hq.1, hq.2.1.le.trans hlocal.le⟩).symm
      _ = A.chart q := congrArg A.chart hqeq.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t, 0), ⟨ht.1, ht.2, rfl⟩, ?_⟩
    exact A.incident_axis t ⟨ht.1, ht.2.le.trans hlocal.le⟩

private lemma image_oldInterfacePiece {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    A.chart '' oldInterfacePiece r = A.oldInterfaceTrace r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hqeq : q = (0, q.2) := Prod.ext hq.1 rfl
    refine ⟨q.2, ⟨hq.2.1, hq.2.2⟩, ?_⟩
    calc
      C.interface.curve q.2 = A.chart (0, q.2) :=
        (A.interface_axis q.2
          ⟨hq.2.1, hq.2.2.le.trans hlocal.le⟩).symm
      _ = A.chart q := congrArg A.chart hqeq.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(0, t), ⟨rfl, ht.1, ht.2⟩, ?_⟩
    exact A.interface_axis t ⟨ht.1, ht.2.le.trans hlocal.le⟩

/-- Complete inserted and retained frontier of the constructed local model. -/
theorem localModel_frontier_inside_window {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.localModel r) ∩ interior (A.window r) =
      A.retainedIncidentTrace r ∪ A.retainedInterfaceTrace r ∪
        A.connectorTrace r := by
  calc
    frontier (A.localModel r) ∩ interior (A.window r) =
        A.chart ''
          (frontier (trimmedOpenCorner r) ∩
            interior (A.coordinateWindow r)) := by
      rw [localModel, window, ← A.chart.image_frontier,
        ← A.chart.image_interior, ← Set.image_inter A.chart.injective]
    _ = A.chart ''
        (retainedIncidentPiece r ∪ retainedInterfacePiece r ∪
          cornerConnector r) := by
      rw [A.frontier_trimmed_inter_coordinateWindow hr]
    _ = A.retainedIncidentTrace r ∪ A.retainedInterfaceTrace r ∪
        A.connectorTrace r := by
      rw [image_union, image_union, A.image_retainedIncidentPiece hr hlocal,
        A.image_retainedInterfacePiece hr hlocal]
      rfl

/-- Open untrimmed quadrant model used only to derive the unchanged local
frontier; it is not a supplied replacement. -/
private def oldLocalModel : Set PlanePoint := A.chart '' openCorner

private def localNeighborhood : Set PlanePoint :=
  A.chart '' openLocalizationSquare (0, 0) A.localRadius

private lemma isOpen_localNeighborhood : IsOpen A.localNeighborhood :=
  A.chart.isOpenMap _
    (isOpen_openLocalizationSquare (0, 0) A.localRadius)

private lemma representative_inter_localNeighborhood :
    C.representative ∩ A.localNeighborhood =
      A.oldLocalModel ∩ A.localNeighborhood := by
  ext p
  constructor
  · rintro ⟨hpU, q, hq, rfl⟩
    exact ⟨⟨q, (A.representative_local q hq).mp hpU, rfl⟩,
      ⟨q, hq, rfl⟩⟩
  · rintro ⟨⟨q, hqCorner, hqp⟩, ⟨z, hz, hzp⟩⟩
    have hqz : q = z := A.chart.injective (hqp.trans hzp.symm)
    subst z
    subst p
    exact ⟨(A.representative_local q hz).mpr hqCorner, ⟨q, hz, rfl⟩⟩

private lemma interior_window_subset_localNeighborhood {r : ℝ}
    (hlocal : 2 * r < A.localRadius) :
    interior (A.window r) ⊆ A.localNeighborhood := by
  rw [window, ← A.chart.image_interior]
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q, A.coordinateWindow_subset_openLocalSquare hlocal
    (interior_subset hq), rfl⟩

/-- The common source chart derives complete local frontier coverage of the
unchanged representative by the two actual regular germs. -/
theorem representative_frontier_inside_window {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier C.representative ∩ interior (A.window r) =
      A.oldIncidentTrace r ∪ A.oldInterfaceTrace r := by
  have hfrontLocal :
      frontier C.representative ∩ A.localNeighborhood =
        frontier A.oldLocalModel ∩ A.localNeighborhood :=
    frontier_inter_eq_of_inter_open_eq A.isOpen_localNeighborhood
      A.representative_inter_localNeighborhood
  have hsub := A.interior_window_subset_localNeighborhood hlocal
  calc
    frontier C.representative ∩ interior (A.window r) =
        (frontier C.representative ∩ A.localNeighborhood) ∩
          interior (A.window r) := by
      ext p
      simp only [mem_inter_iff]
      tauto
    _ = (frontier A.oldLocalModel ∩ A.localNeighborhood) ∩
          interior (A.window r) := by rw [hfrontLocal]
    _ = frontier A.oldLocalModel ∩ interior (A.window r) := by
      ext p
      simp only [mem_inter_iff]
      tauto
    _ = A.chart ''
        (frontier openCorner ∩ interior (A.coordinateWindow r)) := by
      rw [oldLocalModel, window, ← A.chart.image_frontier,
        ← A.chart.image_interior, ← Set.image_inter A.chart.injective]
    _ = A.chart '' (oldIncidentPiece r ∪ oldInterfacePiece r) := by
      rw [A.frontier_openCorner_inter_coordinateWindow hr]
    _ = A.oldIncidentTrace r ∪ A.oldInterfaceTrace r := by
      rw [image_union, A.image_oldIncidentPiece hlocal,
        A.image_oldInterfacePiece hlocal]

/-- The constructed competitor is open. -/
lemma isOpen_competitor (r : ℝ) : IsOpen (A.competitor r) :=
  localizedCompetitor_isOpen _ _ _

/-- The constructed competitor is bounded by the unchanged representative and
the actual localization window. -/
lemma isBounded_competitor (r : ℝ) :
    Bornology.IsBounded (A.competitor r) :=
  localizedCompetitor_isBounded C.representative_isBounded
    (A.isBounded_window r)

/-- Exact complete frontier of the actual same-representative splice.  The
removed old initial germs are absent, the retained germs and connector are
inserted literally, and every unchanged exterior frontier point remains. -/
theorem competitor_frontier {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    frontier (A.competitor r) =
      (A.retainedIncidentTrace r ∪ A.retainedInterfaceTrace r ∪
        A.connectorTrace r) ∪
          (frontier C.representative ∩ (interior (A.window r))ᶜ) := by
  rw [competitor]
  have h := localizedCompetitor_frontier_eq_piecewise
    C.representative_isOpen (A.isOpen_localModel r) (A.isClosed_window r)
    (A.closure_interior_window hr) (A.isOpen_collar r)
    (A.frontier_window_subset_collar hr hlocal)
    A.representative_inter_collar_eq_localModel
  rw [A.localModel_frontier_inside_window hr hlocal] at h
  exact h

/-- The exact complete-cost split is an application of the retained splice
theorem to the constructed model and derived collar. -/
theorem competitor_complete_cost (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    smoothCost lam (A.competitor r) =
      smoothCostOn lam (A.localModel r) (interior (A.window r)) +
        smoothCostOn lam C.representative (interior (A.window r))ᶜ := by
  exact localizedCompetitor_complete_cost lam C.representative_isOpen
    (A.isOpen_localModel r) (A.isClosed_window r)
    (A.closure_interior_window hr) (A.isOpen_collar r)
    (A.frontier_window_subset_collar hr hlocal)
    A.representative_inter_collar_eq_localModel

/-- Exact carrier and complete-frontier agreement outside the constructed
localization window. -/
theorem competitor_agrees_outside {r : ℝ} :
    A.competitor r ∩ (A.window r)ᶜ =
        C.representative ∩ (A.window r)ᶜ ∧
      frontier (A.competitor r) ∩ interior (A.window r)ᶜ =
        frontier C.representative ∩ interior (A.window r)ᶜ :=
  localizedCompetitor_agrees_outside C.representative_isOpen
    (A.isOpen_localModel r) (A.isClosed_window r)

/-- Scale-independent quadratic weighted-area defect for the actual constructed
competitor. -/
theorem competitor_weightedArea_defect_le {lam r : ℝ} (hlam : 1 ≤ lam)
    (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    |WeightedArea lam (A.competitor r) -
        WeightedArea lam C.representative| ≤
      4 * lam * (4 * A.coordinateBound) ^ 2 * r ^ 2 := by
  exact localizedCompetitor_weightedArea_defect_le hlam
    (mul_nonneg (by norm_num) A.coordinateBound_pos.le) hr.le
    C.representative_isOpen (A.isOpen_localModel r) (A.isClosed_window r)
    C.representative_isBounded (A.isBounded_window r)
    (A.window_subset_localizationSquare hlocal)

/-! ## Literal trace multiplicity and local cost accounting -/

/-- Parameterization of the constructed connector.  Unlike
`RegularEndpointTrace.shortcutLength`, this is the literal chart image used by
the actual splice. -/
def connectorParam (r t : ℝ) : PlanePoint :=
  A.chart (t, r - t)

lemma connectorParam_continuous (r : ℝ) :
    Continuous (A.connectorParam r) := by
  exact A.chart.continuous.comp
    (continuous_id.prodMk (continuous_const.sub continuous_id))

/-- The literal connector has the expected interval parameterization. -/
theorem connectorTrace_eq_image_Icc {r : ℝ} (_hr : 0 ≤ r) :
    A.connectorTrace r = A.connectorParam r '' Icc 0 r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.1, ⟨hq.1, ?_⟩, ?_⟩
    · linarith [hq.2.1, hq.2.2]
    · apply congrArg A.chart
      apply Prod.ext
      · rfl
      · dsimp [connectorParam]
        linarith [hq.2.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t, r - t), ⟨ht.1, by linarith [ht.2], by ring⟩, rfl⟩

/-- The common corner chart proves local injectivity of the actual incident
trace; injectivity is not added to the source corner record. -/
theorem incident_injOn_local :
    Set.InjOn C.incident.curve (Icc 0 A.localRadius) := by
  intro s hs t ht hst
  have hchart : A.chart (s, 0) = A.chart (t, 0) := by
    rw [A.incident_axis s hs, A.incident_axis t ht]
    exact hst
  exact congrArg Prod.fst (A.chart.injective hchart)

/-- The common corner chart likewise proves local injectivity of the actual
interface trace, including horizontal and vertical chart orientations. -/
theorem interface_injOn_local :
    Set.InjOn C.interface.curve (Icc 0 A.localRadius) := by
  intro s hs t ht hst
  have hchart : A.chart (0, s) = A.chart (0, t) := by
    rw [A.interface_axis s hs, A.interface_axis t ht]
    exact hst
  exact congrArg Prod.snd (A.chart.injective hchart)

/-- The connector has multiplicity one at every positive scale. -/
theorem connectorParam_injOn (r : ℝ) :
    Set.InjOn (A.connectorParam r) (Icc 0 r) := by
  intro s _hs t _ht hst
  have hpair : (s, r - s) = (t, r - t) := by
    exact A.chart.injective hst
  exact congrArg Prod.fst hpair
/-- A single positive source scale on which both actual germs are regular and
the common chart proves multiplicity one. -/
theorem exists_traceMetricRadius :
    ∃ ρ > 0, ρ ≤ A.localRadius ∧
      (∀ t ∈ Icc 0 ρ, 0 < C.incident.speed t) ∧
      (∀ t ∈ Icc 0 ρ, 0 < C.interface.speed t) := by
  obtain ⟨ρi, hρi, hi⟩ := C.incident.exists_speed_pos_radius
  obtain ⟨ρf, hρf, hf⟩ := C.interface.exists_speed_pos_radius
  refine ⟨min A.localRadius (min ρi ρf),
    lt_min A.localRadius_pos (lt_min hρi hρf),
    min_le_left _ _, ?_, ?_⟩
  · intro t ht
    exact hi t
      ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  · intro t ht
    exact hf t
      ⟨ht.1, ht.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- Exact `H¹` mass of the old incident germ in the physical splice window. -/
theorem hausdorffMeasure_oldIncidentTrace_eq_arcLength
    {r : ℝ} (hr : 0 ≤ r) (hlocal : 2 * r ≤ A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.oldIncidentTrace r) =
      ENNReal.ofReal (C.incident.arcLength (2 * r)) := by
  have hinj : Set.InjOn C.incident.curve (Icc 0 (2 * r)) := by
    apply A.incident_injOn_local.mono
    intro t ht
    exact ⟨ht.1, ht.2.trans hlocal⟩
  simpa [oldIncidentTrace, RegularEndpointTrace.arcLength] using
    C.incident.hausdorffMeasure_curve_Ico_eq_arcLength_sub
      (by linarith) hinj hregular

/-- Exact `H¹` mass of the retained incident germ. -/
theorem hausdorffMeasure_retainedIncidentTrace_eq_arcLength_sub
    {r : ℝ} (hr : 0 ≤ r) (hlocal : 2 * r ≤ A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.retainedIncidentTrace r) =
      ENNReal.ofReal
        (C.incident.arcLength (2 * r) - C.incident.arcLength r) := by
  have hinj : Set.InjOn C.incident.curve (Icc r (2 * r)) := by
    apply A.incident_injOn_local.mono
    intro t ht
    exact ⟨hr.trans ht.1, ht.2.trans hlocal⟩
  apply C.incident.hausdorffMeasure_curve_Ico_eq_arcLength_sub
    (by linarith) hinj
  intro t ht
  exact hregular t ⟨hr.trans ht.1, ht.2⟩

/-- Exact `H¹` mass of the old interface germ in the physical splice window. -/
theorem hausdorffMeasure_oldInterfaceTrace_eq_arcLength
    {r : ℝ} (hr : 0 ≤ r) (hlocal : 2 * r ≤ A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.oldInterfaceTrace r) =
      ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
  have hinj : Set.InjOn C.interface.curve (Icc 0 (2 * r)) := by
    apply A.interface_injOn_local.mono
    intro t ht
    exact ⟨ht.1, ht.2.trans hlocal⟩
  simpa [oldInterfaceTrace, RegularEndpointTrace.arcLength] using
    C.interface.hausdorffMeasure_curve_Ico_eq_arcLength_sub
      (by linarith) hinj hregular

/-- Exact `H¹` mass of the retained interface germ. -/
theorem hausdorffMeasure_retainedInterfaceTrace_eq_arcLength_sub
    {r : ℝ} (hr : 0 ≤ r) (hlocal : 2 * r ≤ A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.retainedInterfaceTrace r) =
      ENNReal.ofReal
        (C.interface.arcLength (2 * r) - C.interface.arcLength r) := by
  have hinj : Set.InjOn C.interface.curve (Icc r (2 * r)) := by
    apply A.interface_injOn_local.mono
    intro t ht
    exact ⟨hr.trans ht.1, ht.2.trans hlocal⟩
  apply C.interface.hausdorffMeasure_curve_Ico_eq_arcLength_sub
    (by linarith) hinj
  intro t ht
  exact hregular t ⟨hr.trans ht.1, ht.2⟩


private theorem measurableSet_incident_image_Ico
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ A.localRadius) :
    MeasurableSet (C.incident.curve '' Ico a b) := by
  rw [image_Ico_eq_image_Icc_diff_endpoint A.incident_injOn_local hab]
  · exact ((isCompact_Icc.image C.incident.curve_continuous).measurableSet).diff
      (measurableSet_singleton (C.incident.curve b))
  · intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩

private theorem measurableSet_interface_image_Ico
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ A.localRadius) :
    MeasurableSet (C.interface.curve '' Ico a b) := by
  rw [image_Ico_eq_image_Icc_diff_endpoint A.interface_injOn_local hab]
  · exact ((isCompact_Icc.image C.interface.curve_continuous).measurableSet).diff
      (measurableSet_singleton (C.interface.curve b))
  · intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩

lemma measurableSet_retainedIncidentTrace {r : ℝ} (hr : 0 ≤ r)
    (hlocal : 2 * r ≤ A.localRadius) :
    MeasurableSet (A.retainedIncidentTrace r) := by
  exact A.measurableSet_incident_image_Ico hr (by linarith) hlocal

lemma measurableSet_retainedInterfaceTrace {r : ℝ} (hr : 0 ≤ r)
    (hlocal : 2 * r ≤ A.localRadius) :
    MeasurableSet (A.retainedInterfaceTrace r) := by
  exact A.measurableSet_interface_image_Ico hr (by linarith) hlocal

lemma measurableSet_oldIncidentTrace {r : ℝ} (hr : 0 ≤ r)
    (hlocal : 2 * r ≤ A.localRadius) :
    MeasurableSet (A.oldIncidentTrace r) := by
  exact A.measurableSet_incident_image_Ico le_rfl (by linarith) hlocal

lemma measurableSet_oldInterfaceTrace {r : ℝ} (hr : 0 ≤ r)
    (hlocal : 2 * r ≤ A.localRadius) :
    MeasurableSet (A.oldInterfaceTrace r) := by
  exact A.measurableSet_interface_image_Ico le_rfl (by linarith) hlocal

lemma measurableSet_connectorTrace {r : ℝ} (hr : 0 ≤ r) :
    MeasurableSet (A.connectorTrace r) := by
  rw [A.connectorTrace_eq_image_Icc hr]
  exact (isCompact_Icc.image (A.connectorParam_continuous r)).measurableSet

theorem retainedIncidentTrace_disjoint_retainedInterfaceTrace
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    Disjoint (A.retainedIncidentTrace r) (A.retainedInterfaceTrace r) := by
  rw [Set.disjoint_left]
  rintro p ⟨s, hs, hsp⟩ ⟨t, ht, htp⟩
  have hsLocal : s ∈ Icc 0 A.localRadius :=
    ⟨hr.le.trans hs.1, hs.2.le.trans hlocal.le⟩
  have htLocal : t ∈ Icc 0 A.localRadius :=
    ⟨hr.le.trans ht.1, ht.2.le.trans hlocal.le⟩
  have hcoords : (s, 0) = (0, t) := by
    apply A.chart.injective
    calc
      A.chart (s, 0) = C.incident.curve s := A.incident_axis s hsLocal
      _ = p := hsp
      _ = C.interface.curve t := htp.symm
      _ = A.chart (0, t) := (A.interface_axis t htLocal).symm
  have hs0 : s = 0 := congrArg Prod.fst hcoords
  have hspos : 0 < s := hr.trans_le hs.1
  exact hspos.ne' hs0

theorem retainedIncidentTrace_inter_connector_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.retainedIncidentTrace r ∩ A.connectorTrace r).Finite := by
  apply (Set.finite_singleton (C.incident.curve r)).subset
  rintro p ⟨⟨s, hs, hsp⟩, q, hq, hqp⟩
  have hsLocal : s ∈ Icc 0 A.localRadius :=
    ⟨hr.le.trans hs.1, hs.2.le.trans hlocal.le⟩
  have hcoords : (s, 0) = q := by
    apply A.chart.injective
    calc
      A.chart (s, 0) = C.incident.curve s := A.incident_axis s hsLocal
      _ = p := hsp
      _ = A.chart q := hqp.symm
  have hqSecond : q.2 = 0 := by
    simpa using congrArg Prod.snd hcoords.symm
  have hqFirst : q.1 = r := by
    linarith [hq.2.2]
  have hsEq : s = r := by
    simpa [hqFirst] using congrArg Prod.fst hcoords
  simpa only [mem_singleton_iff, hsEq] using hsp.symm

theorem retainedInterfaceTrace_inter_connector_finite
    {r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.retainedInterfaceTrace r ∩ A.connectorTrace r).Finite := by
  apply (Set.finite_singleton (C.interface.curve r)).subset
  rintro p ⟨⟨t, ht, htp⟩, q, hq, hqp⟩
  have htLocal : t ∈ Icc 0 A.localRadius :=
    ⟨hr.le.trans ht.1, ht.2.le.trans hlocal.le⟩
  have hcoords : (0, t) = q := by
    apply A.chart.injective
    calc
      A.chart (0, t) = C.interface.curve t := A.interface_axis t htLocal
      _ = p := htp
      _ = A.chart q := hqp.symm
  have hqFirst : q.1 = 0 := by
    simpa using congrArg Prod.fst hcoords.symm
  have hqSecond : q.2 = r := by
    linarith [hq.2.2]
  have htEq : t = r := by
    simpa [hqSecond] using congrArg Prod.snd hcoords
  simpa only [mem_singleton_iff, htEq] using htp.symm

theorem oldIncidentTrace_inter_oldInterfaceTrace_finite
    {r : ℝ} (_hr : 0 < r) (hlocal : 2 * r < A.localRadius) :
    (A.oldIncidentTrace r ∩ A.oldInterfaceTrace r).Finite := by
  apply (Set.finite_singleton C.junction).subset
  rintro p ⟨⟨s, hs, hsp⟩, t, ht, htp⟩
  have hsLocal : s ∈ Icc 0 A.localRadius :=
    ⟨hs.1, hs.2.le.trans hlocal.le⟩
  have htLocal : t ∈ Icc 0 A.localRadius :=
    ⟨ht.1, ht.2.le.trans hlocal.le⟩
  have hcoords : (s, 0) = (0, t) := by
    apply A.chart.injective
    calc
      A.chart (s, 0) = C.incident.curve s := A.incident_axis s hsLocal
      _ = p := hsp
      _ = C.interface.curve t := htp.symm
      _ = A.chart (0, t) := (A.interface_axis t htLocal).symm
  have hs0 : s = 0 := congrArg Prod.fst hcoords
  simpa only [mem_singleton_iff, hs0, C.incident.curve_zero] using hsp.symm

/-- Exact local cost of the new frontier as the sum of the three literal trace
costs.  No arclength or density price is inserted here. -/
theorem localModel_inside_cost_eq_trace_sum
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    smoothCostOn lam (A.localModel r) (interior (A.window r)) =
      weightedTraceCost lam (A.retainedIncidentTrace r) +
        weightedTraceCost lam (A.retainedInterfaceTrace r) +
          weightedTraceCost lam (A.connectorTrace r) := by
  rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam (A.localModel r) isOpen_interior.measurableSet,
    A.localModel_frontier_inside_window hr hlocal]
  have hincidentInterfaceFinite :
      (A.retainedIncidentTrace r ∩ A.retainedInterfaceTrace r).Finite := by
    rw [(A.retainedIncidentTrace_disjoint_retainedInterfaceTrace hr hlocal).inter_eq]
    exact Set.finite_empty
  have hunionConnectorFinite :
      ((A.retainedIncidentTrace r ∪ A.retainedInterfaceTrace r) ∩
          A.connectorTrace r).Finite := by
    rw [union_inter_distrib_right]
    exact (A.retainedIncidentTrace_inter_connector_finite hr hlocal).union
      (A.retainedInterfaceTrace_inter_connector_finite hr hlocal)
  rw [CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      ((A.measurableSet_retainedIncidentTrace hr.le hlocal.le).union
        (A.measurableSet_retainedInterfaceTrace hr.le hlocal.le))
      (A.measurableSet_connectorTrace hr.le) hunionConnectorFinite,
    CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      (A.measurableSet_retainedIncidentTrace hr.le hlocal.le)
      (A.measurableSet_retainedInterfaceTrace hr.le hlocal.le)
      hincidentInterfaceFinite,
    add_assoc]

/-- Exact local cost of the unchanged frontier as the two old literal trace
costs. -/
theorem representative_inside_cost_eq_trace_sum
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    smoothCostOn lam C.representative (interior (A.window r)) =
      weightedTraceCost lam (A.oldIncidentTrace r) +
        weightedTraceCost lam (A.oldInterfaceTrace r) := by
  rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam C.representative isOpen_interior.measurableSet,
    A.representative_frontier_inside_window hr hlocal,
    CMVRelaxation.FiniteBandRearrangement.weightedTraceCost_union_eq_add_of_inter_finite
      lam
      (A.measurableSet_oldIncidentTrace hr.le hlocal.le)
      (A.measurableSet_oldInterfaceTrace hr.le hlocal.le)
      (A.oldIncidentTrace_inter_oldInterfaceTrace_finite hr hlocal)]

/-- The unchanged interface piece has literal price one.  The separate
`C.radius` premise is required because the chart radius is not silently
identified with the source trace radius. -/
theorem weightedTraceCost_oldInterface_eq_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius) :
    weightedTraceCost lam (A.oldInterfaceTrace r) =
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.oldInterfaceTrace r) := by
  rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam 1 (A.measurableSet_oldInterfaceTrace hr.le hlocal.le)]
  · simp
  · rintro _ ⟨t, ht, rfl⟩
    exact C.interface_stripDensity_eq_one lam
      ⟨ht.1, ht.2.le.trans htrace⟩

/-- The retained interface piece has the same literal price one. -/
theorem weightedTraceCost_retainedInterface_eq_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius) :
    weightedTraceCost lam (A.retainedInterfaceTrace r) =
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' A.retainedInterfaceTrace r) := by
  rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam 1 (A.measurableSet_retainedInterfaceTrace hr.le hlocal.le)]
  · simp
  · rintro _ ⟨t, ht, rfl⟩
    exact C.interface_stripDensity_eq_one lam
      ⟨hr.le.trans ht.1, ht.2.le.trans htrace⟩
/-- Literal interface price combined with exact regular-trace arclength. -/
theorem weightedTraceCost_oldInterface_eq_arcLength
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    weightedTraceCost lam (A.oldInterfaceTrace r) =
      ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
  rw [A.weightedTraceCost_oldInterface_eq_hausdorff lam hr hlocal htrace,
    A.hausdorffMeasure_oldInterfaceTrace_eq_arcLength
      hr.le hlocal.le hregular]

/-- Literal retained-interface price combined with exact regular-trace
arclength. -/
theorem weightedTraceCost_retainedInterface_eq_arcLength_sub
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    weightedTraceCost lam (A.retainedInterfaceTrace r) =
      ENNReal.ofReal
        (C.interface.arcLength (2 * r) - C.interface.arcLength r) := by
  rw [A.weightedTraceCost_retainedInterface_eq_hausdorff
      lam hr hlocal htrace,
    A.hausdorffMeasure_retainedInterfaceTrace_eq_arcLength_sub
      hr.le hlocal.le hregular]


/-! ## Source-side physical phase applicability -/

/-- The physical constant-density side occupied by the incident germ. -/
inductive LocalTracePhase where
  | strip
  | exterior
  deriving DecidableEq

/-- Geometric membership in one of the two literal strip-density phases. -/
def LocalTracePhase.Contains (phase : LocalTracePhase) (p : PlanePoint) : Prop :=
  match phase with
  | .strip => |p.2| ≤ 1
  | .exterior => 1 < |p.2|

/-- Literal density price of a physical phase. -/
def LocalTracePhase.weight (phase : LocalTracePhase) (lam : ℝ) : ℝ :=
  match phase with
  | .strip => 1
  | .exterior => lam

theorem LocalTracePhase.stripDensity_eq_weight
    (phase : LocalTracePhase) (lam : ℝ) {p : PlanePoint}
    (hp : phase.Contains p) :
    StripDensity lam p = phase.weight lam := by
  cases phase with
  | strip =>
      change |p.2| ≤ 1 at hp
      simp [LocalTracePhase.weight, StripDensity, hp]
  | exterior =>
      change 1 < |p.2| at hp
      have hout : ¬|p.2| ≤ 1 := not_le.mpr hp
      simp [LocalTracePhase.weight, StripDensity, hout]

/-- Primitive physical-side information not contained in the topological
corner chart.  It classifies the unchanged chart sector by signed source
height; it contains no competitor, frontier, cost, or contact inequality. -/
structure PhysicalPhaseApplicability where
  phase : LocalTracePhase
  chart_sector_phase :
    ∀ q ∈ openLocalizationSquare (0, 0) A.localRadius,
      0 < q.1 → 0 ≤ q.2 → phase.Contains (A.chart q)

namespace PhysicalPhaseApplicability

variable (P : PhysicalPhaseApplicability A)

/-- The actual incident germ receives its literal strip-density price from the
physical chart sector, not from a supplied cost formula. -/
theorem incident_stripDensity_eq_weight
    (lam : ℝ) {t : ℝ} (ht : t ∈ Ioo 0 A.localRadius) :
    StripDensity lam (C.incident.curve t) = P.phase.weight lam := by
  have hq : (t, 0) ∈ openLocalizationSquare (0, 0) A.localRadius := by
    simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
    exact ⟨⟨by linarith [A.localRadius_pos, ht.1], ht.2⟩,
      ⟨by linarith [A.localRadius_pos], A.localRadius_pos⟩⟩
  have hphase := P.chart_sector_phase (t, 0) hq ht.1 le_rfl
  rw [A.incident_axis t ⟨ht.1.le, ht.2.le⟩] at hphase
  exact P.phase.stripDensity_eq_weight lam hphase
/-- The junction is the only possible exception to the incident phase price on
the complete old half-open germ, and it is `H¹`-null. -/
theorem weightedTraceCost_oldIncident_eq_phase_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    weightedTraceCost lam (A.oldIncidentTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.oldIncidentTrace r) := by
  apply weightedTraceCost_eq_const_mul_hausdorff_except_point
    lam (P.phase.weight lam)
    (A.measurableSet_oldIncidentTrace hr.le hlocal.le) C.junction
  rintro _ ⟨t, ht, rfl⟩ hne
  apply incident_stripDensity_eq_weight A P lam
  have htne : t ≠ 0 := by
    intro ht0
    apply hne
    simpa [ht0] using C.incident.curve_zero
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm htne), ht.2.trans hlocal⟩

/-- The complete old incident cost is its exact arclength times the source
phase price. -/
theorem weightedTraceCost_oldIncident_eq_phase_arcLength
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t) :
    weightedTraceCost lam (A.oldIncidentTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        ENNReal.ofReal (C.incident.arcLength (2 * r)) := by
  rw [weightedTraceCost_oldIncident_eq_phase_hausdorff A P lam hr hlocal,
    A.hausdorffMeasure_oldIncidentTrace_eq_arcLength
      hr.le hlocal.le hregular]


/-- The retained incident piece has the phase price derived from the unchanged
source chart. -/
theorem weightedTraceCost_retainedIncident_eq_phase_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) :
    weightedTraceCost lam (A.retainedIncidentTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.retainedIncidentTrace r) := by
  apply weightedTraceCost_eq_const_mul_hausdorff_of_measurable
    lam (P.phase.weight lam)
    (A.measurableSet_retainedIncidentTrace hr.le hlocal.le)
  rintro _ ⟨t, ht, rfl⟩
  exact incident_stripDensity_eq_weight A P lam
    ⟨hr.trans_le ht.1, ht.2.trans hlocal⟩
/-- Literal incident phase price combined with exact regular-trace
arclength. -/
theorem weightedTraceCost_retainedIncident_eq_phase_arcLength_sub
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius)
    (hregular : ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t) :
    weightedTraceCost lam (A.retainedIncidentTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        ENNReal.ofReal
          (C.incident.arcLength (2 * r) - C.incident.arcLength r) := by
  rw [weightedTraceCost_retainedIncident_eq_phase_hausdorff A P lam hr hlocal,
    A.hausdorffMeasure_retainedIncidentTrace_eq_arcLength_sub
      hr.le hlocal.le hregular]
/-- The actual new local frontier cost with both regular germs replaced by
their exact arclength expressions.  The remaining connector term is still the
literal chart-image trace; no chord-length substitution is made. -/
theorem localModel_inside_cost_eq_phase_arcLength_add_connector
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    smoothCostOn lam (A.localModel r) (interior (A.window r)) =
      ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal
            (C.incident.arcLength (2 * r) - C.incident.arcLength r) +
        ENNReal.ofReal
            (C.interface.arcLength (2 * r) - C.interface.arcLength r) +
          weightedTraceCost lam (A.connectorTrace r) := by
  rw [A.localModel_inside_cost_eq_trace_sum lam hr hlocal,
    weightedTraceCost_retainedIncident_eq_phase_arcLength_sub
      A P lam hr hlocal hincidentRegular,
    A.weightedTraceCost_retainedInterface_eq_arcLength_sub
      lam hr hlocal htrace hinterfaceRegular]



/-- Every non-interface point of the literal connector receives the same
physical price as the incident germ.  The excluded endpoint is the actual
interface point and is `H¹`-null in the later cost identity. -/
theorem connector_stripDensity_eq_weight
    (lam : ℝ) {r t : ℝ} (hr : 0 < r) (hlocal : r < A.localRadius)
    (ht : t ∈ Ioc 0 r) :
    StripDensity lam (A.connectorParam r t) = P.phase.weight lam := by
  have hq : (t, r - t) ∈
      openLocalizationSquare (0, 0) A.localRadius := by
    simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
    constructor
    · exact ⟨by linarith [A.localRadius_pos, ht.1],
        lt_of_le_of_lt ht.2 hlocal⟩
    · constructor
      · linarith [A.localRadius_pos, ht.2]
      · linarith [ht.1, hlocal]
  have hphase := P.chart_sector_phase (t, r - t) hq ht.1
    (by linarith [ht.2])
  exact P.phase.stripDensity_eq_weight lam hphase
/-- The literal connector has the source phase price; its single interface
endpoint is immaterial to `H¹`. -/
theorem weightedTraceCost_connector_eq_phase_hausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : r < A.localRadius) :
    weightedTraceCost lam (A.connectorTrace r) =
      ENNReal.ofReal (P.phase.weight lam) *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.connectorTrace r) := by
  apply weightedTraceCost_eq_const_mul_hausdorff_except_point
    lam (P.phase.weight lam) (A.measurableSet_connectorTrace hr.le)
      (A.connectorParam r 0)
  intro q hq hne
  rw [A.connectorTrace_eq_image_Icc hr.le] at hq
  rcases hq with ⟨t, ht, rfl⟩
  apply connector_stripDensity_eq_weight A P lam hr hlocal
  have htne : t ≠ 0 := by
    intro ht0
    apply hne
    rw [ht0]
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm htne), ht.2⟩

/-- Exact old local frontier cost in phase-weighted regular arclengths. -/
theorem representative_inside_cost_eq_phase_arcLengths
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    smoothCostOn lam C.representative (interior (A.window r)) =
      ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (C.incident.arcLength (2 * r)) +
        ENNReal.ofReal (C.interface.arcLength (2 * r)) := by
  rw [A.representative_inside_cost_eq_trace_sum lam hr hlocal,
    weightedTraceCost_oldIncident_eq_phase_arcLength
      A P lam hr hlocal hincidentRegular,
    A.weightedTraceCost_oldInterface_eq_arcLength
      lam hr hlocal htrace hinterfaceRegular]

/-- Exact new local frontier cost with the connector kept as its literal
Euclidean `H¹` mass. -/
theorem localModel_inside_cost_eq_phase_arcLength_add_connectorHausdorff
    (lam : ℝ) {r : ℝ} (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t) :
    smoothCostOn lam (A.localModel r) (interior (A.window r)) =
      ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal
            (C.incident.arcLength (2 * r) - C.incident.arcLength r) +
        ENNReal.ofReal
            (C.interface.arcLength (2 * r) - C.interface.arcLength r) +
          ENNReal.ofReal (P.phase.weight lam) *
            (μH[1] : Measure EuclideanPlane)
              (planeEuclideanHomeomorph '' A.connectorTrace r) := by
  rw [localModel_inside_cost_eq_phase_arcLength_add_connector
      A P lam hr hlocal htrace hincidentRegular hinterfaceRegular,
    weightedTraceCost_connector_eq_phase_hausdorff
      A P lam hr (by linarith)]


end PhysicalPhaseApplicability
end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison
