import CMVSourceBoundaryContinuation

open Set Function Filter Real
open scoped Topology ContDiff

noncomputable section

namespace CMVSourceFiniteSlabArcInventory

open CMVTwoPatchGraphVariation
open CMVSourceBoundaryContinuation

/-- Abscissae where a horizontal line meets a squared circle equation. -/
def circleHorizontalFiber (center : PlanePoint) (radiusSquared y : ℝ) : Set ℝ :=
  {x | (x - center.1) ^ 2 + (y - center.2) ^ 2 = radiusSquared}

/-- Once one intersection is known, every intersection is it or its reflection
in the vertical diameter. -/
theorem circleHorizontalFiber_subset_pair_of_mem
    {center : PlanePoint} {radiusSquared y x₀ : ℝ}
    (hx₀ : x₀ ∈ circleHorizontalFiber center radiusSquared y) :
    circleHorizontalFiber center radiusSquared y ⊆
      {x₀, 2 * center.1 - x₀} := by
  intro x hx
  simp only [mem_insert_iff, mem_singleton_iff]
  change (x - center.1) ^ 2 + (y - center.2) ^ 2 = radiusSquared at hx
  change (x₀ - center.1) ^ 2 + (y - center.2) ^ 2 = radiusSquared at hx₀
  have hsq : (x - center.1) ^ 2 = (x₀ - center.1) ^ 2 := by
    linarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hsame | hreflect
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A circle has at most two intersections with any horizontal line, including
empty and tangent fibers. -/
theorem circleHorizontalFiber_finite
    (center : PlanePoint) (radiusSquared y : ℝ) :
    (circleHorizontalFiber center radiusSquared y).Finite := by
  by_cases hne : (circleHorizontalFiber center radiusSquared y).Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    exact ({x₀, 2 * center.1 - x₀} : Set ℝ).toFinite.subset
      (circleHorizontalFiber_subset_pair_of_mem hx₀)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

/-- Cardinal form of circle/horizontal-line multiplicity. -/
theorem circleHorizontalFiber_ncard_le_two
    (center : PlanePoint) (radiusSquared y : ℝ) :
    (circleHorizontalFiber center radiusSquared y).ncard ≤ 2 := by
  by_cases hne : (circleHorizontalFiber center radiusSquared y).Nonempty
  · rcases hne with ⟨x₀, hx₀⟩
    calc
      (circleHorizontalFiber center radiusSquared y).ncard ≤
          ({x₀, 2 * center.1 - x₀} : Set ℝ).ncard :=
        Set.ncard_le_ncard (circleHorizontalFiber_subset_pair_of_mem hx₀)
      _ ≤ 2 := by
        exact (Set.ncard_insert_le x₀
          ({2 * center.1 - x₀} : Set ℝ)).trans_eq (by simp)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Two distinct ordered intersections are reflected across the circle center,
and hence select the left and right branches without branch data. -/
theorem ordered_circle_intersections
    {center : PlanePoint} {radiusSquared y xLeft xRight : ℝ}
    (hLeft : xLeft ∈ circleHorizontalFiber center radiusSquared y)
    (hRight : xRight ∈ circleHorizontalFiber center radiusSquared y)
    (horder : xLeft < xRight) :
    xLeft + xRight = 2 * center.1 ∧
      xLeft < center.1 ∧ center.1 < xRight := by
  have hsq : (xLeft - center.1) ^ 2 =
      (xRight - center.1) ^ 2 := by
    change (xLeft - center.1) ^ 2 + (y - center.2) ^ 2 = radiusSquared at hLeft
    change (xRight - center.1) ^ 2 + (y - center.2) ^ 2 = radiusSquared at hRight
    linarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hsame | hreflect
  · exfalso
    linarith
  · constructor
    · linarith
    · constructor <;> linarith

/-- Abscissae where a horizontal line meets an affine support line. -/
def lineHorizontalFiber (point : PlanePoint) (slope y : ℝ) : Set ℝ :=
  {x | y = point.2 + slope * (x - point.1)}

/-- A nonhorizontal line has exactly one point at every height. -/
theorem lineHorizontalFiber_eq_singleton
    {point : PlanePoint} {slope y : ℝ} (hslope : slope ≠ 0) :
    lineHorizontalFiber point slope y =
      {point.1 + (y - point.2) / slope} := by
  ext x
  simp only [lineHorizontalFiber, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro hx
    field_simp [hslope]
    nlinarith
  · intro hx
    rw [hx]
    field_simp [hslope]
    ring

/-- A horizontal support line meets its own height in every abscissa.  This is
the exposed-interface-segment branch, not a finite contact set. -/
theorem lineHorizontalFiber_zero_slope_support_height
    (point : PlanePoint) :
    lineHorizontalFiber point 0 point.2 = Set.univ := by
  ext x
  simp [lineHorizontalFiber]

/-- A horizontal support line has no point at any other height. -/
theorem lineHorizontalFiber_zero_slope_other_height
    {point : PlanePoint} {y : ℝ} (hy : y ≠ point.2) :
    lineHorizontalFiber point 0 y = ∅ := by
  ext x
  simp [lineHorizontalFiber, hy]

/-- Raw contacts are genuinely infinite when a zero-curvature support line
coincides with the queried interface.  A finite slab inventory must count the
maximal exposed segment, not its points. -/
theorem lineHorizontalFiber_zero_slope_support_height_infinite
    (point : PlanePoint) :
    (lineHorizontalFiber point 0 point.2).Infinite := by
  rw [lineHorizontalFiber_zero_slope_support_height]
  exact Set.infinite_univ

/-- The existing zero-curvature support line therefore has one horizontal
intersection whenever its slope is nonzero. -/
theorem supportingLine_horizontalSection_eq_singleton
    {carrier : Set PlanePoint}
    (A : ActualRegularGraphChart carrier) {anchor y : ℝ}
    (hslope : deriv A.patch.graph anchor ≠ 0) :
    CMVSourceClassification.horizontalSection
        (A.patch.supportingLineAt anchor) y =
      {anchor + (y - A.patch.graph anchor) /
        deriv A.patch.graph anchor} := by
  change lineHorizontalFiber (anchor, A.patch.graph anchor)
      (deriv A.patch.graph anchor) y = _
  exact lineHorizontalFiber_eq_singleton hslope

/-- Compactness, when separately established for the actual atlas locus, turns
local constancy into a finite set of supporting carriers. Compactness is not
present in `BranchNeutralGraphAtlas` and must not be inferred from boundedness. -/
theorem supportAt_range_finite_of_compact
    {carrier locus : Set PlanePoint} {K : ℝ} [CompactSpace locus]
    (A : BranchNeutralGraphAtlas carrier locus K) :
    (Set.range A.supportAt).Finite :=
  A.supportAt_isLocallyConstant.range_finite

/-- Set-level wrapper for the compact-locus finiteness route. -/
theorem supportAt_range_finite
    {carrier locus : Set PlanePoint} {K : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K)
    (hcompact : IsCompact locus) :
    (Set.range A.supportAt).Finite := by
  let _ : CompactSpace locus := isCompact_iff_compactSpace.mp hcompact
  exact A.supportAt_isLocallyConstant.range_finite

/-- The support selected by one atlas component has finite horizontal fibers.
For zero curvature the nonhorizontality premise is essential. -/
theorem supportAt_horizontalSection_finite
    {carrier locus : Set PlanePoint} {K y : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus)
    (hline : K = 0 → deriv (A.chart p).patch.graph p.1.1 ≠ 0) :
    (CMVSourceClassification.horizontalSection (A.supportAt p) y).Finite := by
  unfold BranchNeutralGraphAtlas.supportAt
  split_ifs with hK
  · rw [supportingLine_horizontalSection_eq_singleton
      (A.chart p) (hline hK)]
    exact Set.finite_singleton _
  · change (circleHorizontalFiber
      ((A.chart p).patch.supportingCenter K p.1.1)
      ((1 / ((A.chart p).patch.side.areaSign * K)) ^ 2) y).Finite
    exact circleHorizontalFiber_finite _ _ _

/-- Multiplicity form: one nonhorizontal line point in the flat case, and at
most two circle points in the curved case. -/
theorem supportAt_horizontalSection_ncard_le_two
    {carrier locus : Set PlanePoint} {K y : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus)
    (hline : K = 0 → deriv (A.chart p).patch.graph p.1.1 ≠ 0) :
    (CMVSourceClassification.horizontalSection (A.supportAt p) y).ncard ≤ 2 := by
  unfold BranchNeutralGraphAtlas.supportAt
  split_ifs with hK
  · rw [supportingLine_horizontalSection_eq_singleton
      (A.chart p) (hline hK)]
    simp
  · change (circleHorizontalFiber
      ((A.chart p).patch.supportingCenter K p.1.1)
      ((1 / ((A.chart p).patch.side.areaSign * K)) ^ 2) y).ncard ≤ 2
    exact circleHorizontalFiber_ncard_le_two _ _ _

/-- Abscissae of the maximal actual continuation component at height `y`. -/
def maximalComponentHorizontalFiber
    {carrier locus : Set PlanePoint} {K : ℝ}
    (_A : BranchNeutralGraphAtlas carrier locus K) (p : locus) (y : ℝ) : Set ℝ :=
  CMVSourceClassification.horizontalSection
    (connectedComponentIn locus p.1) y

/-- The maximal component is contained in the one support selected at any
base point of that component. -/
theorem maximalComponentHorizontalFiber_subset_support
    {carrier locus : Set PlanePoint} {K y : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    maximalComponentHorizontalFiber A p y ⊆
      CMVSourceClassification.horizontalSection (A.supportAt p) y := by
  intro x hx
  change (x, y) ∈ connectedComponentIn locus p.1 at hx
  change (x, y) ∈ A.supportAt p
  rw [connectedComponentIn_eq_image p.2] at hx
  exact A.connectedComponent_subset_supportAt p hx

/-- Finiteness is derived separately for each maximal support carrier; no
finiteness of the atlas, its components, or its supporting carriers is used. -/
theorem maximalComponentHorizontalFiber_finite
    {carrier locus : Set PlanePoint} {K y : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus)
    (hline : K = 0 → deriv (A.chart p).patch.graph p.1.1 ≠ 0) :
    (maximalComponentHorizontalFiber A p y).Finite := by
  exact (supportAt_horizontalSection_finite A p hline).subset
    (maximalComponentHorizontalFiber_subset_support A p)

/-- Every transverse horizontal section of one maximal continuation component
has multiplicity at most two, without a global finite arc list. -/
theorem maximalComponentHorizontalFiber_ncard_le_two
    {carrier locus : Set PlanePoint} {K y : ℝ}
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus)
    (hline : K = 0 → deriv (A.chart p).patch.graph p.1.1 ≠ 0) :
    (maximalComponentHorizontalFiber A p y).ncard ≤ 2 := by
  calc
    (maximalComponentHorizontalFiber A p y).ncard ≤
        (CMVSourceClassification.horizontalSection (A.supportAt p) y).ncard :=
      Set.ncard_le_ncard (maximalComponentHorizontalFiber_subset_support A p)
        (supportAt_horizontalSection_finite A p hline)
    _ ≤ 2 := supportAt_horizontalSection_ncard_le_two A p hline

/-- Actual planar frontier points visible in a horizontal section.  Tangencies
that do not enter the one-dimensional section frontier are deliberately absent. -/
def sectionVisibleFrontier (U : Set PlanePoint) (y : ℝ) : Set PlanePoint :=
  {p | p.2 = y ∧
    p.1 ∈ frontier (CMVSourceClassification.horizontalSection U y)}

/-- An exact nonempty interval section has exactly two visible planar frontier
points.  This is a section theorem, not a claim about all planar tangencies. -/
theorem sectionVisibleFrontier_eq_pair_of_section_eq_Ioo
    {U : Set PlanePoint} {y left right : ℝ}
    (horder : left < right)
    (hsection : CMVSourceClassification.horizontalSection U y =
      Ioo left right) :
    sectionVisibleFrontier U y = {(left, y), (right, y)} := by
  ext p
  simp only [sectionVisibleFrontier, mem_ofPred_eq, mem_insert_iff,
    mem_singleton_iff]
  rw [hsection, frontier_Ioo horder]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hpy, hp⟩
    rcases hp with hp | hp
    · exact Or.inl (Prod.ext hp hpy)
    · exact Or.inr (Prod.ext hp hpy)
  · rintro (hp | hp)
    · rw [hp]
      exact ⟨rfl, Or.inl rfl⟩
    · rw [hp]
      exact ⟨rfl, Or.inr rfl⟩

/-- Every section-visible point is an actual planar frontier point. -/
theorem sectionVisibleFrontier_subset_frontier
    (U : Set PlanePoint) (y : ℝ) :
    sectionVisibleFrontier U y ⊆ frontier U := by
  intro p hp
  have hfrontier :=
    CMVSourceClassification.frontier_horizontalSection_subset U y hp.2
  change (p.1, y) ∈ frontier U at hfrontier
  change (p.1, p.2) ∈ frontier U
  rw [hp.1]
  exact hfrontier

/-- A transverse locally one-sided circle point on an actual interval section
must be one of its two endpoints. -/
theorem transverse_circle_point_eq_interval_endpoint
    {U : Set PlanePoint} {center p : PlanePoint} {radius left right : ℝ}
    (horder : left < right)
    (hsection : CMVSourceClassification.horizontalSection U p.2 =
      Ioo left right)
    (hcircle : CMVFigureFour.circleValue center radius p = 0)
    (htransverse : p.1 ≠ center.1)
    (hlocal : CMVFigureFour.LocallyOneSided U center radius p) :
    p.1 = left ∨ p.1 = right := by
  have hp := CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
    hcircle htransverse hlocal
  rw [hsection, frontier_Ioo horder] at hp
  simpa only [mem_insert_iff, mem_singleton_iff] using hp

/-- Two ordered transverse locally one-sided circle points, possibly on
unselected distinct supports, are forced to be the left and right endpoints. -/
theorem ordered_transverse_circle_points_are_interval_endpoints
    {U : Set PlanePoint} {p q centerP centerQ : PlanePoint}
    {radiusP radiusQ left right : ℝ}
    (hleft_le_right : left ≤ right)
    (hsection : CMVSourceClassification.horizontalSection U p.2 = Ioo left right)
    (hsameHeight : q.2 = p.2)
    (hpCircle : CMVFigureFour.circleValue centerP radiusP p = 0)
    (hqCircle : CMVFigureFour.circleValue centerQ radiusQ q = 0)
    (hpTransverse : p.1 ≠ centerP.1)
    (hqTransverse : q.1 ≠ centerQ.1)
    (hpLocal : CMVFigureFour.LocallyOneSided U centerP radiusP p)
    (hqLocal : CMVFigureFour.LocallyOneSided U centerQ radiusQ q)
    (hpq : p.1 < q.1) :
    left = p.1 ∧ right = q.1 := by
  have hpFrontier :=
    CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hpCircle hpTransverse hpLocal
  have hqFrontierAtQ :=
    CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hqCircle hqTransverse hqLocal
  have hqFrontier : q.1 ∈ frontier
      (CMVSourceClassification.horizontalSection U p.2) := by
    simpa only [hsameHeight] using hqFrontierAtQ
  exact CMVFigureFour.openInterval_endpoints_of_ordered_frontier
    hleft_le_right hsection hpFrontier hqFrontier hpq

end CMVSourceFiniteSlabArcInventory
