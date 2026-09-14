import CMVFiniteJunctionRepair
import CMVRelativeLevelTraceAveraging

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement

/-- Branch-neutral finite-band data for horizontal Schwarz rearrangement.

The endpoint functions are global continuous representatives of the graphs on
one closed height band.  Only their restrictions to the indicated band enter
the carrier.  Components may collapse or meet at an endpoint, but are strictly
positive and separated at every interior height.  The `C¹` and integrability
fields are retained for literal frontier-cost accounting; none is used to
postulate a frontier formula. -/
structure Region where
  bandCount : ℕ
  bandCount_pos : 0 < bandCount
  cuts : Fin (bandCount + 1) → ℝ
  cuts_strict : StrictMono cuts
  componentCount : Fin bandCount → ℕ
  componentCount_pos : ∀ i, 0 < componentCount i
  left : (i : Fin bandCount) → Fin (componentCount i) → ℝ → ℝ
  right : (i : Fin bandCount) → Fin (componentCount i) → ℝ → ℝ
  left_continuous : ∀ i j, Continuous (left i j)
  right_continuous : ∀ i j, Continuous (right i j)
  left_contDiffOn : ∀ i j,
    ContDiffOn ℝ 1 (left i j) (Ioo (cuts i.castSucc) (cuts i.succ))
  right_contDiffOn : ∀ i j,
    ContDiffOn ℝ 1 (right i j) (Ioo (cuts i.castSucc) (cuts i.succ))
  left_speed_integrable : ∀ i j,
    IntegrableOn (fun y => Real.sqrt (1 + deriv (left i j) y ^ 2))
      (Ioo (cuts i.castSucc) (cuts i.succ))
  right_speed_integrable : ∀ i j,
    IntegrableOn (fun y => Real.sqrt (1 + deriv (right i j) y ^ 2))
      (Ioo (cuts i.castSucc) (cuts i.succ))
  width_nonneg : ∀ i j y,
    y ∈ Icc (cuts i.castSucc) (cuts i.succ) → left i j y ≤ right i j y
  width_pos : ∀ i j y,
    y ∈ Ioo (cuts i.castSucc) (cuts i.succ) → left i j y < right i j y
  components_ordered : ∀ i {j k}, j < k → ∀ y,
    y ∈ Icc (cuts i.castSucc) (cuts i.succ) → right i j y ≤ left i k y
  components_strict : ∀ i {j k}, j < k → ∀ y,
    y ∈ Ioo (cuts i.castSucc) (cuts i.succ) → right i j y < left i k y

namespace Region

/-- One literal closed graph component, using the previously checked horizontal
band primitive. -/
def componentCarrier (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  FiniteJunctionRepair.closedHorizontalGraphBand (R.left i j) (R.right i j)
    (Icc (R.cuts i.castSucc) (R.cuts i.succ))

/-- Literal union of all components in one closed height band. -/
def bandCarrier (R : Region) (i : Fin R.bandCount) : Set PlanePoint :=
  ⋃ j : Fin (R.componentCount i), R.componentCarrier i j

/-- Original literal finite-band carrier.  Adjacent closed bands both contribute
at their common cut, so the section there is their actual trace union. -/
def carrier (R : Region) : Set PlanePoint :=
  ⋃ i : Fin R.bandCount, R.bandCarrier i

/-- Actual closed one-sided section union of a band at a height. -/
def fiber (R : Region) (i : Fin R.bandCount) (y : ℝ) : Set ℝ :=
  ⋃ j : Fin (R.componentCount i), Icc (R.left i j y) (R.right i j y)

/-- Finite set of all interval endpoints in one actual one-sided section. -/
def fiberEndpoints (R : Region) (i : Fin R.bandCount) (y : ℝ) : Set ℝ :=
  Set.range (fun j : Fin (R.componentCount i) => R.left i j y) ∪
    Set.range (fun j : Fin (R.componentCount i) => R.right i j y)

/-- Total section width, counted componentwise.  Interior strict separation
makes this equal to the Lebesgue measure of `fiber`; that measure theorem is a
later cost/area layer. -/
def totalWidth (R : Region) (i : Fin R.bandCount) (y : ℝ) : ℝ :=
  ∑ j : Fin (R.componentCount i), (R.right i j y - R.left i j y)

/-- Centered closed interval with the same componentwise total width. -/
def centeredFiber (R : Region) (i : Fin R.bandCount) (y : ℝ) : Set ℝ :=
  Icc (-R.totalWidth i y / 2) (R.totalWidth i y / 2)

/-- Literal centered graph band for one original band. -/
def centeredBandCarrier (R : Region) (i : Fin R.bandCount) : Set PlanePoint :=
  FiniteJunctionRepair.closedHorizontalGraphBand
    (fun y => -R.totalWidth i y / 2) (fun y => R.totalWidth i y / 2)
    (Icc (R.cuts i.castSucc) (R.cuts i.succ))

/-- Literal centered finite-band competitor. -/
def centeredCarrier (R : Region) : Set PlanePoint :=
  ⋃ i : Fin R.bandCount, R.centeredBandCarrier i

/-- Closed endpoint graph of one component.  Endpoint coincidences are retained
rather than silently deleted. -/
def leftGraphTrace (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  (fun y => (R.left i j y, y)) '' Icc (R.cuts i.castSucc) (R.cuts i.succ)

/-- Closed right endpoint graph of one component. -/
def rightGraphTrace (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  (fun y => (R.right i j y, y)) '' Icc (R.cuts i.castSucc) (R.cuts i.succ)

/-- Closed lower end trace of one component, including a possible singleton. -/
def lowerEndTrace (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  Icc (R.left i j (R.cuts i.castSucc)) (R.right i j (R.cuts i.castSucc)) ×ˢ
    {R.cuts i.castSucc}

/-- Closed upper end trace of one component, including a possible singleton. -/
def upperEndTrace (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  Icc (R.left i j (R.cuts i.succ)) (R.right i j (R.cuts i.succ)) ×ˢ
    {R.cuts i.succ}

/-- Complete candidate frontier of a single closed graph component. -/
def componentFrontierTrace (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : Set PlanePoint :=
  (R.leftGraphTrace i j ∪ R.rightGraphTrace i j) ∪
    (R.lowerEndTrace i j ∪ R.upperEndTrace i j)

/-- Union of all complete component traces in one band. -/
def bandComponentFrontierTrace (R : Region) (i : Fin R.bandCount) :
    Set PlanePoint :=
  ⋃ j : Fin (R.componentCount i), R.componentFrontierTrace i j

/-- Raw finite union of every component frontier.  Internal overlaps are still
present here; later seam accounting removes precisely their filled interiors. -/
def rawComponentFrontierTrace (R : Region) : Set PlanePoint :=
  ⋃ i : Fin R.bandCount, R.bandComponentFrontierTrace i

/-- Lower band incident to an internal seam. -/
def seamLowerBand (R : Region) (i : Fin (R.bandCount - 1)) : Fin R.bandCount :=
  ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le ..)⟩

/-- Upper band incident to an internal seam. -/
def seamUpperBand (R : Region) (i : Fin (R.bandCount - 1)) : Fin R.bandCount :=
  ⟨i + 1, by omega⟩

/-- Height of an internal seam. -/
def seamHeight (R : Region) (i : Fin (R.bandCount - 1)) : ℝ :=
  R.cuts (R.seamUpperBand i).castSucc

/-- The positive-length part of an internal horizontal seam is the symmetric
difference of its two actual one-sided closed section unions.  Finite endpoint
remainders are accounted for by the closed endpoint graphs. -/
def seamSymmDiff (R : Region) (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧
    p.1 ∈ R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
      R.fiber (R.seamUpperBand i) (R.seamHeight i)}

/-- Finite endpoint correction at an internal seam.  These points are retained
by the closed endpoint graphs even when they do not belong to the set-theoretic
symmetric difference. -/
def seamEndpointSet (R : Region) (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  (fun x => (x, R.seamHeight i)) ''
    (R.fiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
      R.fiberEndpoints (R.seamUpperBand i) (R.seamHeight i))

/-- One-dimensional closed seam boundary derived from the actual traces: points
present on at least one side, except those interior to both side fibers. -/
def seamBoundaryFiber (R : Region) (i : Fin (R.bandCount - 1)) : Set ℝ :=
  let lower := R.fiber (R.seamLowerBand i) (R.seamHeight i)
  let upper := R.fiber (R.seamUpperBand i) (R.seamHeight i)
  (lower ∪ upper) \ (interior lower ∩ interior upper)

/-- Lift of the derived one-dimensional seam boundary to its actual height. -/
def seamBoundaryTrace (R : Region) (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧ p.1 ∈ R.seamBoundaryFiber i}

/-- Membership in a literal component uses the ordered endpoints, not `min` and
`max`, at every active height. -/
theorem mem_componentCarrier_iff (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) (p : PlanePoint) :
    p ∈ R.componentCarrier i j ↔
      p.2 ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
        p.1 ∈ Icc (R.left i j p.2) (R.right i j p.2) := by
  simp only [componentCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand, mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hx⟩
    have hle := R.width_nonneg i j p.2 hy
    rw [min_eq_left hle, max_eq_right hle] at hx
    exact ⟨hy, hx⟩
  · rintro ⟨hy, hx⟩
    have hle := R.width_nonneg i j p.2 hy
    rw [min_eq_left hle, max_eq_right hle]
    exact ⟨hy, hx⟩

/-- Strict graph inequalities at an interior height give a genuine planar
interior point of the literal component. -/
theorem mem_interior_componentCarrier_of_strict (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) (p : PlanePoint)
    (hy : p.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hx : p.1 ∈ Ioo (R.left i j p.2) (R.right i j p.2)) :
    p ∈ interior (R.componentCarrier i j) := by
  let U : Set PlanePoint :=
    {q | (q.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∧
      R.left i j q.2 < q.1) ∧ q.1 < R.right i j q.2}
  have hUopen : IsOpen U := by
    exact ((isOpen_Ioo.preimage continuous_snd).inter
      (isOpen_lt ((R.left_continuous i j).comp continuous_snd)
        continuous_fst)).inter
      (isOpen_lt continuous_fst
        ((R.right_continuous i j).comp continuous_snd))
  have hpU : p ∈ U := ⟨⟨hy, hx.1⟩, hx.2⟩
  have hUsub : U ⊆ R.componentCarrier i j := by
    intro q hq
    rw [R.mem_componentCarrier_iff]
    exact ⟨⟨hq.1.1.1.le, hq.1.1.2.le⟩, ⟨hq.1.2.le, hq.2.le⟩⟩
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hUopen.mem_nhds hpU) hUsub)

/-- Exact horizontal section of one literal component. -/
theorem horizontalSection_componentCarrier (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) (y : ℝ) :
    horizontalSection (R.componentCarrier i j) y =
      if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then
        Icc (R.left i j y) (R.right i j y)
      else ∅ := by
  ext x
  rw [show x ∈ horizontalSection (R.componentCarrier i j) y ↔
      (x, y) ∈ R.componentCarrier i j from Iff.rfl,
    R.mem_componentCarrier_iff]
  by_cases hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
  · simp [hy]
  · simp [hy]

/-- Exact horizontal section of one finite component union. -/
theorem horizontalSection_bandCarrier (R : Region) (i : Fin R.bandCount)
    (y : ℝ) :
    horizontalSection (R.bandCarrier i) y =
      if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then R.fiber i y else ∅ := by
  rw [bandCarrier]
  change (fun x : ℝ => (x, y)) ⁻¹' (⋃ j, R.componentCarrier i j) = _
  rw [preimage_iUnion]
  change (⋃ j, horizontalSection (R.componentCarrier i j) y) = _
  simp_rw [R.horizontalSection_componentCarrier]
  by_cases hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
  · simp only [hy, if_true, fiber]
  · simp only [hy, if_false, iUnion_empty]

/-- Exact section formula at every height, including all cuts.  At an internal
cut this is literally the union of both adjacent one-sided traces. -/
theorem horizontalSection_carrier (R : Region) (y : ℝ) :
    horizontalSection R.carrier y =
      ⋃ i : Fin R.bandCount,
        if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then R.fiber i y else ∅ := by
  rw [carrier]
  change (fun x : ℝ => (x, y)) ⁻¹' (⋃ i, R.bandCarrier i) = _
  rw [preimage_iUnion]
  change (⋃ i, horizontalSection (R.bandCarrier i) y) = _
  simp_rw [R.horizontalSection_bandCarrier]
private theorem frontier_biUnion_finset_subset
    {ι X : Type*} [TopologicalSpace X]
    (J : Finset ι) (T : ι → Set X) :
    frontier (⋃ p ∈ J, T p) ⊆ ⋃ p ∈ J, frontier (T p) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert p J hp ih =>
      have hsets :
          (⋃ q ∈ insert p J, T q) = T p ∪ ⋃ q ∈ J, T q := by
        ext x
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨q, hq, hxq⟩
          rcases hq with rfl | hq
          · exact Or.inl hxq
          · exact Or.inr ⟨q, hq, hxq⟩
        · rintro (hxp | ⟨q, hq, hxq⟩)
          · exact ⟨p, Or.inl rfl, hxp⟩
          · exact ⟨q, Or.inr hq, hxq⟩
      rw [hsets]
      intro x hx
      rcases frontier_union_subset (T p) (⋃ q ∈ J, T q) hx with hx | hx
      · simp only [mem_iUnion, Finset.mem_insert]
        exact ⟨p, Or.inl rfl, hx.1⟩
      · have hxJ := ih hx.2
        simp only [mem_iUnion, Finset.mem_insert] at hxJ ⊢
        rcases hxJ with ⟨q, hqJ, hxq⟩
        exact ⟨q, Or.inr hqJ, hxq⟩

/-- Actual one-sided fibers are closed finite unions. -/
theorem isClosed_fiber (R : Region) (i : Fin R.bandCount) (y : ℝ) :
    IsClosed (R.fiber i y) := by
  unfold fiber
  exact isClosed_iUnion_of_finite fun _ => isClosed_Icc

/-- Every one-dimensional fiber-frontier point is one of the finite graph
endpoints.  This also covers reversed inactive representatives and degenerate
limiting intervals. -/
theorem frontier_fiber_subset_fiberEndpoints (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    frontier (R.fiber i y) ⊆ R.fiberEndpoints i y := by
  rw [show R.fiber i y =
      ⋃ j ∈ (Finset.univ : Finset (Fin (R.componentCount i))),
        Icc (R.left i j y) (R.right i j y) by
    simp [fiber]]
  intro x hx
  have hx' := frontier_biUnion_finset_subset
    (Finset.univ : Finset (Fin (R.componentCount i)))
    (fun j => Icc (R.left i j y) (R.right i j y)) hx
  simp only [mem_iUnion] at hx'
  rcases hx' with ⟨j, _hjmem, hxj⟩
  by_cases hj : R.left i j y ≤ R.right i j y
  · rw [frontier_Icc hj] at hxj
    have hxj' : x = R.left i j y ∨ x = R.right i j y := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hxj
    rcases hxj' with hxj' | hxj'
    · subst x
      exact Or.inl ⟨j, rfl⟩
    · subst x
      exact Or.inr ⟨j, rfl⟩
  · rw [Icc_eq_empty hj, frontier_empty] at hxj
    exact hxj.elim

/-- The symmetric difference is always part of the seam boundary obtained from
the two actual closed traces. -/
theorem symmDiff_subset_seamBoundaryFiber (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.fiber (R.seamUpperBand i) (R.seamHeight i) ⊆
      R.seamBoundaryFiber i := by
  let A := R.fiber (R.seamLowerBand i) (R.seamHeight i)
  let B := R.fiber (R.seamUpperBand i) (R.seamHeight i)
  change A ∆ B ⊆ (A ∪ B) \ (interior A ∩ interior B)
  intro x hx
  rcases hx with hx | hx
  · exact ⟨Or.inl hx.1, fun hi => hx.2 (interior_subset hi.2)⟩
  · exact ⟨Or.inr hx.1, fun hi => hx.2 (interior_subset hi.1)⟩

/-- Conversely, every seam-boundary point outside the symmetric difference is
a frontier point of one side fiber and hence belongs to the finite endpoint
correction. -/
theorem seamBoundaryFiber_subset_symmDiff_union_endpoints (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamBoundaryFiber i ⊆
      (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.fiber (R.seamUpperBand i) (R.seamHeight i)) ∪
      (R.fiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
        R.fiberEndpoints (R.seamUpperBand i) (R.seamHeight i)) := by
  let A := R.fiber (R.seamLowerBand i) (R.seamHeight i)
  let B := R.fiber (R.seamUpperBand i) (R.seamHeight i)
  change (A ∪ B) \ (interior A ∩ interior B) ⊆
    (A ∆ B) ∪
      (R.fiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
        R.fiberEndpoints (R.seamUpperBand i) (R.seamHeight i))
  intro x hx
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · by_cases hAi : x ∈ interior A
      · have hBni : x ∉ interior B := fun hBi => hx.2 ⟨hAi, hBi⟩
        have hFrontB : x ∈ frontier B := by
          rw [(R.isClosed_fiber (R.seamUpperBand i)
            (R.seamHeight i)).frontier_eq]
          exact ⟨hB, hBni⟩
        exact Or.inr (Or.inr
          (R.frontier_fiber_subset_fiberEndpoints
            (R.seamUpperBand i) (R.seamHeight i) hFrontB))
      · have hFrontA : x ∈ frontier A := by
          rw [(R.isClosed_fiber (R.seamLowerBand i)
            (R.seamHeight i)).frontier_eq]
          exact ⟨hA, hAi⟩
        exact Or.inr (Or.inl
          (R.frontier_fiber_subset_fiberEndpoints
            (R.seamLowerBand i) (R.seamHeight i) hFrontA))
    · exact Or.inl (Or.inl ⟨hA, hB⟩)
  · have hB : x ∈ B := hx.1.resolve_left hA
    exact Or.inl (Or.inr ⟨hB, hA⟩)

/-- Lifted generic seam accounting: the actual symmetric-difference trace is
contained in the derived seam boundary. -/
theorem seamSymmDiff_subset_seamBoundaryTrace (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamSymmDiff i ⊆ R.seamBoundaryTrace i := by
  rintro p ⟨hy, hx⟩
  exact ⟨hy, R.symmDiff_subset_seamBoundaryFiber i hx⟩

/-- The derived seam boundary differs from the actual one-sided symmetric
difference only by the proved finite endpoint set. -/
theorem seamBoundaryTrace_subset_symmDiff_union_endpoints (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamBoundaryTrace i ⊆ R.seamSymmDiff i ∪ R.seamEndpointSet i := by
  rintro p ⟨hy, hx⟩
  rcases R.seamBoundaryFiber_subset_symmDiff_union_endpoints i hx with hs | he
  · exact Or.inl ⟨hy, hs⟩
  · refine Or.inr ⟨p.1, he, ?_⟩
    exact Prod.ext rfl hy.symm

/-- The endpoint correction in any actual one-sided fiber is finite. -/
theorem fiberEndpoints_finite (R : Region) (i : Fin R.bandCount) (y : ℝ) :
    (R.fiberEndpoints i y).Finite :=
  Set.Finite.union (Set.finite_range _) (Set.finite_range _)

/-- Every internal seam endpoint correction is finite. -/
theorem seamEndpointSet_finite (R : Region) (i : Fin (R.bandCount - 1)) :
    (R.seamEndpointSet i).Finite := by
  exact ((R.fiberEndpoints_finite (R.seamLowerBand i) (R.seamHeight i)).union
    (R.fiberEndpoints_finite (R.seamUpperBand i) (R.seamHeight i))).image _

/-- Finite seam endpoint corrections carry no Euclidean `H¹` cost. -/
theorem hausdorffMeasure_seamEndpointSet (R : Region)
    (i : Fin (R.bandCount - 1)) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' R.seamEndpointSet i) = 0 := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  exact (R.seamEndpointSet_finite i).image planeEuclideanHomeomorph
    |>.measure_zero μH[1]

/-- A limiting component with coincident endpoints is the expected singleton,
not an empty or orientation-reversed interval. -/
theorem componentInterval_eq_singleton_of_eq (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) (y : ℝ)
    (h : R.left i j y = R.right i j y) :
    Icc (R.left i j y) (R.right i j y) = {R.left i j y} := by
  simp [h]


/-- Every active total width is nonnegative, including degenerate limiting
components. -/
theorem totalWidth_nonneg (R : Region) (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    0 ≤ R.totalWidth i y := by
  unfold totalWidth
  exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (R.width_nonneg i j y hy)

/-- Exact section of one centered band. -/
theorem horizontalSection_centeredBandCarrier (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    horizontalSection (R.centeredBandCarrier i) y =
      if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then
        R.centeredFiber i y
      else ∅ := by
  ext x
  simp only [horizontalSection, centeredBandCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand, mem_preimage, mem_ofPred_eq]
  by_cases hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
  · have hw := R.totalWidth_nonneg i hy
    simp [hy, centeredFiber, min_eq_left (by linarith : -R.totalWidth i y / 2 ≤
      R.totalWidth i y / 2), max_eq_right (by linarith : -R.totalWidth i y / 2 ≤
      R.totalWidth i y / 2)]
  · simp [hy]

/-- Exact section formula for the literal centered carrier, including cuts. -/
theorem horizontalSection_centeredCarrier (R : Region) (y : ℝ) :
    horizontalSection R.centeredCarrier y =
      ⋃ i : Fin R.bandCount,
        if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then
          R.centeredFiber i y
        else ∅ := by
  rw [centeredCarrier]
  change (fun x : ℝ => (x, y)) ⁻¹' (⋃ i, R.centeredBandCarrier i) = _
  rw [preimage_iUnion]
  change (⋃ i, horizontalSection (R.centeredBandCarrier i) y) = _
  simp_rw [R.horizontalSection_centeredBandCarrier]

/-- Componentwise summation preserves global endpoint continuity. -/
theorem continuous_totalWidth (R : Region) (i : Fin R.bandCount) :
    Continuous (R.totalWidth i) := by
  unfold totalWidth
  exact continuous_finsetSum Finset.univ fun j _ =>
    (R.right_continuous i j).sub (R.left_continuous i j)

/-- Membership in the centered band uses the actual centered interval,
including when its width degenerates at a cut. -/
theorem mem_centeredBandCarrier_iff (R : Region) (i : Fin R.bandCount)
    (p : PlanePoint) :
    p ∈ R.centeredBandCarrier i ↔
      p.2 ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
        p.1 ∈ R.centeredFiber i p.2 := by
  simp only [centeredBandCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand, centeredFiber, mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hx⟩
    have hw := R.totalWidth_nonneg i hy
    have horder : -R.totalWidth i p.2 / 2 ≤ R.totalWidth i p.2 / 2 := by
      linarith
    rw [min_eq_left horder, max_eq_right horder] at hx
    exact ⟨hy, hx⟩
  · rintro ⟨hy, hx⟩
    have hw := R.totalWidth_nonneg i hy
    have horder : -R.totalWidth i p.2 / 2 ≤ R.totalWidth i p.2 / 2 := by
      linarith
    rw [min_eq_left horder, max_eq_right horder]
    exact ⟨hy, hx⟩

/-- Each centered graph band is closed. -/
theorem isClosed_centeredBandCarrier (R : Region) (i : Fin R.bandCount) :
    IsClosed (R.centeredBandCarrier i) := by
  rw [show R.centeredBandCarrier i =
      {p : PlanePoint |
        (p.2 ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
          -R.totalWidth i p.2 / 2 ≤ p.1) ∧
            p.1 ≤ R.totalWidth i p.2 / 2} by
    ext p
    rw [R.mem_centeredBandCarrier_iff]
    simp only [centeredFiber, mem_Icc, mem_ofPred_eq]
    tauto]
  have hw : Continuous (R.totalWidth i) := R.continuous_totalWidth i
  exact ((isClosed_Icc.preimage continuous_snd).inter
    (isClosed_le ((hw.comp continuous_snd).neg.div_const 2) continuous_fst)).inter
      (isClosed_le continuous_fst ((hw.comp continuous_snd).div_const 2))

/-- The literal centered finite-band carrier is closed. -/
theorem isClosed_centeredCarrier (R : Region) : IsClosed R.centeredCarrier := by
  unfold centeredCarrier
  exact isClosed_iUnion_of_finite fun i => R.isClosed_centeredBandCarrier i

/-- Literal components are closed; this is derived from endpoint continuity and
ordered graph inequalities. -/
theorem isClosed_componentCarrier (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) : IsClosed (R.componentCarrier i j) := by
  rw [show R.componentCarrier i j =
      {p : PlanePoint |
        (p.2 ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
          R.left i j p.2 ≤ p.1) ∧ p.1 ≤ R.right i j p.2} by
    ext p
    rw [R.mem_componentCarrier_iff]
    simp only [mem_Icc, mem_ofPred_eq]
    tauto]
  exact ((isClosed_Icc.preimage continuous_snd).inter
    (isClosed_le ((R.left_continuous i j).comp continuous_snd) continuous_fst)).inter
      (isClosed_le continuous_fst ((R.right_continuous i j).comp continuous_snd))

/-- Every frontier point of a generic component lies on one of its two endpoint
graphs or one of its two literal end traces.  No frontier equation is assumed. -/
theorem frontier_componentCarrier_subset_componentFrontierTrace (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    frontier (R.componentCarrier i j) ⊆ R.componentFrontierTrace i j := by
  rintro ⟨x, y⟩ hp
  rw [(R.isClosed_componentCarrier i j).frontier_eq] at hp
  rcases hp with ⟨hmem, hnotInterior⟩
  rw [R.mem_componentCarrier_iff] at hmem
  change y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
    x ∈ Icc (R.left i j y) (R.right i j y) at hmem
  change (x, y) ∈
    (R.leftGraphTrace i j ∪ R.rightGraphTrace i j) ∪
      (R.lowerEndTrace i j ∪ R.upperEndTrace i j)
  rcases hmem.1.1.eq_or_lt with hya | hya
  · subst y
    exact Or.inr (Or.inl ⟨hmem.2, rfl⟩)
  · rcases hmem.1.2.eq_or_lt with hyb | hyb
    · subst y
      exact Or.inr (Or.inr ⟨hmem.2, rfl⟩)
    · rcases hmem.2.1.eq_or_lt with hxl | hxl
      · subst x
        exact Or.inl (Or.inl
          ⟨y, ⟨hya.le, hyb.le⟩, rfl⟩)
      · rcases hmem.2.2.eq_or_lt with hxr | hxr
        · subst x
          exact Or.inl (Or.inr
            ⟨y, ⟨hya.le, hyb.le⟩, rfl⟩)
        · exact False.elim (hnotInterior
            (R.mem_interior_componentCarrier_of_strict i j (x, y)
              ⟨hya, hyb⟩ ⟨hxl, hxr⟩))

private theorem mem_frontier_of_escape
    {S : Set PlanePoint} (hS : IsClosed S) {p : PlanePoint} (hp : p ∈ S)
    (q : ℕ → PlanePoint) (hq : ∀ n, q n ∉ S)
    (hlim : Tendsto q atTop (𝓝 p)) : p ∈ frontier S := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · simpa only [hS.closure_eq] using hp
  · apply mem_closure_of_tendsto hlim
    filter_upwards [] with n
    exact hq n

private theorem escapeScale_pos (n : ℕ) : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
  positivity

private theorem escapeScale_tendsto :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every listed endpoint graph and end trace is an actual frontier point of
the single component.  Escape sequences prove this even when an end interval
degenerates to a singleton. -/
theorem componentFrontierTrace_subset_frontier_componentCarrier (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.componentFrontierTrace i j ⊆ frontier (R.componentCarrier i j) := by
  unfold componentFrontierTrace
  apply union_subset
  · apply union_subset
    · rintro _ ⟨y, hy, rfl⟩
      let q : ℕ → PlanePoint :=
        fun n => (R.left i j y - 1 / (n + 1 : ℝ), y)
      apply mem_frontier_of_escape (R.isClosed_componentCarrier i j)
        (R.mem_componentCarrier_iff i j _ |>.2
          ⟨hy, ⟨le_rfl, R.width_nonneg i j y hy⟩⟩) q
      · intro n hqn
        rw [R.mem_componentCarrier_iff] at hqn
        dsimp only [q] at hqn
        linarith [hqn.2.1, escapeScale_pos n]
      · have hx : Tendsto
            (fun n : ℕ => R.left i j y - 1 / (n + 1))
            atTop (𝓝 (R.left i j y)) := by
          simpa only [sub_zero] using
            tendsto_const_nhds.sub escapeScale_tendsto
        exact hx.prodMk_nhds tendsto_const_nhds
    · rintro _ ⟨y, hy, rfl⟩
      let q : ℕ → PlanePoint :=
        fun n => (R.right i j y + 1 / (n + 1 : ℝ), y)
      apply mem_frontier_of_escape (R.isClosed_componentCarrier i j)
        (R.mem_componentCarrier_iff i j _ |>.2
          ⟨hy, ⟨R.width_nonneg i j y hy, le_rfl⟩⟩) q
      · intro n hqn
        rw [R.mem_componentCarrier_iff] at hqn
        dsimp only [q] at hqn
        linarith [hqn.2.2, escapeScale_pos n]
      · have hx : Tendsto
            (fun n : ℕ => R.right i j y + 1 / (n + 1))
            atTop (𝓝 (R.right i j y)) := by
          simpa only [add_zero] using
            tendsto_const_nhds.add escapeScale_tendsto
        exact hx.prodMk_nhds tendsto_const_nhds
  · apply union_subset
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      change y = R.cuts i.castSucc at hy
      subst y
      let q : ℕ → PlanePoint :=
        fun n => (x, R.cuts i.castSucc - 1 / (n + 1 : ℝ))
      have hcuts : R.cuts i.castSucc < R.cuts i.succ :=
        R.cuts_strict Fin.castSucc_lt_succ
      apply mem_frontier_of_escape (R.isClosed_componentCarrier i j)
        (R.mem_componentCarrier_iff i j _ |>.2
          ⟨⟨le_rfl, hcuts.le⟩, hx⟩) q
      · intro n hqn
        rw [R.mem_componentCarrier_iff] at hqn
        dsimp only [q] at hqn
        linarith [hqn.1.1, escapeScale_pos n]
      · have hy' : Tendsto
            (fun n : ℕ => R.cuts i.castSucc - 1 / (n + 1))
            atTop (𝓝 (R.cuts i.castSucc)) := by
          simpa only [sub_zero] using
            tendsto_const_nhds.sub escapeScale_tendsto
        exact tendsto_const_nhds.prodMk_nhds hy'
    · rintro ⟨x, y⟩ ⟨hx, hy⟩
      change y = R.cuts i.succ at hy
      subst y
      let q : ℕ → PlanePoint :=
        fun n => (x, R.cuts i.succ + 1 / (n + 1 : ℝ))
      have hcuts : R.cuts i.castSucc < R.cuts i.succ :=
        R.cuts_strict Fin.castSucc_lt_succ
      apply mem_frontier_of_escape (R.isClosed_componentCarrier i j)
        (R.mem_componentCarrier_iff i j _ |>.2
          ⟨⟨hcuts.le, le_rfl⟩, hx⟩) q
      · intro n hqn
        rw [R.mem_componentCarrier_iff] at hqn
        dsimp only [q] at hqn
        linarith [hqn.1.2, escapeScale_pos n]
      · have hy' : Tendsto
            (fun n : ℕ => R.cuts i.succ + 1 / (n + 1))
            atTop (𝓝 (R.cuts i.succ)) := by
          simpa only [add_zero] using
            tendsto_const_nhds.add escapeScale_tendsto
        exact tendsto_const_nhds.prodMk_nhds hy'

/-- Complete topological-frontier decomposition of every generic closed graph
component, derived from ordering and continuity. -/
theorem frontier_componentCarrier (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) :
    frontier (R.componentCarrier i j) = R.componentFrontierTrace i j :=
  Set.Subset.antisymm
    (R.frontier_componentCarrier_subset_componentFrontierTrace i j)
    (R.componentFrontierTrace_subset_frontier_componentCarrier i j)

/-- The frontier of a whole finite component band is contained in the union of
the exact component-frontier decompositions. -/
theorem frontier_bandCarrier_subset_bandComponentFrontierTrace (R : Region)
    (i : Fin R.bandCount) :
    frontier (R.bandCarrier i) ⊆ R.bandComponentFrontierTrace i := by
  rw [show R.bandCarrier i =
      ⋃ j ∈ (Finset.univ : Finset (Fin (R.componentCount i))),
        R.componentCarrier i j by
    simp [bandCarrier]]
  intro p hp
  have hp' := frontier_biUnion_finset_subset
    (Finset.univ : Finset (Fin (R.componentCount i)))
    (fun j => R.componentCarrier i j) hp
  simp only [mem_iUnion] at hp'
  rcases hp' with ⟨j, _hjmem, hpj⟩
  rw [R.frontier_componentCarrier i j] at hpj
  rw [bandComponentFrontierTrace]
  exact mem_iUnion.mpr ⟨j, hpj⟩

/-- Every global frontier point lies on one of the derived component traces.
This is the raw upper decomposition before internal filled seams are removed. -/
theorem frontier_carrier_subset_rawComponentFrontierTrace (R : Region) :
    frontier R.carrier ⊆ R.rawComponentFrontierTrace := by
  rw [show R.carrier =
      ⋃ i ∈ (Finset.univ : Finset (Fin R.bandCount)), R.bandCarrier i by
    simp [carrier]]
  intro p hp
  have hp' := frontier_biUnion_finset_subset
    (Finset.univ : Finset (Fin R.bandCount)) R.bandCarrier hp
  simp only [mem_iUnion] at hp'
  rcases hp' with ⟨i, _himem, hpi⟩
  rw [rawComponentFrontierTrace]
  exact mem_iUnion.mpr
    ⟨i, R.frontier_bandCarrier_subset_bandComponentFrontierTrace i hpi⟩

/-- Each finite graph band is closed. -/
theorem isClosed_bandCarrier (R : Region) (i : Fin R.bandCount) :
    IsClosed (R.bandCarrier i) := by
  unfold bandCarrier
  exact isClosed_iUnion_of_finite fun j => R.isClosed_componentCarrier i j

/-- The original finite-band carrier is closed. -/
theorem isClosed_carrier (R : Region) : IsClosed R.carrier := by
  unfold carrier
  exact isClosed_iUnion_of_finite fun i => R.isClosed_bandCarrier i

end Region

end FiniteBandRearrangement
end CMVRelaxation
