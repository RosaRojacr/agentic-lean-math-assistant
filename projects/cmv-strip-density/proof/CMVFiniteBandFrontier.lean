import CMVFiniteBandRearrangement

open Set Function Filter MeasureTheory
open scoped Topology ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement
namespace Region

/-- The first occupied height band. -/
def firstBand (R : Region) : Fin R.bandCount := ⟨0, R.bandCount_pos⟩

/-- The last occupied height band. -/
def lastBand (R : Region) : Fin R.bandCount :=
  ⟨R.bandCount - 1, by have := R.bandCount_pos; omega⟩

/-- Strict interiors of the actual component intervals.  Unlike `interior fiber`,
this deliberately retains a pinched endpoint where two limiting components meet. -/
def fiberCore (R : Region) (i : Fin R.bandCount) (y : ℝ) : Set ℝ :=
  ⋃ j : Fin (R.componentCount i), Ioo (R.left i j y) (R.right i j y)

/-- Union of all closed endpoint graphs.  Their cut endpoints are retained even
when two limiting component intervals meet. -/
def graphTrace (R : Region) : Set PlanePoint :=
  ⋃ i : Fin R.bandCount, ⋃ j : Fin (R.componentCount i),
    R.leftGraphTrace i j ∪ R.rightGraphTrace i j

/-- Literal lower outer-end trace. -/
def lowerOuterTrace (R : Region) : Set PlanePoint :=
  {p | p.2 = R.cuts R.firstBand.castSucc ∧
    p.1 ∈ R.fiber R.firstBand (R.cuts R.firstBand.castSucc)}

/-- Literal upper outer-end trace. -/
def upperOuterTrace (R : Region) : Set PlanePoint :=
  {p | p.2 = R.cuts R.lastBand.succ ∧
    p.1 ∈ R.fiber R.lastBand (R.cuts R.lastBand.succ)}

/-- The seam part retained after filled two-sided interiors are removed.  The
finite endpoint correction is explicit because a pinched limiting component
endpoint can lie in the interior of both closed one-sided fiber unions while
remaining on the planar frontier. -/
def seamFrontierFiber (R : Region) (i : Fin (R.bandCount - 1)) : Set ℝ :=
  (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
      R.fiber (R.seamUpperBand i) (R.seamHeight i)) ∪
    (R.fiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
      R.fiberEndpoints (R.seamUpperBand i) (R.seamHeight i))

/-- Lift of the exact retained seam fiber. -/
def seamFrontierTrace (R : Region) (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧ p.1 ∈ R.seamFrontierFiber i}

/-- Complete derived frontier trace: all endpoint graphs, both outer ends, and
the actual one-sided seam symmetric differences with finite endpoint corrections. -/
def completeFrontierTrace (R : Region) : Set PlanePoint :=
  R.graphTrace ∪ R.lowerOuterTrace ∪ R.upperOuterTrace ∪
    ⋃ i : Fin (R.bandCount - 1), R.seamFrontierTrace i

/-- A point strictly inside one component on both sides of an internal cut is
stably filled in the plane. -/
def filledSeamCoreTrace (R : Region) (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧
    p.1 ∈ R.fiberCore (R.seamLowerBand i) (R.seamHeight i) ∧
    p.1 ∈ R.fiberCore (R.seamUpperBand i) (R.seamHeight i)}

@[simp] theorem firstBand_val (R : Region) : R.firstBand.val = 0 := rfl

@[simp] theorem lastBand_val (R : Region) : R.lastBand.val = R.bandCount - 1 := rfl

@[simp] theorem seamLowerBand_val (R : Region) (i : Fin (R.bandCount - 1)) :
    (R.seamLowerBand i).val = i.val := rfl

@[simp] theorem seamUpperBand_val (R : Region) (i : Fin (R.bandCount - 1)) :
    (R.seamUpperBand i).val = i.val + 1 := rfl

/-- The upper endpoint of the lower incident band is the lower endpoint of the
upper incident band. -/
theorem seamLower_succ_eq_seamUpper_castSucc (R : Region)
    (i : Fin (R.bandCount - 1)) :
    (R.seamLowerBand i).succ = (R.seamUpperBand i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem cuts_seamLower_succ (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.cuts (R.seamLowerBand i).succ = R.seamHeight i := by
  rw [seamHeight, R.seamLower_succ_eq_seamUpper_castSucc i]

@[simp] theorem cuts_seamUpper_castSucc (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.cuts (R.seamUpperBand i).castSucc = R.seamHeight i := rfl

/-- Closed band intervals have disjoint interiors. -/
theorem band_eq_of_height_mem_Ioo_mem_Icc (R : Region)
    (i k : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hk : y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)) : k = i := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hki | hik
  · have hidx : k.succ ≤ i.castSucc := by
      simpa only [Fin.succ_le_castSucc_iff] using hki
    have hcuts := R.cuts_strict.monotone hidx
    linarith [hk.2, hy.1]
  · have hidx : i.succ ≤ k.castSucc := by
      simpa only [Fin.succ_le_castSucc_iff] using hik
    have hcuts := R.cuts_strict.monotone hidx
    linarith [hy.2, hk.1]

/-- At an interior band height the global literal carrier has exactly that
band's actual fiber. -/
theorem horizontalSection_carrier_of_mem_Ioo (R : Region)
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    horizontalSection R.carrier y = R.fiber i y := by
  rw [R.horizontalSection_carrier]
  ext x
  constructor
  · intro hx
    rw [mem_iUnion] at hx
    rcases hx with ⟨k, hx⟩
    by_cases hk : y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)
    · simp only [hk, if_true] at hx
      simpa [R.band_eq_of_height_mem_Ioo_mem_Icc i k hy hk] using hx
    · simp [hk] at hx
  · intro hx
    rw [mem_iUnion]
    refine ⟨i, ?_⟩
    rw [if_pos (show y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) from
      ⟨hy.1.le, hy.2.le⟩)]
    exact hx


private theorem mem_frontier_union_of_mem_frontier_of_not_mem
    {s t : Set PlanePoint} {p : PlanePoint}
    (hs : IsClosed s) (ht : IsClosed t) (hp : p ∈ frontier s)
    (hpt : p ∉ t) : p ∈ frontier (s ∪ t) := by
  have hps : p ∈ s := hs.frontier_subset hp
  have hpUnion : p ∈ s ∪ t := Or.inl hps
  rw [mem_frontier_iff_notMem_interior hpUnion]
  intro hi
  have hUnion : interior (s ∪ t) ∈ 𝓝 p := isOpen_interior.mem_nhds hi
  have htCompl : tᶜ ∈ 𝓝 p := ht.isOpen_compl.mem_nhds hpt
  have hsNhd : s ∈ 𝓝 p := by
    apply mem_of_superset (inter_mem hUnion htCompl)
    rintro q ⟨hqUnion, hqNotT⟩
    rcases interior_subset hqUnion with hqs | hqt
    · exact hqs
    · exact False.elim (hqNotT hqt)
  have hpInterior : p ∈ interior s := mem_interior_iff_mem_nhds.mpr hsNhd
  exact (mem_frontier_iff_notMem_interior hps).mp hp hpInterior

private theorem mem_frontier_biUnion_finset_of_unique
    {ι : Type*} {J : Finset ι} {T : ι → Set PlanePoint} {a : ι}
    {p : PlanePoint} (ha : a ∈ J)
    (hclosed : ∀ k ∈ J, IsClosed (T k))
    (hp : p ∈ frontier (T a))
    (hother : ∀ k ∈ J, k ≠ a → p ∉ T k) :
    p ∈ frontier (⋃ k ∈ J, T k) := by
  classical
  let U : Set PlanePoint := ⋃ k ∈ J.erase a, T k
  have hUclosed : IsClosed U := by
    exact isClosed_biUnion_finset fun k hk =>
      hclosed k (Finset.mem_of_mem_erase hk)
  have hpU : p ∉ U := by
    intro hpU
    simp only [U, mem_iUnion] at hpU
    rcases hpU with ⟨k, hk, hpTk⟩
    exact hother k (Finset.mem_of_mem_erase hk)
      (Finset.ne_of_mem_erase hk) hpTk
  have hdecomp : (⋃ k ∈ J, T k) = T a ∪ U := by
    ext q
    simp only [U, mem_iUnion, mem_union]
    constructor
    · rintro ⟨k, hk, hq⟩
      by_cases hka : k = a
      · exact Or.inl (hka ▸ hq)
      · exact Or.inr ⟨k, Finset.mem_erase.mpr ⟨hka, hk⟩, hq⟩
    · rintro (hq | ⟨k, hk, hq⟩)
      · exact ⟨a, ha, hq⟩
      · exact ⟨k, Finset.mem_of_mem_erase hk, hq⟩
  rw [hdecomp]
  exact mem_frontier_union_of_mem_frontier_of_not_mem
    (hclosed a ha) hUclosed hp hpU

/-- At an interior height, a left endpoint of one component belongs to no
other component in the same band. -/
theorem left_endpoint_not_mem_other_component (R : Region)
    (i : Fin R.bandCount) {j k : Fin (R.componentCount i)} {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) (hkj : k ≠ j) :
    (R.left i j y, y) ∉ R.componentCarrier i k := by
  intro hp
  rw [R.mem_componentCarrier_iff] at hp
  rcases lt_or_gt_of_ne hkj with hkj | hjk
  · have hsep := R.components_strict i hkj y hy
    linarith [hp.2.2]
  · have hsep := R.components_strict i hjk y hy
    have hw := R.width_pos i j y hy
    linarith [hp.2.1]

/-- At an interior height, a right endpoint of one component belongs to no
other component in the same band. -/
theorem right_endpoint_not_mem_other_component (R : Region)
    (i : Fin R.bandCount) {j k : Fin (R.componentCount i)} {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) (hkj : k ≠ j) :
    (R.right i j y, y) ∉ R.componentCarrier i k := by
  intro hp
  rw [R.mem_componentCarrier_iff] at hp
  rcases lt_or_gt_of_ne hkj with hkj | hjk
  · have hsep := R.components_strict i hkj y hy
    have hw := R.width_pos i j y hy
    linarith [hp.2.2]
  · have hsep := R.components_strict i hjk y hy
    linarith [hp.2.1]

/-- A point whose height is interior to one band belongs to no other band. -/
theorem point_not_mem_other_band (R : Region)
    (i k : Fin R.bandCount) {p : PlanePoint}
    (hy : p.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) (hki : k ≠ i) :
    p ∉ R.bandCarrier k := by
  intro hp
  rw [bandCarrier, mem_iUnion] at hp
  rcases hp with ⟨j, hpj⟩
  rw [R.mem_componentCarrier_iff] at hpj
  exact hki (R.band_eq_of_height_mem_Ioo_mem_Icc i k hy hpj.1)

/-- Every open-band left endpoint graph is part of the global literal
frontier. -/
theorem open_leftGraphTrace_subset_frontier_carrier (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    (fun y => (R.left i j y, y)) ''
        Ioo (R.cuts i.castSucc) (R.cuts i.succ) ⊆ frontier R.carrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hpComponent :
      (R.left i j y, y) ∈ frontier (R.componentCarrier i j) := by
    rw [R.frontier_componentCarrier i j, componentFrontierTrace]
    exact Or.inl (Or.inl ⟨y, ⟨hy.1.le, hy.2.le⟩, rfl⟩)
  have hpBand : (R.left i j y, y) ∈ frontier (R.bandCarrier i) := by
    rw [show R.bandCarrier i =
        ⋃ k ∈ (Finset.univ : Finset (Fin (R.componentCount i))),
          R.componentCarrier i k by simp [bandCarrier]]
    apply mem_frontier_biUnion_finset_of_unique (Finset.mem_univ j)
    · intro k _hk
      exact R.isClosed_componentCarrier i k
    · exact hpComponent
    · intro k _hk hkj
      exact R.left_endpoint_not_mem_other_component i hy hkj
  rw [show R.carrier =
      ⋃ k ∈ (Finset.univ : Finset (Fin R.bandCount)), R.bandCarrier k by
    simp [carrier]]
  apply mem_frontier_biUnion_finset_of_unique (Finset.mem_univ i)
  · intro k _hk
    exact R.isClosed_bandCarrier k
  · exact hpBand
  · intro k _hk hki
    exact R.point_not_mem_other_band i k hy hki

/-- Every open-band right endpoint graph is part of the global literal
frontier. -/
theorem open_rightGraphTrace_subset_frontier_carrier (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    (fun y => (R.right i j y, y)) ''
        Ioo (R.cuts i.castSucc) (R.cuts i.succ) ⊆ frontier R.carrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hpComponent :
      (R.right i j y, y) ∈ frontier (R.componentCarrier i j) := by
    rw [R.frontier_componentCarrier i j, componentFrontierTrace]
    exact Or.inl (Or.inr ⟨y, ⟨hy.1.le, hy.2.le⟩, rfl⟩)
  have hpBand : (R.right i j y, y) ∈ frontier (R.bandCarrier i) := by
    rw [show R.bandCarrier i =
        ⋃ k ∈ (Finset.univ : Finset (Fin (R.componentCount i))),
          R.componentCarrier i k by simp [bandCarrier]]
    apply mem_frontier_biUnion_finset_of_unique (Finset.mem_univ j)
    · intro k _hk
      exact R.isClosed_componentCarrier i k
    · exact hpComponent
    · intro k _hk hkj
      exact R.right_endpoint_not_mem_other_component i hy hkj
  rw [show R.carrier =
      ⋃ k ∈ (Finset.univ : Finset (Fin R.bandCount)), R.bandCarrier k by
    simp [carrier]]
  apply mem_frontier_biUnion_finset_of_unique (Finset.mem_univ i)
  · intro k _hk
    exact R.isClosed_bandCarrier k
  · exact hpBand
  · intro k _hk hki
    exact R.point_not_mem_other_band i k hy hki

/-- Closed left endpoint graphs, including every cut endpoint, lie on the
global frontier.  Cut points are obtained as limits of actual open-band graph
frontier points rather than deleted as planar-null artifacts. -/
theorem leftGraphTrace_subset_frontier_carrier (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.leftGraphTrace i j ⊆ frontier R.carrier := by
  intro p hp
  rcases hp with ⟨y, hy, rfl⟩
  have hab : R.cuts i.castSucc < R.cuts i.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hcontinuous : Continuous (fun z => (R.left i j z, z)) :=
    (R.left_continuous i j).prodMk continuous_id
  have hyClosure : y ∈ closure (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    rw [closure_Ioo hab.ne]
    exact hy
  have hpClosure :
      (R.left i j y, y) ∈
        closure ((fun z => (R.left i j z, z)) ''
          Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    exact image_closure_subset_closure_image hcontinuous
      ⟨y, hyClosure, rfl⟩
  exact closure_minimal
    (R.open_leftGraphTrace_subset_frontier_carrier i j) isClosed_frontier hpClosure

/-- Closed right endpoint graphs likewise remain in the global frontier. -/
theorem rightGraphTrace_subset_frontier_carrier (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.rightGraphTrace i j ⊆ frontier R.carrier := by
  intro p hp
  rcases hp with ⟨y, hy, rfl⟩
  have hab : R.cuts i.castSucc < R.cuts i.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hcontinuous : Continuous (fun z => (R.right i j z, z)) :=
    (R.right_continuous i j).prodMk continuous_id
  have hyClosure : y ∈ closure (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    rw [closure_Ioo hab.ne]
    exact hy
  have hpClosure :
      (R.right i j y, y) ∈
        closure ((fun z => (R.right i j z, z)) ''
          Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    exact image_closure_subset_closure_image hcontinuous
      ⟨y, hyClosure, rfl⟩
  exact closure_minimal
    (R.open_rightGraphTrace_subset_frontier_carrier i j) isClosed_frontier hpClosure

/-- Every retained closed endpoint graph is an actual global frontier trace. -/
theorem graphTrace_subset_frontier_carrier (R : Region) :
    R.graphTrace ⊆ frontier R.carrier := by
  rintro p hp
  simp only [graphTrace, mem_iUnion] at hp
  rcases hp with ⟨i, j, hp | hp⟩
  · exact R.leftGraphTrace_subset_frontier_carrier i j hp
  · exact R.rightGraphTrace_subset_frontier_carrier i j hp

private theorem mem_frontier_of_escape_sequence
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

/-- The complete lower end fiber is actual frontier, including every
degenerate component endpoint. -/
theorem lowerOuterTrace_subset_frontier_carrier (R : Region) :
    R.lowerOuterTrace ⊆ frontier R.carrier := by
  rintro p ⟨hy, hx⟩
  rcases p with ⟨x, y⟩
  change y = R.cuts R.firstBand.castSucc at hy
  subst y
  rw [fiber, mem_iUnion] at hx
  rcases hx with ⟨j, hxj⟩
  have hcuts : R.cuts R.firstBand.castSucc < R.cuts R.firstBand.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hpComponent :
      (x, R.cuts R.firstBand.castSucc) ∈ R.componentCarrier R.firstBand j :=
    R.mem_componentCarrier_iff R.firstBand j _ |>.2
      ⟨⟨le_rfl, hcuts.le⟩, hxj⟩
  have hpCarrier :
      (x, R.cuts R.firstBand.castSucc) ∈ R.carrier := by
    rw [carrier, mem_iUnion]
    exact ⟨R.firstBand, mem_iUnion.mpr ⟨j, hpComponent⟩⟩
  let q : ℕ → PlanePoint :=
    fun n => (x, R.cuts R.firstBand.castSucc - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape_sequence R.isClosed_carrier hpCarrier q
  · intro n hqn
    rw [carrier, mem_iUnion] at hqn
    rcases hqn with ⟨i, hqi⟩
    rw [bandCarrier, mem_iUnion] at hqi
    rcases hqi with ⟨k, hqk⟩
    rw [R.mem_componentCarrier_iff] at hqk
    have hidx : R.firstBand.castSucc ≤ i.castSucc := by
      apply Fin.mk_le_mk.mpr
      simp [firstBand]
    have hcutle := R.cuts_strict.monotone hidx
    dsimp only [q] at hqk
    linarith [hqk.1.1, escapeScale_pos n]
  · have hyLim : Tendsto
        (fun n : ℕ => R.cuts R.firstBand.castSucc - 1 / (n + 1))
        atTop (𝓝 (R.cuts R.firstBand.castSucc)) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hyLim

/-- The complete upper end fiber is actual frontier. -/
theorem upperOuterTrace_subset_frontier_carrier (R : Region) :
    R.upperOuterTrace ⊆ frontier R.carrier := by
  rintro p ⟨hy, hx⟩
  rcases p with ⟨x, y⟩
  change y = R.cuts R.lastBand.succ at hy
  subst y
  rw [fiber, mem_iUnion] at hx
  rcases hx with ⟨j, hxj⟩
  have hcuts : R.cuts R.lastBand.castSucc < R.cuts R.lastBand.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hpComponent :
      (x, R.cuts R.lastBand.succ) ∈ R.componentCarrier R.lastBand j :=
    R.mem_componentCarrier_iff R.lastBand j _ |>.2
      ⟨⟨hcuts.le, le_rfl⟩, hxj⟩
  have hpCarrier :
      (x, R.cuts R.lastBand.succ) ∈ R.carrier := by
    rw [carrier, mem_iUnion]
    exact ⟨R.lastBand, mem_iUnion.mpr ⟨j, hpComponent⟩⟩
  let q : ℕ → PlanePoint :=
    fun n => (x, R.cuts R.lastBand.succ + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape_sequence R.isClosed_carrier hpCarrier q
  · intro n hqn
    rw [carrier, mem_iUnion] at hqn
    rcases hqn with ⟨i, hqi⟩
    rw [bandCarrier, mem_iUnion] at hqi
    rcases hqi with ⟨k, hqk⟩
    rw [R.mem_componentCarrier_iff] at hqk
    have hidx : i.succ ≤ R.lastBand.succ := by
      apply Fin.mk_le_mk.mpr
      -- The successor of every band index is at most the final cut index.
      have hi := i.isLt
      have hn := R.bandCount_pos
      omega
    have hcutle := R.cuts_strict.monotone hidx
    dsimp only [q] at hqk
    linarith [hqk.1.2, escapeScale_pos n]
  · have hyLim : Tendsto
        (fun n : ℕ => R.cuts R.lastBand.succ + 1 / (n + 1))
        atTop (𝓝 (R.cuts R.lastBand.succ)) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hyLim

/-- Fiber membership is literal band membership at every active closed-band
height. -/
theorem mem_bandCarrier_iff_mem_fiber (R : Region) (i : Fin R.bandCount)
    {x y : ℝ} (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    (x, y) ∈ R.bandCarrier i ↔ x ∈ R.fiber i y := by
  change x ∈ horizontalSection (R.bandCarrier i) y ↔ _
  rw [R.horizontalSection_bandCarrier]
  simp only [if_pos hy]

/-- A global carrier point at an interior height belongs to that unique band. -/
theorem mem_bandCarrier_of_mem_carrier_of_height_mem_Ioo (R : Region)
    (i : Fin R.bandCount) {p : PlanePoint}
    (hp : p ∈ R.carrier)
    (hy : p.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    p ∈ R.bandCarrier i := by
  change p.1 ∈ horizontalSection R.carrier p.2 at hp
  rw [R.horizontalSection_carrier_of_mem_Ioo i hy] at hp
  exact (R.mem_bandCarrier_iff_mem_fiber i ⟨hy.1.le, hy.2.le⟩).2 hp

/-- A planar interior point on an internal cut belongs to the lower incident
closed band. -/
theorem mem_seamLowerBand_of_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hp : (x, R.seamHeight i) ∈ interior R.carrier) :
    (x, R.seamHeight i) ∈ R.bandCarrier (R.seamLowerBand i) := by
  let low := R.cuts (R.seamLowerBand i).castSucc
  let c := R.seamHeight i
  have hlc : low < c := by
    dsimp only [low, c]
    rw [← R.cuts_seamLower_succ i]
    exact R.cuts_strict Fin.castSucc_lt_succ
  let q : ℕ → PlanePoint :=
    fun n => (x, c - (c - low) / (n + 2 : ℝ))
  have hqHeight : ∀ n,
      (q n).2 ∈ Ioo (R.cuts (R.seamLowerBand i).castSucc)
        (R.cuts (R.seamLowerBand i).succ) := by
    intro n
    dsimp only [q, low, c]
    rw [R.cuts_seamLower_succ i]
    have hn : (0 : ℝ) < n + 2 := by positivity
    constructor <;> field_simp <;> nlinarith
  have hqLim : Tendsto q atTop (𝓝 (x, R.seamHeight i)) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => (c - low) / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    have hyLim : Tendsto
        (fun n : ℕ => c - (c - low) / (n + 2 : ℝ)) atTop (𝓝 c) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hdiv
    simpa only [q, c] using tendsto_const_nhds.prodMk_nhds hyLim
  apply (R.isClosed_bandCarrier (R.seamLowerBand i)).mem_of_tendsto hqLim
  have hevInterior : ∀ᶠ n in atTop, q n ∈ interior R.carrier :=
    hqLim.eventually (isOpen_interior.mem_nhds hp)
  filter_upwards [hevInterior] with n hn
  exact R.mem_bandCarrier_of_mem_carrier_of_height_mem_Ioo
    (R.seamLowerBand i) (interior_subset hn) (hqHeight n)

/-- A planar interior point on an internal cut also belongs to the upper
incident closed band. -/
theorem mem_seamUpperBand_of_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hp : (x, R.seamHeight i) ∈ interior R.carrier) :
    (x, R.seamHeight i) ∈ R.bandCarrier (R.seamUpperBand i) := by
  let c := R.seamHeight i
  let high := R.cuts (R.seamUpperBand i).succ
  have hch : c < high := by
    dsimp only [c, high]
    exact R.cuts_strict Fin.castSucc_lt_succ
  let q : ℕ → PlanePoint :=
    fun n => (x, c + (high - c) / (n + 2 : ℝ))
  have hqHeight : ∀ n,
      (q n).2 ∈ Ioo (R.cuts (R.seamUpperBand i).castSucc)
        (R.cuts (R.seamUpperBand i).succ) := by
    intro n
    dsimp only [q, c, high]
    rw [R.cuts_seamUpper_castSucc i]
    have hn : (0 : ℝ) < n + 2 := by positivity
    constructor <;> field_simp <;> nlinarith
  have hqLim : Tendsto q atTop (𝓝 (x, R.seamHeight i)) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => (high - c) / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    have hyLim : Tendsto
        (fun n : ℕ => c + (high - c) / (n + 2 : ℝ)) atTop (𝓝 c) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdiv
    simpa only [q, c] using tendsto_const_nhds.prodMk_nhds hyLim
  apply (R.isClosed_bandCarrier (R.seamUpperBand i)).mem_of_tendsto hqLim
  have hevInterior : ∀ᶠ n in atTop, q n ∈ interior R.carrier :=
    hqLim.eventually (isOpen_interior.mem_nhds hp)
  filter_upwards [hevInterior] with n hn
  exact R.mem_bandCarrier_of_mem_carrier_of_height_mem_Ioo
    (R.seamUpperBand i) (interior_subset hn) (hqHeight n)

/-- The actual one-sided fiber symmetric difference at every internal cut is
literal planar frontier. -/
theorem seamSymmDiff_subset_frontier_carrier (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamSymmDiff i ⊆ frontier R.carrier := by
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  change y = R.seamHeight i at hy
  subst y
  rw [R.isClosed_carrier.frontier_eq]
  rcases hx with hx | hx
  · have hLowerHeight :
        R.seamHeight i ∈
          Icc (R.cuts (R.seamLowerBand i).castSucc)
            (R.cuts (R.seamLowerBand i).succ) := by
      rw [R.cuts_seamLower_succ i]
      exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
    have hpLower : (x, R.seamHeight i) ∈
        R.bandCarrier (R.seamLowerBand i) :=
      (R.mem_bandCarrier_iff_mem_fiber (R.seamLowerBand i) hLowerHeight).2 hx.1
    refine ⟨?_, ?_⟩
    · rw [carrier, mem_iUnion]
      exact ⟨R.seamLowerBand i, hpLower⟩
    · intro hpInterior
      have hpUpper := R.mem_seamUpperBand_of_mem_interior i hpInterior
      have hUpperHeight :
          R.seamHeight i ∈
            Icc (R.cuts (R.seamUpperBand i).castSucc)
              (R.cuts (R.seamUpperBand i).succ) := by
        exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩
      exact hx.2 ((R.mem_bandCarrier_iff_mem_fiber
        (R.seamUpperBand i) hUpperHeight).1 hpUpper)
  · have hUpperHeight :
        R.seamHeight i ∈
          Icc (R.cuts (R.seamUpperBand i).castSucc)
            (R.cuts (R.seamUpperBand i).succ) := by
      exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩
    have hpUpper : (x, R.seamHeight i) ∈
        R.bandCarrier (R.seamUpperBand i) :=
      (R.mem_bandCarrier_iff_mem_fiber (R.seamUpperBand i) hUpperHeight).2 hx.1
    refine ⟨?_, ?_⟩
    · rw [carrier, mem_iUnion]
      exact ⟨R.seamUpperBand i, hpUpper⟩
    · intro hpInterior
      have hpLower := R.mem_seamLowerBand_of_mem_interior i hpInterior
      have hLowerHeight :
          R.seamHeight i ∈
            Icc (R.cuts (R.seamLowerBand i).castSucc)
              (R.cuts (R.seamLowerBand i).succ) := by
        rw [R.cuts_seamLower_succ i]
        exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
      exact hx.2 ((R.mem_bandCarrier_iff_mem_fiber
        (R.seamLowerBand i) hLowerHeight).1 hpLower)

/-- Every finite endpoint correction at a seam is already carried by a closed
endpoint graph, hence is genuine planar frontier. -/
theorem seamEndpointSet_subset_graphTrace (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamEndpointSet i ⊆ R.graphTrace := by
  rintro p ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [graphTrace]
      refine mem_iUnion.mpr ⟨R.seamLowerBand i, mem_iUnion.mpr ⟨j, Or.inl ?_⟩⟩
      exact ⟨R.seamHeight i, by
        rw [R.cuts_seamLower_succ i]
        exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩, rfl⟩
    · rw [graphTrace]
      refine mem_iUnion.mpr ⟨R.seamLowerBand i, mem_iUnion.mpr ⟨j, Or.inr ?_⟩⟩
      exact ⟨R.seamHeight i, by
        rw [R.cuts_seamLower_succ i]
        exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩, rfl⟩
  · rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [graphTrace]
      refine mem_iUnion.mpr ⟨R.seamUpperBand i, mem_iUnion.mpr ⟨j, Or.inl ?_⟩⟩
      exact ⟨R.seamHeight i,
        ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩, rfl⟩
    · rw [graphTrace]
      refine mem_iUnion.mpr ⟨R.seamUpperBand i, mem_iUnion.mpr ⟨j, Or.inr ?_⟩⟩
      exact ⟨R.seamHeight i,
        ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩, rfl⟩

/-- The corrected seam trace is actual frontier.  This includes pinched
component endpoints omitted by `interior fiber`. -/
theorem seamFrontierTrace_subset_frontier_carrier (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamFrontierTrace i ⊆ frontier R.carrier := by
  rintro p ⟨hy, hx⟩
  rcases hx with hx | hx
  · apply R.seamSymmDiff_subset_frontier_carrier i
    exact ⟨hy, hx⟩
  · apply R.graphTrace_subset_frontier_carrier
    apply R.seamEndpointSet_subset_graphTrace i
    refine ⟨p.1, hx, ?_⟩
    exact Prod.ext rfl hy.symm

/-- Every strict component core is contained in its closed fiber. -/
theorem fiberCore_subset_fiber (R : Region) (i : Fin R.bandCount) (y : ℝ) :
    R.fiberCore i y ⊆ R.fiber i y := by
  rintro x hx
  rw [fiberCore, mem_iUnion] at hx
  rcases hx with ⟨j, hxj⟩
  rw [fiber, mem_iUnion]
  exact ⟨j, ⟨hxj.1.le, hxj.2.le⟩⟩

/-- Away from the finite endpoint set, membership in a closed one-sided fiber
is strict membership in one component. -/
theorem mem_fiberCore_of_mem_fiber_of_not_mem_endpoints (R : Region)
    (i : Fin R.bandCount) (y x : ℝ)
    (hx : x ∈ R.fiber i y) (hxe : x ∉ R.fiberEndpoints i y) :
    x ∈ R.fiberCore i y := by
  rw [fiber, mem_iUnion] at hx
  rcases hx with ⟨j, hxj⟩
  rw [fiberCore, mem_iUnion]
  refine ⟨j, ?_⟩
  constructor
  · exact lt_of_le_of_ne hxj.1 fun h =>
      hxe (Or.inl ⟨j, h⟩)
  · exact lt_of_le_of_ne hxj.2 fun h =>
      hxe (Or.inr ⟨j, h.symm⟩)

/-- A point lying strictly inside one actual component on both sides of a cut
has a genuine open planar neighborhood in the literal carrier. -/
theorem filledSeamCoreTrace_subset_interior_carrier (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.filledSeamCoreTrace i ⊆ interior R.carrier := by
  rintro p ⟨hy, hxLower, hxUpper⟩
  rcases p with ⟨x, y⟩
  change y = R.seamHeight i at hy
  subst y
  rw [fiberCore, mem_iUnion] at hxLower hxUpper
  rcases hxLower with ⟨jLower, hxLower⟩
  rcases hxUpper with ⟨jUpper, hxUpper⟩
  let low := R.cuts (R.seamLowerBand i).castSucc
  let high := R.cuts (R.seamUpperBand i).succ
  let U : Set PlanePoint :=
    {q | q.2 ∈ Ioo low high ∧
      R.left (R.seamLowerBand i) jLower q.2 < q.1 ∧
      q.1 < R.right (R.seamLowerBand i) jLower q.2 ∧
      R.left (R.seamUpperBand i) jUpper q.2 < q.1 ∧
      q.1 < R.right (R.seamUpperBand i) jUpper q.2}
  have hUopen : IsOpen U := by
    have h₁ : IsOpen {q : PlanePoint | q.2 ∈ Ioo low high} :=
      isOpen_Ioo.preimage continuous_snd
    have h₂ : IsOpen {q : PlanePoint |
        R.left (R.seamLowerBand i) jLower q.2 < q.1} :=
      isOpen_lt
        ((R.left_continuous (R.seamLowerBand i) jLower).comp continuous_snd)
        continuous_fst
    have h₃ : IsOpen {q : PlanePoint |
        q.1 < R.right (R.seamLowerBand i) jLower q.2} :=
      isOpen_lt continuous_fst
        ((R.right_continuous (R.seamLowerBand i) jLower).comp continuous_snd)
    have h₄ : IsOpen {q : PlanePoint |
        R.left (R.seamUpperBand i) jUpper q.2 < q.1} :=
      isOpen_lt
        ((R.left_continuous (R.seamUpperBand i) jUpper).comp continuous_snd)
        continuous_fst
    have h₅ : IsOpen {q : PlanePoint |
        q.1 < R.right (R.seamUpperBand i) jUpper q.2} :=
      isOpen_lt continuous_fst
        ((R.right_continuous (R.seamUpperBand i) jUpper).comp continuous_snd)
    rw [show U =
        ((({q : PlanePoint | q.2 ∈ Ioo low high} ∩
          {q | R.left (R.seamLowerBand i) jLower q.2 < q.1}) ∩
          {q | q.1 < R.right (R.seamLowerBand i) jLower q.2}) ∩
          {q | R.left (R.seamUpperBand i) jUpper q.2 < q.1}) ∩
          {q | q.1 < R.right (R.seamUpperBand i) jUpper q.2} by
      ext q
      simp only [U, mem_ofPred_eq, mem_inter_iff]
      tauto]
    exact (((h₁.inter h₂).inter h₃).inter h₄).inter h₅
  have hlc : low < R.seamHeight i := by
    dsimp only [low]
    rw [← R.cuts_seamLower_succ i]
    exact R.cuts_strict Fin.castSucc_lt_succ
  have hch : R.seamHeight i < high := by
    dsimp only [high]
    exact R.cuts_strict Fin.castSucc_lt_succ
  have hpU : (x, R.seamHeight i) ∈ U :=
    ⟨⟨hlc, hch⟩, hxLower.1, hxLower.2, hxUpper.1, hxUpper.2⟩
  have hUsub : U ⊆ R.carrier := by
    rintro q ⟨hqHeight, hqLowerLeft, hqLowerRight, hqUpperLeft, hqUpperRight⟩
    by_cases hqc : q.2 ≤ R.seamHeight i
    · have hqComponent :
          q ∈ R.componentCarrier (R.seamLowerBand i) jLower := by
        rw [R.mem_componentCarrier_iff]
        refine ⟨?_, ⟨hqLowerLeft.le, hqLowerRight.le⟩⟩
        rw [R.cuts_seamLower_succ i]
        exact ⟨hqHeight.1.le, hqc⟩
      rw [carrier, mem_iUnion]
      exact ⟨R.seamLowerBand i, mem_iUnion.mpr ⟨jLower, hqComponent⟩⟩
    · have hqComponent :
          q ∈ R.componentCarrier (R.seamUpperBand i) jUpper := by
        rw [R.mem_componentCarrier_iff]
        exact ⟨⟨le_of_lt (lt_of_not_ge hqc), hqHeight.2.le⟩,
          ⟨hqUpperLeft.le, hqUpperRight.le⟩⟩
      rw [carrier, mem_iUnion]
      exact ⟨R.seamUpperBand i, mem_iUnion.mpr ⟨jUpper, hqComponent⟩⟩
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hUopen.mem_nhds hpU) hUsub)

/-- Every point in the union of the two closed one-sided fibers is either on
the corrected seam frontier or is genuinely filled in the plane. -/
theorem mem_seamFrontierTrace_or_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hx : x ∈ R.fiber (R.seamLowerBand i) (R.seamHeight i) ∪
      R.fiber (R.seamUpperBand i) (R.seamHeight i)) :
    (x, R.seamHeight i) ∈ R.seamFrontierTrace i ∨
      (x, R.seamHeight i) ∈ interior R.carrier := by
  let A := R.fiber (R.seamLowerBand i) (R.seamHeight i)
  let B := R.fiber (R.seamUpperBand i) (R.seamHeight i)
  let EA := R.fiberEndpoints (R.seamLowerBand i) (R.seamHeight i)
  let EB := R.fiberEndpoints (R.seamUpperBand i) (R.seamHeight i)
  change x ∈ A ∪ B at hx
  by_cases hEA : x ∈ EA
  · left
    exact ⟨rfl, Or.inr (Or.inl hEA)⟩
  by_cases hEB : x ∈ EB
  · left
    exact ⟨rfl, Or.inr (Or.inr hEB)⟩
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · right
      apply R.filledSeamCoreTrace_subset_interior_carrier i
      exact ⟨rfl,
        R.mem_fiberCore_of_mem_fiber_of_not_mem_endpoints
          (R.seamLowerBand i) (R.seamHeight i) x hA hEA,
        R.mem_fiberCore_of_mem_fiber_of_not_mem_endpoints
          (R.seamUpperBand i) (R.seamHeight i) x hB hEB⟩
    · left
      exact ⟨rfl, Or.inl (Or.inl ⟨hA, hB⟩)⟩
  · have hB : x ∈ B := hx.resolve_left hA
    left
    exact ⟨rfl, Or.inl (Or.inr ⟨hB, hA⟩)⟩

/-- All displayed pieces of the complete derived trace are actual frontier. -/
theorem completeFrontierTrace_subset_frontier_carrier (R : Region) :
    R.completeFrontierTrace ⊆ frontier R.carrier := by
  rintro p hp
  rcases hp with ((hp | hp) | hp) | hp
  · exact R.graphTrace_subset_frontier_carrier hp
  · exact R.lowerOuterTrace_subset_frontier_carrier hp
  · exact R.upperOuterTrace_subset_frontier_carrier hp
  · rw [mem_iUnion] at hp
    rcases hp with ⟨i, hp⟩
    exact R.seamFrontierTrace_subset_frontier_carrier i hp

/-- Every band is either first or the upper incident band of a unique
preceding seam. -/
theorem eq_firstBand_or_exists_seamUpperBand (R : Region)
    (i : Fin R.bandCount) :
    i = R.firstBand ∨
      ∃ s : Fin (R.bandCount - 1), R.seamUpperBand s = i := by
  by_cases hi : i.val = 0
  · left
    apply Fin.ext
    simpa [firstBand] using hi
  · right
    let s : Fin (R.bandCount - 1) :=
      ⟨i.val - 1, by
        have hil := i.isLt
        have hn := R.bandCount_pos
        omega⟩
    refine ⟨s, ?_⟩
    apply Fin.ext
    dsimp only [s, seamUpperBand]
    omega

/-- Every band is either last or the lower incident band of a unique following
seam. -/
theorem eq_lastBand_or_exists_seamLowerBand (R : Region)
    (i : Fin R.bandCount) :
    i = R.lastBand ∨
      ∃ s : Fin (R.bandCount - 1), R.seamLowerBand s = i := by
  by_cases hi : i.val = R.bandCount - 1
  · left
    apply Fin.ext
    simpa [lastBand] using hi
  · right
    have hil : i.val < R.bandCount - 1 := by
      have hi' := i.isLt
      have hn := R.bandCount_pos
      omega
    let s : Fin (R.bandCount - 1) := ⟨i.val, hil⟩
    refine ⟨s, ?_⟩
    apply Fin.ext
    rfl

private theorem graphTrace_subset_completeFrontierTrace (R : Region) :
    R.graphTrace ⊆ R.completeFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inl (Or.inl hp))

private theorem lowerOuterTrace_subset_completeFrontierTrace (R : Region) :
    R.lowerOuterTrace ⊆ R.completeFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inl (Or.inr hp))

private theorem upperOuterTrace_subset_completeFrontierTrace (R : Region) :
    R.upperOuterTrace ⊆ R.completeFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inr hp)

private theorem seamFrontierTrace_subset_completeFrontierTrace (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamFrontierTrace i ⊆ R.completeFrontierTrace := by
  intro p hp
  exact Or.inr (mem_iUnion.mpr ⟨i, hp⟩)

/-- A lower component-end trace is either the global lower outer end, a
corrected internal seam point, or a genuinely filled planar interior point. -/
theorem lowerEndTrace_subset_completeFrontierTrace_union_interior (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.lowerEndTrace i j ⊆ R.completeFrontierTrace ∪ interior R.carrier := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change y = R.cuts i.castSucc at hy
  subst y
  rcases R.eq_firstBand_or_exists_seamUpperBand i with hi | ⟨s, hsi⟩
  · subst i
    left
    apply R.lowerOuterTrace_subset_completeFrontierTrace
    refine ⟨rfl, ?_⟩
    rw [fiber, mem_iUnion]
    exact ⟨j, hx⟩
  · subst i
    have hxUnion :
        x ∈ R.fiber (R.seamLowerBand s) (R.seamHeight s) ∪
          R.fiber (R.seamUpperBand s) (R.seamHeight s) := by
      right
      rw [fiber, mem_iUnion]
      exact ⟨j, hx⟩
    rcases R.mem_seamFrontierTrace_or_mem_interior s hxUnion with hp | hp
    · left
      exact R.seamFrontierTrace_subset_completeFrontierTrace s hp
    · exact Or.inr hp

/-- An upper component-end trace has the analogous exhaustive classification. -/
theorem upperEndTrace_subset_completeFrontierTrace_union_interior (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.upperEndTrace i j ⊆ R.completeFrontierTrace ∪ interior R.carrier := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  change y = R.cuts i.succ at hy
  subst y
  rcases R.eq_lastBand_or_exists_seamLowerBand i with hi | ⟨s, hsi⟩
  · subst i
    left
    apply R.upperOuterTrace_subset_completeFrontierTrace
    refine ⟨rfl, ?_⟩
    rw [fiber, mem_iUnion]
    exact ⟨j, hx⟩
  · subst i
    have hxUnion :
        x ∈ R.fiber (R.seamLowerBand s) (R.seamHeight s) ∪
          R.fiber (R.seamUpperBand s) (R.seamHeight s) := by
      left
      rw [fiber, mem_iUnion]
      exact ⟨j, hx⟩
    rcases R.mem_seamFrontierTrace_or_mem_interior s hxUnion with hp | hp
    · left
      exact R.seamFrontierTrace_subset_completeFrontierTrace s hp
    · exact Or.inr hp

/-- Every global frontier point lies on the corrected complete trace.  Filled
one-sided overlaps are removed using actual planar interior neighborhoods; no
frontier equation is supplied as input. -/
theorem frontier_carrier_subset_completeFrontierTrace (R : Region) :
    frontier R.carrier ⊆ R.completeFrontierTrace := by
  intro p hp
  have hpCarrier : p ∈ R.carrier := R.isClosed_carrier.frontier_subset hp
  have hpNotInterior : p ∉ interior R.carrier :=
    (mem_frontier_iff_notMem_interior hpCarrier).mp hp
  have hraw := R.frontier_carrier_subset_rawComponentFrontierTrace hp
  rw [rawComponentFrontierTrace, mem_iUnion] at hraw
  rcases hraw with ⟨i, hraw⟩
  rw [bandComponentFrontierTrace, mem_iUnion] at hraw
  rcases hraw with ⟨j, hraw⟩
  rcases hraw with (hleft | hright) | hlower | hupper
  · apply R.graphTrace_subset_completeFrontierTrace
    rw [graphTrace]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, Or.inl hleft⟩⟩
  · apply R.graphTrace_subset_completeFrontierTrace
    rw [graphTrace]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, Or.inr hright⟩⟩
  · rcases R.lowerEndTrace_subset_completeFrontierTrace_union_interior
      i j hlower with hcomplete | hinterior
    · exact hcomplete
    · exact False.elim (hpNotInterior hinterior)
  · rcases R.upperEndTrace_subset_completeFrontierTrace_union_interior
      i j hupper with hcomplete | hinterior
    · exact hcomplete
    · exact False.elim (hpNotInterior hinterior)

/-- Exact complete topological-frontier decomposition for every branch-neutral
finite-band region, including outer ends, width jumps, collapsed components,
and pinched component mergers at internal cuts. -/
theorem frontier_carrier (R : Region) :
    frontier R.carrier = R.completeFrontierTrace :=
  Set.Subset.antisymm R.frontier_carrier_subset_completeFrontierTrace
    R.completeFrontierTrace_subset_frontier_carrier

/-- Total width is strictly positive throughout every open band. -/
theorem totalWidth_pos (R : Region) (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    0 < R.totalWidth i y := by
  have : Nonempty (Fin (R.componentCount i)) :=
    ⟨⟨0, R.componentCount_pos i⟩⟩
  unfold totalWidth
  apply Finset.sum_pos
  · intro j _hj
    exact sub_pos.mpr (R.width_pos i j y hy)
  · exact Finset.univ_nonempty

/-- Closed left graph of the centered interval in one band. -/
def centeredLeftGraphTrace (R : Region) (i : Fin R.bandCount) : Set PlanePoint :=
  (fun y => (-R.totalWidth i y / 2, y)) ''
    Icc (R.cuts i.castSucc) (R.cuts i.succ)

/-- Closed right graph of the centered interval in one band. -/
def centeredRightGraphTrace (R : Region) (i : Fin R.bandCount) : Set PlanePoint :=
  (fun y => (R.totalWidth i y / 2, y)) ''
    Icc (R.cuts i.castSucc) (R.cuts i.succ)

/-- All centered closed endpoint graphs. -/
def centeredGraphTrace (R : Region) : Set PlanePoint :=
  ⋃ i : Fin R.bandCount, R.centeredLeftGraphTrace i ∪ R.centeredRightGraphTrace i

/-- Lower outer trace of the centered carrier. -/
def centeredLowerOuterTrace (R : Region) : Set PlanePoint :=
  {p | p.2 = R.cuts R.firstBand.castSucc ∧
    p.1 ∈ R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc)}

/-- Upper outer trace of the centered carrier. -/
def centeredUpperOuterTrace (R : Region) : Set PlanePoint :=
  {p | p.2 = R.cuts R.lastBand.succ ∧
    p.1 ∈ R.centeredFiber R.lastBand (R.cuts R.lastBand.succ)}

/-- The two endpoints of one centered fiber. -/
def centeredFiberEndpoints (R : Region) (i : Fin R.bandCount) (y : ℝ) : Set ℝ :=
  {-R.totalWidth i y / 2, R.totalWidth i y / 2}

/-- Finite endpoint correction for a centered internal seam. -/
def centeredSeamEndpointSet (R : Region)
    (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  (fun x => (x, R.seamHeight i)) ''
    (R.centeredFiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
      R.centeredFiberEndpoints (R.seamUpperBand i) (R.seamHeight i))

/-- Exact corrected seam of the centered carrier. -/
def centeredSeamFrontierTrace (R : Region)
    (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧
    p.1 ∈
      (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) ∪
      (R.centeredFiberEndpoints (R.seamLowerBand i) (R.seamHeight i) ∪
        R.centeredFiberEndpoints (R.seamUpperBand i) (R.seamHeight i))}

/-- Complete derived trace for the literal centered finite-band carrier. -/
def completeCenteredFrontierTrace (R : Region) : Set PlanePoint :=
  R.centeredGraphTrace ∪ R.centeredLowerOuterTrace ∪ R.centeredUpperOuterTrace ∪
    ⋃ i : Fin (R.bandCount - 1), R.centeredSeamFrontierTrace i

/-- Every open-band point of the centered left graph is global frontier. -/
theorem open_centeredLeftGraphTrace_subset_frontier_centeredCarrier (R : Region)
    (i : Fin R.bandCount) :
    (fun y => (-R.totalWidth i y / 2, y)) ''
        Ioo (R.cuts i.castSucc) (R.cuts i.succ) ⊆
      frontier R.centeredCarrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hw : 0 < R.totalWidth i y := R.totalWidth_pos i hy
  have hpBand :
      (-R.totalWidth i y / 2, y) ∈ R.centeredBandCarrier i :=
    R.mem_centeredBandCarrier_iff i _ |>.2
      ⟨⟨hy.1.le, hy.2.le⟩, by
        simp only [centeredFiber, mem_Icc]
        constructor <;> linarith⟩
  have hpCarrier :
      (-R.totalWidth i y / 2, y) ∈ R.centeredCarrier := by
    rw [centeredCarrier, mem_iUnion]
    exact ⟨i, hpBand⟩
  let q : ℕ → PlanePoint :=
    fun n => (-R.totalWidth i y / 2 - 1 / (n + 1 : ℝ), y)
  apply mem_frontier_of_escape_sequence R.isClosed_centeredCarrier hpCarrier q
  · intro n hqn
    rw [centeredCarrier, mem_iUnion] at hqn
    rcases hqn with ⟨k, hqk⟩
    rw [R.mem_centeredBandCarrier_iff] at hqk
    have hki := R.band_eq_of_height_mem_Ioo_mem_Icc i k hy hqk.1
    subst k
    dsimp only [q] at hqk
    simp only [centeredFiber, mem_Icc] at hqk
    linarith [hqk.2.1, escapeScale_pos n]
  · have hxLim : Tendsto
        (fun n : ℕ => -R.totalWidth i y / 2 - 1 / (n + 1))
        atTop (𝓝 (-R.totalWidth i y / 2)) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub escapeScale_tendsto
    exact hxLim.prodMk_nhds tendsto_const_nhds

/-- Every open-band point of the centered right graph is global frontier. -/
theorem open_centeredRightGraphTrace_subset_frontier_centeredCarrier (R : Region)
    (i : Fin R.bandCount) :
    (fun y => (R.totalWidth i y / 2, y)) ''
        Ioo (R.cuts i.castSucc) (R.cuts i.succ) ⊆
      frontier R.centeredCarrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hw : 0 < R.totalWidth i y := R.totalWidth_pos i hy
  have hpBand :
      (R.totalWidth i y / 2, y) ∈ R.centeredBandCarrier i :=
    R.mem_centeredBandCarrier_iff i _ |>.2
      ⟨⟨hy.1.le, hy.2.le⟩, by
        simp only [centeredFiber, mem_Icc]
        constructor <;> linarith⟩
  have hpCarrier :
      (R.totalWidth i y / 2, y) ∈ R.centeredCarrier := by
    rw [centeredCarrier, mem_iUnion]
    exact ⟨i, hpBand⟩
  let q : ℕ → PlanePoint :=
    fun n => (R.totalWidth i y / 2 + 1 / (n + 1 : ℝ), y)
  apply mem_frontier_of_escape_sequence R.isClosed_centeredCarrier hpCarrier q
  · intro n hqn
    rw [centeredCarrier, mem_iUnion] at hqn
    rcases hqn with ⟨k, hqk⟩
    rw [R.mem_centeredBandCarrier_iff] at hqk
    have hki := R.band_eq_of_height_mem_Ioo_mem_Icc i k hy hqk.1
    subst k
    dsimp only [q] at hqk
    simp only [centeredFiber, mem_Icc] at hqk
    linarith [hqk.2.2, escapeScale_pos n]
  · have hxLim : Tendsto
        (fun n : ℕ => R.totalWidth i y / 2 + 1 / (n + 1))
        atTop (𝓝 (R.totalWidth i y / 2)) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add escapeScale_tendsto
    exact hxLim.prodMk_nhds tendsto_const_nhds

/-- Closed centered left graphs, including cut endpoints, are frontier. -/
theorem centeredLeftGraphTrace_subset_frontier_centeredCarrier (R : Region)
    (i : Fin R.bandCount) :
    R.centeredLeftGraphTrace i ⊆ frontier R.centeredCarrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hab : R.cuts i.castSucc < R.cuts i.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hcontinuous : Continuous (fun z => (-R.totalWidth i z / 2, z)) :=
    (R.continuous_totalWidth i).neg.div_const 2 |>.prodMk continuous_id
  have hyClosure : y ∈ closure (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    rw [closure_Ioo hab.ne]
    exact hy
  have hpClosure :
      (-R.totalWidth i y / 2, y) ∈
        closure ((fun z => (-R.totalWidth i z / 2, z)) ''
          Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :=
    image_closure_subset_closure_image hcontinuous ⟨y, hyClosure, rfl⟩
  exact closure_minimal
    (R.open_centeredLeftGraphTrace_subset_frontier_centeredCarrier i)
    isClosed_frontier hpClosure

/-- Closed centered right graphs are frontier. -/
theorem centeredRightGraphTrace_subset_frontier_centeredCarrier (R : Region)
    (i : Fin R.bandCount) :
    R.centeredRightGraphTrace i ⊆ frontier R.centeredCarrier := by
  rintro _ ⟨y, hy, rfl⟩
  have hab : R.cuts i.castSucc < R.cuts i.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hcontinuous : Continuous (fun z => (R.totalWidth i z / 2, z)) :=
    (R.continuous_totalWidth i).div_const 2 |>.prodMk continuous_id
  have hyClosure : y ∈ closure (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
    rw [closure_Ioo hab.ne]
    exact hy
  have hpClosure :
      (R.totalWidth i y / 2, y) ∈
        closure ((fun z => (R.totalWidth i z / 2, z)) ''
          Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :=
    image_closure_subset_closure_image hcontinuous ⟨y, hyClosure, rfl⟩
  exact closure_minimal
    (R.open_centeredRightGraphTrace_subset_frontier_centeredCarrier i)
    isClosed_frontier hpClosure

/-- All centered closed graph traces are actual frontier. -/
theorem centeredGraphTrace_subset_frontier_centeredCarrier (R : Region) :
    R.centeredGraphTrace ⊆ frontier R.centeredCarrier := by
  rintro p hp
  rw [centeredGraphTrace, mem_iUnion] at hp
  rcases hp with ⟨i, hp | hp⟩
  · exact R.centeredLeftGraphTrace_subset_frontier_centeredCarrier i hp
  · exact R.centeredRightGraphTrace_subset_frontier_centeredCarrier i hp

/-- The centered lower outer fiber is actual frontier. -/
theorem centeredLowerOuterTrace_subset_frontier_centeredCarrier (R : Region) :
    R.centeredLowerOuterTrace ⊆ frontier R.centeredCarrier := by
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  change y = R.cuts R.firstBand.castSucc at hy
  subst y
  have hcuts : R.cuts R.firstBand.castSucc < R.cuts R.firstBand.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hpBand :
      (x, R.cuts R.firstBand.castSucc) ∈ R.centeredBandCarrier R.firstBand :=
    R.mem_centeredBandCarrier_iff R.firstBand _ |>.2
      ⟨⟨le_rfl, hcuts.le⟩, hx⟩
  have hpCarrier :
      (x, R.cuts R.firstBand.castSucc) ∈ R.centeredCarrier := by
    rw [centeredCarrier, mem_iUnion]
    exact ⟨R.firstBand, hpBand⟩
  let q : ℕ → PlanePoint :=
    fun n => (x, R.cuts R.firstBand.castSucc - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape_sequence R.isClosed_centeredCarrier hpCarrier q
  · intro n hqn
    rw [centeredCarrier, mem_iUnion] at hqn
    rcases hqn with ⟨i, hqi⟩
    rw [R.mem_centeredBandCarrier_iff] at hqi
    have hidx : R.firstBand.castSucc ≤ i.castSucc := by
      apply Fin.mk_le_mk.mpr
      simp [firstBand]
    have hcutle := R.cuts_strict.monotone hidx
    dsimp only [q] at hqi
    linarith [hqi.1.1, escapeScale_pos n]
  · have hyLim : Tendsto
        (fun n : ℕ => R.cuts R.firstBand.castSucc - 1 / (n + 1))
        atTop (𝓝 (R.cuts R.firstBand.castSucc)) := by
      simpa only [sub_zero] using
        tendsto_const_nhds.sub escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hyLim

/-- The centered upper outer fiber is actual frontier. -/
theorem centeredUpperOuterTrace_subset_frontier_centeredCarrier (R : Region) :
    R.centeredUpperOuterTrace ⊆ frontier R.centeredCarrier := by
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  change y = R.cuts R.lastBand.succ at hy
  subst y
  have hcuts : R.cuts R.lastBand.castSucc < R.cuts R.lastBand.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hpBand :
      (x, R.cuts R.lastBand.succ) ∈ R.centeredBandCarrier R.lastBand :=
    R.mem_centeredBandCarrier_iff R.lastBand _ |>.2
      ⟨⟨hcuts.le, le_rfl⟩, hx⟩
  have hpCarrier :
      (x, R.cuts R.lastBand.succ) ∈ R.centeredCarrier := by
    rw [centeredCarrier, mem_iUnion]
    exact ⟨R.lastBand, hpBand⟩
  let q : ℕ → PlanePoint :=
    fun n => (x, R.cuts R.lastBand.succ + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape_sequence R.isClosed_centeredCarrier hpCarrier q
  · intro n hqn
    rw [centeredCarrier, mem_iUnion] at hqn
    rcases hqn with ⟨i, hqi⟩
    rw [R.mem_centeredBandCarrier_iff] at hqi
    have hidx : i.succ ≤ R.lastBand.succ := by
      apply Fin.mk_le_mk.mpr
      have hi := i.isLt
      have hn := R.bandCount_pos
      omega
    have hcutle := R.cuts_strict.monotone hidx
    dsimp only [q] at hqi
    linarith [hqi.1.2, escapeScale_pos n]
  · have hyLim : Tendsto
        (fun n : ℕ => R.cuts R.lastBand.succ + 1 / (n + 1))
        atTop (𝓝 (R.cuts R.lastBand.succ)) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hyLim

/-- A centered-carrier point at an interior height belongs to the unique
centered band. -/
theorem mem_centeredBandCarrier_of_mem_centeredCarrier_of_height_mem_Ioo
    (R : Region) (i : Fin R.bandCount) {p : PlanePoint}
    (hp : p ∈ R.centeredCarrier)
    (hy : p.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    p ∈ R.centeredBandCarrier i := by
  rw [centeredCarrier, mem_iUnion] at hp
  rcases hp with ⟨k, hpk⟩
  rw [R.mem_centeredBandCarrier_iff] at hpk
  have hki := R.band_eq_of_height_mem_Ioo_mem_Icc i k hy hpk.1
  subst k
  exact R.mem_centeredBandCarrier_iff i _ |>.2 hpk

/-- An interior centered-carrier point on a seam belongs to the lower incident
centered band. -/
theorem mem_centeredSeamLowerBand_of_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hp : (x, R.seamHeight i) ∈ interior R.centeredCarrier) :
    (x, R.seamHeight i) ∈ R.centeredBandCarrier (R.seamLowerBand i) := by
  let low := R.cuts (R.seamLowerBand i).castSucc
  let c := R.seamHeight i
  have hlc : low < c := by
    dsimp only [low, c]
    rw [← R.cuts_seamLower_succ i]
    exact R.cuts_strict Fin.castSucc_lt_succ
  let q : ℕ → PlanePoint :=
    fun n => (x, c - (c - low) / (n + 2 : ℝ))
  have hqHeight : ∀ n,
      (q n).2 ∈ Ioo (R.cuts (R.seamLowerBand i).castSucc)
        (R.cuts (R.seamLowerBand i).succ) := by
    intro n
    dsimp only [q, low, c]
    rw [R.cuts_seamLower_succ i]
    have hn : (0 : ℝ) < n + 2 := by positivity
    constructor <;> field_simp <;> nlinarith
  have hqLim : Tendsto q atTop (𝓝 (x, R.seamHeight i)) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => (c - low) / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    have hyLim : Tendsto
        (fun n : ℕ => c - (c - low) / (n + 2 : ℝ)) atTop (𝓝 c) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hdiv
    simpa only [q, c] using tendsto_const_nhds.prodMk_nhds hyLim
  apply (R.isClosed_centeredBandCarrier
    (R.seamLowerBand i)).mem_of_tendsto hqLim
  have hevInterior : ∀ᶠ n in atTop, q n ∈ interior R.centeredCarrier :=
    hqLim.eventually (isOpen_interior.mem_nhds hp)
  filter_upwards [hevInterior] with n hn
  exact R.mem_centeredBandCarrier_of_mem_centeredCarrier_of_height_mem_Ioo
    (R.seamLowerBand i) (interior_subset hn) (hqHeight n)

/-- An interior centered-carrier point on a seam belongs to the upper incident
centered band. -/
theorem mem_centeredSeamUpperBand_of_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hp : (x, R.seamHeight i) ∈ interior R.centeredCarrier) :
    (x, R.seamHeight i) ∈ R.centeredBandCarrier (R.seamUpperBand i) := by
  let c := R.seamHeight i
  let high := R.cuts (R.seamUpperBand i).succ
  have hch : c < high := by
    dsimp only [c, high]
    exact R.cuts_strict Fin.castSucc_lt_succ
  let q : ℕ → PlanePoint :=
    fun n => (x, c + (high - c) / (n + 2 : ℝ))
  have hqHeight : ∀ n,
      (q n).2 ∈ Ioo (R.cuts (R.seamUpperBand i).castSucc)
        (R.cuts (R.seamUpperBand i).succ) := by
    intro n
    dsimp only [q, c, high]
    rw [R.cuts_seamUpper_castSucc i]
    have hn : (0 : ℝ) < n + 2 := by positivity
    constructor <;> field_simp <;> nlinarith
  have hqLim : Tendsto q atTop (𝓝 (x, R.seamHeight i)) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => (high - c) / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    have hyLim : Tendsto
        (fun n : ℕ => c + (high - c) / (n + 2 : ℝ)) atTop (𝓝 c) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdiv
    simpa only [q, c] using tendsto_const_nhds.prodMk_nhds hyLim
  apply (R.isClosed_centeredBandCarrier
    (R.seamUpperBand i)).mem_of_tendsto hqLim
  have hevInterior : ∀ᶠ n in atTop, q n ∈ interior R.centeredCarrier :=
    hqLim.eventually (isOpen_interior.mem_nhds hp)
  filter_upwards [hevInterior] with n hn
  exact R.mem_centeredBandCarrier_of_mem_centeredCarrier_of_height_mem_Ioo
    (R.seamUpperBand i) (interior_subset hn) (hqHeight n)

/-- The centered fiber symmetric difference at a seam is literal frontier. -/
theorem centeredSeamSymmDiff_subset_frontier_centeredCarrier (R : Region)
    (i : Fin (R.bandCount - 1)) :
    {p | p.2 = R.seamHeight i ∧
      p.1 ∈ R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)} ⊆
      frontier R.centeredCarrier := by
  rintro ⟨x, y⟩ ⟨hy, hx⟩
  change y = R.seamHeight i at hy
  subst y
  rw [R.isClosed_centeredCarrier.frontier_eq]
  rcases hx with hx | hx
  · have hLowerHeight :
        R.seamHeight i ∈
          Icc (R.cuts (R.seamLowerBand i).castSucc)
            (R.cuts (R.seamLowerBand i).succ) := by
      rw [R.cuts_seamLower_succ i]
      exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
    have hpLower :
        (x, R.seamHeight i) ∈ R.centeredBandCarrier (R.seamLowerBand i) := by
      exact (R.mem_centeredBandCarrier_iff (R.seamLowerBand i) _).2
        ⟨hLowerHeight, hx.1⟩
    refine ⟨?_, ?_⟩
    · rw [centeredCarrier, mem_iUnion]
      exact ⟨R.seamLowerBand i, hpLower⟩
    · intro hpInterior
      have hpUpper := R.mem_centeredSeamUpperBand_of_mem_interior i hpInterior
      rw [R.mem_centeredBandCarrier_iff] at hpUpper
      exact hx.2 hpUpper.2
  · have hUpperHeight :
        R.seamHeight i ∈
          Icc (R.cuts (R.seamUpperBand i).castSucc)
            (R.cuts (R.seamUpperBand i).succ) :=
      ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩
    have hpUpper :
        (x, R.seamHeight i) ∈ R.centeredBandCarrier (R.seamUpperBand i) := by
      exact (R.mem_centeredBandCarrier_iff (R.seamUpperBand i) _).2
        ⟨hUpperHeight, hx.1⟩
    refine ⟨?_, ?_⟩
    · rw [centeredCarrier, mem_iUnion]
      exact ⟨R.seamUpperBand i, hpUpper⟩
    · intro hpInterior
      have hpLower := R.mem_centeredSeamLowerBand_of_mem_interior i hpInterior
      rw [R.mem_centeredBandCarrier_iff] at hpLower
      exact hx.2 hpLower.2

/-- Centered seam endpoint corrections are carried by centered closed graphs. -/
theorem centeredSeamEndpointSet_subset_centeredGraphTrace (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.centeredSeamEndpointSet i ⊆ R.centeredGraphTrace := by
  rintro p ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · simp only [centeredFiberEndpoints, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [centeredGraphTrace, mem_iUnion]
      exact ⟨R.seamLowerBand i, Or.inl
        ⟨R.seamHeight i, by
          rw [R.cuts_seamLower_succ i]
          exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩, rfl⟩⟩
    · rw [centeredGraphTrace, mem_iUnion]
      exact ⟨R.seamLowerBand i, Or.inr
        ⟨R.seamHeight i, by
          rw [R.cuts_seamLower_succ i]
          exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩, rfl⟩⟩
  · simp only [centeredFiberEndpoints, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [centeredGraphTrace, mem_iUnion]
      exact ⟨R.seamUpperBand i, Or.inl
        ⟨R.seamHeight i,
          ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩, rfl⟩⟩
    · rw [centeredGraphTrace, mem_iUnion]
      exact ⟨R.seamUpperBand i, Or.inr
        ⟨R.seamHeight i,
          ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩, rfl⟩⟩

/-- Every corrected centered seam trace is actual frontier. -/
theorem centeredSeamFrontierTrace_subset_frontier_centeredCarrier (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.centeredSeamFrontierTrace i ⊆ frontier R.centeredCarrier := by
  rintro p ⟨hy, hx⟩
  rcases hx with hx | hx
  · exact R.centeredSeamSymmDiff_subset_frontier_centeredCarrier i ⟨hy, hx⟩
  · apply R.centeredGraphTrace_subset_frontier_centeredCarrier
    apply R.centeredSeamEndpointSet_subset_centeredGraphTrace i
    refine ⟨p.1, hx, ?_⟩
    exact Prod.ext rfl hy.symm

/-- Strict membership in both centered one-sided intervals produces an open
two-sided neighborhood across the cut. -/
theorem mem_interior_centeredCarrier_of_common_strict (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hxLower : x ∈ Ioo
      (-R.totalWidth (R.seamLowerBand i) (R.seamHeight i) / 2)
      (R.totalWidth (R.seamLowerBand i) (R.seamHeight i) / 2))
    (hxUpper : x ∈ Ioo
      (-R.totalWidth (R.seamUpperBand i) (R.seamHeight i) / 2)
      (R.totalWidth (R.seamUpperBand i) (R.seamHeight i) / 2)) :
    (x, R.seamHeight i) ∈ interior R.centeredCarrier := by
  let low := R.cuts (R.seamLowerBand i).castSucc
  let high := R.cuts (R.seamUpperBand i).succ
  let U : Set PlanePoint :=
    {q | q.2 ∈ Ioo low high ∧
      -R.totalWidth (R.seamLowerBand i) q.2 / 2 < q.1 ∧
      q.1 < R.totalWidth (R.seamLowerBand i) q.2 / 2 ∧
      -R.totalWidth (R.seamUpperBand i) q.2 / 2 < q.1 ∧
      q.1 < R.totalWidth (R.seamUpperBand i) q.2 / 2}
  have hUopen : IsOpen U := by
    have h₁ : IsOpen {q : PlanePoint | q.2 ∈ Ioo low high} :=
      isOpen_Ioo.preimage continuous_snd
    have h₂ : IsOpen {q : PlanePoint |
        -R.totalWidth (R.seamLowerBand i) q.2 / 2 < q.1} :=
      isOpen_lt
        (((R.continuous_totalWidth (R.seamLowerBand i)).comp
          continuous_snd).neg.div_const 2) continuous_fst
    have h₃ : IsOpen {q : PlanePoint |
        q.1 < R.totalWidth (R.seamLowerBand i) q.2 / 2} :=
      isOpen_lt continuous_fst
        (((R.continuous_totalWidth (R.seamLowerBand i)).comp
          continuous_snd).div_const 2)
    have h₄ : IsOpen {q : PlanePoint |
        -R.totalWidth (R.seamUpperBand i) q.2 / 2 < q.1} :=
      isOpen_lt
        (((R.continuous_totalWidth (R.seamUpperBand i)).comp
          continuous_snd).neg.div_const 2) continuous_fst
    have h₅ : IsOpen {q : PlanePoint |
        q.1 < R.totalWidth (R.seamUpperBand i) q.2 / 2} :=
      isOpen_lt continuous_fst
        (((R.continuous_totalWidth (R.seamUpperBand i)).comp
          continuous_snd).div_const 2)
    rw [show U =
        ((({q : PlanePoint | q.2 ∈ Ioo low high} ∩
          {q | -R.totalWidth (R.seamLowerBand i) q.2 / 2 < q.1}) ∩
          {q | q.1 < R.totalWidth (R.seamLowerBand i) q.2 / 2}) ∩
          {q | -R.totalWidth (R.seamUpperBand i) q.2 / 2 < q.1}) ∩
          {q | q.1 < R.totalWidth (R.seamUpperBand i) q.2 / 2} by
      ext q
      simp only [U, mem_ofPred_eq, mem_inter_iff]
      tauto]
    exact (((h₁.inter h₂).inter h₃).inter h₄).inter h₅
  have hlc : low < R.seamHeight i := by
    dsimp only [low]
    rw [← R.cuts_seamLower_succ i]
    exact R.cuts_strict Fin.castSucc_lt_succ
  have hch : R.seamHeight i < high := by
    dsimp only [high]
    exact R.cuts_strict Fin.castSucc_lt_succ
  have hpU : (x, R.seamHeight i) ∈ U :=
    ⟨⟨hlc, hch⟩, hxLower.1, hxLower.2, hxUpper.1, hxUpper.2⟩
  have hUsub : U ⊆ R.centeredCarrier := by
    rintro q ⟨hqHeight, hqLowerLeft, hqLowerRight, hqUpperLeft, hqUpperRight⟩
    rw [centeredCarrier, mem_iUnion]
    by_cases hqc : q.2 ≤ R.seamHeight i
    · refine ⟨R.seamLowerBand i, ?_⟩
      rw [R.mem_centeredBandCarrier_iff]
      refine ⟨?_, ?_⟩
      · rw [R.cuts_seamLower_succ i]
        exact ⟨hqHeight.1.le, hqc⟩
      · exact ⟨hqLowerLeft.le, hqLowerRight.le⟩
    · refine ⟨R.seamUpperBand i, ?_⟩
      rw [R.mem_centeredBandCarrier_iff]
      exact ⟨⟨le_of_lt (lt_of_not_ge hqc), hqHeight.2.le⟩,
        ⟨hqUpperLeft.le, hqUpperRight.le⟩⟩
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hUopen.mem_nhds hpU) hUsub)

/-- Every point in the union of the centered one-sided seam fibers is either on
the corrected centered seam or is genuinely interior. -/
theorem mem_centeredSeamFrontierTrace_or_mem_interior (R : Region)
    (i : Fin (R.bandCount - 1)) {x : ℝ}
    (hx : x ∈ R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∪
      R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) :
    (x, R.seamHeight i) ∈ R.centeredSeamFrontierTrace i ∨
      (x, R.seamHeight i) ∈ interior R.centeredCarrier := by
  let A := R.centeredFiber (R.seamLowerBand i) (R.seamHeight i)
  let B := R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)
  let EA := R.centeredFiberEndpoints (R.seamLowerBand i) (R.seamHeight i)
  let EB := R.centeredFiberEndpoints (R.seamUpperBand i) (R.seamHeight i)
  change x ∈ A ∪ B at hx
  by_cases hEA : x ∈ EA
  · left
    exact ⟨rfl, Or.inr (Or.inl hEA)⟩
  by_cases hEB : x ∈ EB
  · left
    exact ⟨rfl, Or.inr (Or.inr hEB)⟩
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · right
      apply R.mem_interior_centeredCarrier_of_common_strict i
      · rcases hA with ⟨hAl, hAr⟩
        exact ⟨lt_of_le_of_ne hAl fun h =>
          hEA (by simp [EA, centeredFiberEndpoints, h]),
          lt_of_le_of_ne hAr fun h =>
            hEA (by simp [EA, centeredFiberEndpoints, h.symm])⟩
      · rcases hB with ⟨hBl, hBr⟩
        exact ⟨lt_of_le_of_ne hBl fun h =>
          hEB (by simp [EB, centeredFiberEndpoints, h]),
          lt_of_le_of_ne hBr fun h =>
            hEB (by simp [EB, centeredFiberEndpoints, h.symm])⟩
    · left
      exact ⟨rfl, Or.inl (Or.inl ⟨hA, hB⟩)⟩
  · have hB : x ∈ B := hx.resolve_left hA
    left
    exact ⟨rfl, Or.inl (Or.inr ⟨hB, hA⟩)⟩

/-- The complete centered trace is actual frontier. -/
theorem completeCenteredFrontierTrace_subset_frontier_centeredCarrier (R : Region) :
    R.completeCenteredFrontierTrace ⊆ frontier R.centeredCarrier := by
  rintro p hp
  rcases hp with ((hp | hp) | hp) | hp
  · exact R.centeredGraphTrace_subset_frontier_centeredCarrier hp
  · exact R.centeredLowerOuterTrace_subset_frontier_centeredCarrier hp
  · exact R.centeredUpperOuterTrace_subset_frontier_centeredCarrier hp
  · rw [mem_iUnion] at hp
    rcases hp with ⟨i, hp⟩
    exact R.centeredSeamFrontierTrace_subset_frontier_centeredCarrier i hp

private theorem centeredGraphTrace_subset_completeCenteredFrontierTrace (R : Region) :
    R.centeredGraphTrace ⊆ R.completeCenteredFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inl (Or.inl hp))

private theorem centeredLowerOuterTrace_subset_completeCenteredFrontierTrace
    (R : Region) :
    R.centeredLowerOuterTrace ⊆ R.completeCenteredFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inl (Or.inr hp))

private theorem centeredUpperOuterTrace_subset_completeCenteredFrontierTrace
    (R : Region) :
    R.centeredUpperOuterTrace ⊆ R.completeCenteredFrontierTrace := by
  intro p hp
  exact Or.inl (Or.inr hp)

private theorem centeredSeamFrontierTrace_subset_completeCenteredFrontierTrace
    (R : Region) (i : Fin (R.bandCount - 1)) :
    R.centeredSeamFrontierTrace i ⊆ R.completeCenteredFrontierTrace := by
  intro p hp
  exact Or.inr (mem_iUnion.mpr ⟨i, hp⟩)

/-- Strict centered graph inequalities at an interior height give a genuine
interior point of that centered band. -/
theorem mem_interior_centeredBandCarrier_of_strict (R : Region)
    (i : Fin R.bandCount) (p : PlanePoint)
    (hy : p.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hx : p.1 ∈ Ioo (-R.totalWidth i p.2 / 2) (R.totalWidth i p.2 / 2)) :
    p ∈ interior (R.centeredBandCarrier i) := by
  let U : Set PlanePoint :=
    {q | q.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∧
      -R.totalWidth i q.2 / 2 < q.1 ∧ q.1 < R.totalWidth i q.2 / 2}
  have hUopen : IsOpen U := by
    have h₁ : IsOpen {q : PlanePoint |
        q.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)} :=
      isOpen_Ioo.preimage continuous_snd
    have h₂ : IsOpen {q : PlanePoint | -R.totalWidth i q.2 / 2 < q.1} :=
      isOpen_lt
        (((R.continuous_totalWidth i).comp continuous_snd).neg.div_const 2)
        continuous_fst
    have h₃ : IsOpen {q : PlanePoint | q.1 < R.totalWidth i q.2 / 2} :=
      isOpen_lt continuous_fst
        (((R.continuous_totalWidth i).comp continuous_snd).div_const 2)
    rw [show U =
        ({q : PlanePoint |
          q.2 ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)} ∩
          {q | -R.totalWidth i q.2 / 2 < q.1}) ∩
          {q | q.1 < R.totalWidth i q.2 / 2} by
      ext q
      simp only [U, mem_ofPred_eq, mem_inter_iff]
      tauto]
    exact (h₁.inter h₂).inter h₃
  have hpU : p ∈ U := ⟨hy, hx⟩
  have hUsub : U ⊆ R.centeredBandCarrier i := by
    rintro q ⟨hqHeight, hqLeft, hqRight⟩
    rw [R.mem_centeredBandCarrier_iff]
    exact ⟨⟨hqHeight.1.le, hqHeight.2.le⟩, ⟨hqLeft.le, hqRight.le⟩⟩
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (hUopen.mem_nhds hpU) hUsub)

/-- Every centered-carrier frontier point lies on the derived complete trace. -/
theorem frontier_centeredCarrier_subset_completeCenteredFrontierTrace (R : Region) :
    frontier R.centeredCarrier ⊆ R.completeCenteredFrontierTrace := by
  rintro ⟨x, y⟩ hp
  have hpCarrier : (x, y) ∈ R.centeredCarrier :=
    R.isClosed_centeredCarrier.frontier_subset hp
  have hpNotInterior : (x, y) ∉ interior R.centeredCarrier :=
    (mem_frontier_iff_notMem_interior hpCarrier).mp hp
  rw [centeredCarrier, mem_iUnion] at hpCarrier
  rcases hpCarrier with ⟨i, hpi⟩
  rw [R.mem_centeredBandCarrier_iff] at hpi
  change y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
    x ∈ R.centeredFiber i y at hpi
  rcases hpi.1.1.eq_or_lt with hLower | hLower
  · have hyEq : y = R.cuts i.castSucc := hLower.symm
    subst y
    rcases R.eq_firstBand_or_exists_seamUpperBand i with hi | ⟨s, hsi⟩
    · subst i
      apply R.centeredLowerOuterTrace_subset_completeCenteredFrontierTrace
      exact ⟨rfl, hpi.2⟩
    · subst i
      have hxUnion :
          x ∈ R.centeredFiber (R.seamLowerBand s) (R.seamHeight s) ∪
            R.centeredFiber (R.seamUpperBand s) (R.seamHeight s) :=
        Or.inr hpi.2
      rcases R.mem_centeredSeamFrontierTrace_or_mem_interior s hxUnion with
        hseam | hinterior
      · exact R.centeredSeamFrontierTrace_subset_completeCenteredFrontierTrace
          s hseam
      · exact False.elim (hpNotInterior hinterior)
  · rcases hpi.1.2.eq_or_lt with hUpper | hUpper
    · subst y
      rcases R.eq_lastBand_or_exists_seamLowerBand i with hi | ⟨s, hsi⟩
      · subst i
        apply R.centeredUpperOuterTrace_subset_completeCenteredFrontierTrace
        exact ⟨rfl, hpi.2⟩
      · subst i
        have hxUnion :
            x ∈ R.centeredFiber (R.seamLowerBand s) (R.seamHeight s) ∪
              R.centeredFiber (R.seamUpperBand s) (R.seamHeight s) :=
          Or.inl hpi.2
        rcases R.mem_centeredSeamFrontierTrace_or_mem_interior s hxUnion with
          hseam | hinterior
        · exact R.centeredSeamFrontierTrace_subset_completeCenteredFrontierTrace
            s hseam
        · exact False.elim (hpNotInterior hinterior)
    · have hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) :=
        ⟨hLower, hUpper⟩
      rcases hpi.2.1.eq_or_lt with hLeft | hLeft
      · apply R.centeredGraphTrace_subset_completeCenteredFrontierTrace
        rw [centeredGraphTrace, mem_iUnion]
        exact ⟨i, Or.inl
          ⟨y, ⟨hLower.le, hUpper.le⟩, Prod.ext hLeft rfl⟩⟩
      · rcases hpi.2.2.eq_or_lt with hRight | hRight
        · apply R.centeredGraphTrace_subset_completeCenteredFrontierTrace
          rw [centeredGraphTrace, mem_iUnion]
          exact ⟨i, Or.inr
            ⟨y, ⟨hLower.le, hUpper.le⟩, Prod.ext hRight.symm rfl⟩⟩
        · exfalso
          apply hpNotInterior
          exact interior_mono
            (by
              intro q hq
              rw [centeredCarrier, mem_iUnion]
              exact ⟨i, hq⟩)
            (R.mem_interior_centeredBandCarrier_of_strict i (x, y) hy
              ⟨hLeft, hRight⟩)

/-- Exact complete topological-frontier decomposition of the literal centered
competitor. -/
theorem frontier_centeredCarrier (R : Region) :
    frontier R.centeredCarrier = R.completeCenteredFrontierTrace :=
  Set.Subset.antisymm R.frontier_centeredCarrier_subset_completeCenteredFrontierTrace
    R.completeCenteredFrontierTrace_subset_frontier_centeredCarrier

/-- The corrected original seam is exactly the one-sided fiber symmetric
difference plus its finite endpoint correction. -/
theorem seamFrontierTrace_eq_symmDiff_union_endpointSet (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamFrontierTrace i = R.seamSymmDiff i ∪ R.seamEndpointSet i := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hy, hx⟩
    · refine Or.inr ⟨p.1, hx, ?_⟩
      exact Prod.ext rfl hy.symm
  · rintro (hp | hp)
    · exact ⟨hp.1, Or.inl hp.2⟩
    · rcases hp with ⟨x, hx, rfl⟩
      exact ⟨rfl, Or.inr hx⟩

/-- The centered seam has the same exact symmetric-difference-plus-finite-
endpoint form. -/
theorem centeredSeamFrontierTrace_eq_symmDiff_union_endpointSet (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.centeredSeamFrontierTrace i =
      {p | p.2 = R.seamHeight i ∧
        p.1 ∈ R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)} ∪
        R.centeredSeamEndpointSet i := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hy, hx⟩
    · refine Or.inr ⟨p.1, hx, ?_⟩
      exact Prod.ext rfl hy.symm
  · rintro (hp | hp)
    · exact ⟨hp.1, Or.inl hp.2⟩
    · rcases hp with ⟨x, hx, rfl⟩
      exact ⟨rfl, Or.inr hx⟩

/-- Every centered seam endpoint correction is finite. -/
theorem centeredSeamEndpointSet_finite (R : Region)
    (i : Fin (R.bandCount - 1)) :
    (R.centeredSeamEndpointSet i).Finite := by
  apply Set.Finite.image
  simp [centeredFiberEndpoints]

/-- Centered finite seam corrections carry no Euclidean `H¹` cost. -/
theorem hausdorffMeasure_centeredSeamEndpointSet (R : Region)
    (i : Fin (R.bandCount - 1)) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' R.centeredSeamEndpointSet i) = 0 := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  exact (R.centeredSeamEndpointSet_finite i).image planeEuclideanHomeomorph
    |>.measure_zero μH[1]
end Region
end FiniteBandRearrangement
end CMVRelaxation
