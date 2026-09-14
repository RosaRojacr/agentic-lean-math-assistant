import CMVFiniteBandRearrangement

open Set Function Filter MeasureTheory
open scoped Topology ENNReal symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement
namespace ThreeBandExample

/-- The lower literal closed band of the independent `lambda = 2` specimen. -/
def lowerBand : Set PlanePoint := Icc (-2 : ℝ) 0 ×ˢ Icc (-2 : ℝ) (-1)

/-- The middle literal closed band. -/
def middleBand : Set PlanePoint := Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

/-- The upper literal closed band. -/
def upperBand : Set PlanePoint := Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2

/-- Actual closed union.  At a shared height both adjacent closed traces are
present, rather than one band overriding the other. -/
def carrier : Set PlanePoint := lowerBand ∪ middleBand ∪ upperBand

/-- The six endpoint graphs, retained as closed traces. -/
def verticalTraces : Set PlanePoint :=
  ({(-2 : ℝ), 0} ×ˢ Icc (-2 : ℝ) (-1)) ∪
    ({(-1 : ℝ), 1} ×ˢ Icc (-1 : ℝ) 1) ∪
      ({(0 : ℝ), 2} ×ˢ Icc (1 : ℝ) 2)

/-- Both outer-end traces. -/
def outerTraces : Set PlanePoint :=
  (Icc (-2 : ℝ) 0 ×ˢ {(-2 : ℝ)}) ∪
    (Icc (0 : ℝ) 2 ×ˢ {(2 : ℝ)})

/-- Actual lower-interface mismatch.  The overlap `[-1,0]` is filled by both
one-sided bands; only the two length-one residuals remain horizontal frontier. -/
def lowerSeam : Set PlanePoint :=
  ((Icc (-2 : ℝ) (-1) ∪ Icc (0 : ℝ) 1) ×ˢ {(-1 : ℝ)})

/-- Actual upper-interface mismatch. -/
def upperSeam : Set PlanePoint :=
  ((Icc (-1 : ℝ) 0 ∪ Icc (1 : ℝ) 2) ×ˢ {(1 : ℝ)})

/-- Finite endpoint remainder in the lower seam identity. -/
def lowerSeamEndpoints : Set PlanePoint :=
  {((-1 : ℝ), (-1 : ℝ)), ((0 : ℝ), (-1 : ℝ))}

/-- Finite endpoint remainder in the upper seam identity. -/
def upperSeamEndpoints : Set PlanePoint :=
  {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (1 : ℝ))}

/-- Claimed complete trace, later proved equal to the topological frontier of
`carrier`. -/
def completeTrace : Set PlanePoint :=
  verticalTraces ∪ outerTraces ∪ lowerSeam ∪ upperSeam

@[simp] theorem isClosed_lowerBand : IsClosed lowerBand :=
  isClosed_Icc.prod isClosed_Icc

@[simp] theorem isClosed_middleBand : IsClosed middleBand :=
  isClosed_Icc.prod isClosed_Icc

@[simp] theorem isClosed_upperBand : IsClosed upperBand :=
  isClosed_Icc.prod isClosed_Icc

@[simp] theorem isClosed_carrier : IsClosed carrier :=
  (isClosed_lowerBand.union isClosed_middleBand).union isClosed_upperBand

/-- Generic sections of the lower rectangle. -/
theorem horizontalSection_lowerBand (y : ℝ) :
    horizontalSection lowerBand y =
      if y ∈ Icc (-2 : ℝ) (-1) then Icc (-2 : ℝ) 0 else ∅ := by
  ext x
  simp only [horizontalSection, lowerBand, mem_preimage, mem_prod]
  by_cases hy : y ∈ Icc (-2 : ℝ) (-1) <;> simp [hy]

/-- Generic sections of the middle rectangle. -/
theorem horizontalSection_middleBand (y : ℝ) :
    horizontalSection middleBand y =
      if y ∈ Icc (-1 : ℝ) 1 then Icc (-1 : ℝ) 1 else ∅ := by
  ext x
  simp only [horizontalSection, middleBand, mem_preimage, mem_prod]
  by_cases hy : y ∈ Icc (-1 : ℝ) 1 <;> simp [hy]

/-- Generic sections of the upper rectangle. -/
theorem horizontalSection_upperBand (y : ℝ) :
    horizontalSection upperBand y =
      if y ∈ Icc (1 : ℝ) 2 then Icc (0 : ℝ) 2 else ∅ := by
  ext x
  simp only [horizontalSection, upperBand, mem_preimage, mem_prod]
  by_cases hy : y ∈ Icc (1 : ℝ) 2 <;> simp [hy]

/-- Exact generic section formula for the literal three-band union. -/
theorem horizontalSection_carrier (y : ℝ) :
    horizontalSection carrier y =
      (if y ∈ Icc (-2 : ℝ) (-1) then Icc (-2 : ℝ) 0 else ∅) ∪
      (if y ∈ Icc (-1 : ℝ) 1 then Icc (-1 : ℝ) 1 else ∅) ∪
      (if y ∈ Icc (1 : ℝ) 2 then Icc (0 : ℝ) 2 else ∅) := by
  unfold carrier
  change (fun x : ℝ => (x, y)) ⁻¹' (lowerBand ∪ middleBand ∪ upperBand) = _
  rw [preimage_union, preimage_union]
  change horizontalSection lowerBand y ∪ horizontalSection middleBand y ∪
    horizontalSection upperBand y = _
  rw [horizontalSection_lowerBand, horizontalSection_middleBand,
    horizontalSection_upperBand]

/-- The two adjacent closed traces fill the full lower seam section. -/
theorem horizontalSection_carrier_neg_one :
    horizontalSection carrier (-1) = Icc (-2 : ℝ) 1 := by
  rw [horizontalSection_carrier]
  norm_num
  ext x
  simp only [mem_union, mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> linarith
  · intro h
    by_cases hx : x ≤ 0
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨by linarith, h.2⟩

/-- The two adjacent closed traces fill the full upper seam section. -/
theorem horizontalSection_carrier_one :
    horizontalSection carrier 1 = Icc (-1 : ℝ) 2 := by
  rw [horizontalSection_carrier]
  norm_num
  ext x
  simp only [mem_union, mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> linarith
  · intro h
    by_cases hx : x ≤ 1
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨by linarith, h.2⟩

/-- The overlap across the lower seam is genuinely planar interior, not a
zero-area identification inferred from section arithmetic. -/
theorem lowerOverlap_mem_interior {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    (x, -1) ∈ interior carrier := by
  let O : Set PlanePoint := Ioo (-1 : ℝ) 0 ×ˢ Ioo (-2 : ℝ) 1
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds (show (x, -1) ∈ O by
      exact ⟨hx, by norm_num⟩))
  rintro ⟨u, v⟩ huv
  change (u, v) ∈ carrier
  rcases huv with ⟨hu, hv⟩
  by_cases hvm : v ≤ -1
  · exact Or.inl (Or.inl ⟨⟨by linarith [hu.1], hu.2.le⟩,
      ⟨hv.1.le, hvm⟩⟩)
  · exact Or.inl (Or.inr ⟨⟨hu.1.le, by linarith [hu.2]⟩,
      ⟨by linarith, hv.2.le⟩⟩)

/-- The upper overlap is likewise actual planar interior. -/
theorem upperOverlap_mem_interior {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (x, 1) ∈ interior carrier := by
  let O : Set PlanePoint := Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 2
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds (show (x, 1) ∈ O by
      exact ⟨hx, by norm_num⟩))
  rintro ⟨u, v⟩ huv
  change (u, v) ∈ carrier
  rcases huv with ⟨hu, hv⟩
  by_cases hvp : v ≤ 1
  · exact Or.inl (Or.inr ⟨⟨by linarith [hu.1], hu.2.le⟩,
      ⟨hv.1.le, hvp⟩⟩)
  · exact Or.inr ⟨⟨hu.1.le, by linarith [hu.2]⟩,
      ⟨by linarith, hv.2.le⟩⟩

private theorem frontier_union_subset_union_frontier (s t : Set PlanePoint) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t := by
  intro p hp
  rcases frontier_union_subset s t hp with hp | hp
  · exact Or.inl hp.1
  · exact Or.inr hp.2

private theorem frontier_lowerBand :
    frontier lowerBand =
      ({(-2 : ℝ), 0} ×ˢ Icc (-2 : ℝ) (-1)) ∪
        (Icc (-2 : ℝ) 0 ×ˢ {(-2 : ℝ), -1}) := by
  rw [lowerBand, frontier_prod_eq, closure_Icc, closure_Icc,
    frontier_Icc (by norm_num : (-2 : ℝ) ≤ 0),
    frontier_Icc (by norm_num : (-2 : ℝ) ≤ -1), union_comm]

private theorem frontier_middleBand :
    frontier middleBand =
      ({(-1 : ℝ), 1} ×ˢ Icc (-1 : ℝ) 1) ∪
        (Icc (-1 : ℝ) 1 ×ˢ {(-1 : ℝ), 1}) := by
  rw [middleBand, frontier_prod_eq,
    frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1), union_comm]
  simp only [closure_Icc]

private theorem frontier_upperBand :
    frontier upperBand =
      ({(0 : ℝ), 2} ×ˢ Icc (1 : ℝ) 2) ∪
        (Icc (0 : ℝ) 2 ×ˢ {(1 : ℝ), 2}) := by
  rw [upperBand, frontier_prod_eq, closure_Icc, closure_Icc,
    frontier_Icc (by norm_num : (0 : ℝ) ≤ 2),
    frontier_Icc (by norm_num : (1 : ℝ) ≤ 2), union_comm]

private theorem lowerVertical_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ {(-2 : ℝ), 0} ×ˢ Icc (-2 : ℝ) (-1)) :
    p ∈ completeTrace := by
  simp only [completeTrace, verticalTraces, mem_union]
  aesop

private theorem middleVertical_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ {(-1 : ℝ), 1} ×ˢ Icc (-1 : ℝ) 1) :
    p ∈ completeTrace := by
  simp only [completeTrace, verticalTraces, mem_union]
  aesop

private theorem upperVertical_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ {(0 : ℝ), 2} ×ˢ Icc (1 : ℝ) 2) :
    p ∈ completeTrace := by
  simp only [completeTrace, verticalTraces, mem_union]
  aesop

private theorem lowerOuter_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ Icc (-2 : ℝ) 0 ×ˢ {(-2 : ℝ)}) :
    p ∈ completeTrace := by
  simp only [completeTrace, outerTraces, mem_union]
  aesop

private theorem upperOuter_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ Icc (0 : ℝ) 2 ×ˢ {(2 : ℝ)}) :
    p ∈ completeTrace := by
  simp only [completeTrace, outerTraces, mem_union]
  aesop

private theorem lowerSeam_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ lowerSeam) : p ∈ completeTrace := by
  simp only [completeTrace, mem_union]
  aesop

private theorem upperSeam_mem_completeTrace {p : PlanePoint}
    (hp : p ∈ upperSeam) : p ∈ completeTrace := by
  simp only [completeTrace, mem_union]
  aesop

/-- Every global frontier point lies on one of the six endpoint graphs, an
outer trace, or one of the two true seam mismatches.  The filled overlaps are
removed using their proved planar-interior neighborhoods. -/
theorem frontier_carrier_subset_completeTrace : frontier carrier ⊆ completeTrace := by
  intro p hp
  have hparts : p ∈ frontier lowerBand ∨ p ∈ frontier middleBand ∨
      p ∈ frontier upperBand := by
    have htop := frontier_union_subset_union_frontier
      (lowerBand ∪ middleBand) upperBand hp
    rcases htop with hlm | hu
    · rcases frontier_union_subset_union_frontier lowerBand middleBand hlm with hl | hm
      · exact Or.inl hl
      · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hu)
  have hnotInterior : p ∉ interior carrier := by
    exact (mem_frontier_iff_notMem_interior
      (isClosed_carrier.frontier_subset hp)).mp hp
  rcases p with ⟨x, y⟩
  rcases hparts with hl | hm | hu
  · rw [frontier_lowerBand] at hl
    rcases hl with hvertical | hhorizontal
    · exact lowerVertical_mem_completeTrace hvertical
    · rcases hhorizontal with ⟨hx, hy⟩
      rcases hy with rfl | rfl
      · exact lowerOuter_mem_completeTrace ⟨hx, rfl⟩
      · by_cases hleft : x ≤ -1
        · apply lowerSeam_mem_completeTrace
          exact ⟨Or.inl ⟨hx.1, hleft⟩, rfl⟩
        · by_cases hzero : x < 0
          · exfalso
            exact hnotInterior (lowerOverlap_mem_interior ⟨by linarith, hzero⟩)
          · apply lowerSeam_mem_completeTrace
            exact ⟨Or.inr ⟨by linarith, by linarith [hx.2]⟩, rfl⟩
  · rw [frontier_middleBand] at hm
    rcases hm with hvertical | hhorizontal
    · exact middleVertical_mem_completeTrace hvertical
    · rcases hhorizontal with ⟨hx, hy⟩
      rcases hy with rfl | rfl
      · by_cases hleft : x ≤ -1
        · apply lowerSeam_mem_completeTrace
          exact ⟨Or.inl ⟨by linarith [hx.1], hleft⟩, rfl⟩
        · by_cases hzero : x < 0
          · exfalso
            exact hnotInterior (lowerOverlap_mem_interior ⟨by linarith, hzero⟩)
          · apply lowerSeam_mem_completeTrace
            exact ⟨Or.inr ⟨by linarith, hx.2⟩, rfl⟩
      · by_cases hzero : x ≤ 0
        · apply upperSeam_mem_completeTrace
          exact ⟨Or.inl ⟨hx.1, hzero⟩, rfl⟩
        · by_cases hone : x < 1
          · exfalso
            exact hnotInterior (upperOverlap_mem_interior ⟨by linarith, hone⟩)
          · apply upperSeam_mem_completeTrace
            exact ⟨Or.inr ⟨by linarith, by linarith [hx.2]⟩, rfl⟩
  · rw [frontier_upperBand] at hu
    rcases hu with hvertical | hhorizontal
    · exact upperVertical_mem_completeTrace hvertical
    · rcases hhorizontal with ⟨hx, hy⟩
      rcases hy with rfl | rfl
      · by_cases hzero : x ≤ 0
        · apply upperSeam_mem_completeTrace
          exact ⟨Or.inl ⟨by linarith [hx.1], hzero⟩, rfl⟩
        · by_cases hone : x < 1
          · exfalso
            exact hnotInterior (upperOverlap_mem_interior ⟨by linarith, hone⟩)
          · apply upperSeam_mem_completeTrace
            exact ⟨Or.inr ⟨le_of_not_gt hone, hx.2⟩, rfl⟩
      · exact upperOuter_mem_completeTrace ⟨hx, rfl⟩

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

private theorem leftLowerVertical_frontier {y : ℝ} (hy : y ∈ Icc (-2 : ℝ) (-1)) :
    ((-2 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (-2 - 1 / (n + 1 : ℝ), y)
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inl ⟨by norm_num, hy⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hx, _hy⟩
        linarith [hx.1]
      · rintro ⟨hx, _hy⟩
        linarith [hx.1]
    · rintro ⟨hx, _hy⟩
      linarith [hx.1]
  · have hx : Tendsto (fun n : ℕ => (-2 : ℝ) - 1 / (n + 1)) atTop (𝓝 (-2)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact hx.prodMk_nhds tendsto_const_nhds

private theorem rightLowerVertical_frontier {y : ℝ} (hy : y ∈ Icc (-2 : ℝ) (-1)) :
    ((0 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (1 / (n + 1 : ℝ), y - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inl ⟨by norm_num, hy⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hx, _hy⟩
        linarith [hx.2]
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.1, hy.2]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.1, hy.2]
  · have hx : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => y - 1 / (n + 1 : ℝ)) atTop (𝓝 y) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact hx.prodMk_nhds hy'

private theorem leftMiddleVertical_frontier {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    ((-1 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (-1 - 1 / (n + 1 : ℝ), y + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inr ⟨by norm_num, hy⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hy.1, hyq.2]
      · rintro ⟨hx, _hy⟩
        linarith [hx.1]
    · rintro ⟨hx, _hy⟩
      linarith [hx.1]
  · have hx : Tendsto (fun n : ℕ => (-1 : ℝ) - 1 / (n + 1)) atTop (𝓝 (-1)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => y + 1 / (n + 1 : ℝ)) atTop (𝓝 y) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact hx.prodMk_nhds hy'

private theorem rightMiddleVertical_frontier {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    ((1 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (1 + 1 / (n + 1 : ℝ), y - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inr ⟨by norm_num, hy⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hx, _hy⟩
        linarith [hx.2]
      · rintro ⟨hx, _hy⟩
        linarith [hx.2]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.1, hy.2]
  · have hx : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => y - 1 / (n + 1 : ℝ)) atTop (𝓝 y) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact hx.prodMk_nhds hy'

private theorem leftUpperVertical_frontier {y : ℝ} (hy : y ∈ Icc (1 : ℝ) 2) :
    ((0 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n =>
    (-(1 / (n + 1 : ℝ)), y + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inr ⟨by norm_num, hy⟩) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hy.1, hyq.2]
      · rintro ⟨_hx, hyq⟩
        linarith [hy.1, hyq.2]
    · rintro ⟨hx, _hy⟩
      linarith [hx.1]
  · have hx : Tendsto (fun n : ℕ => -(1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
      simpa using escapeScale_tendsto.neg
    have hy' : Tendsto (fun n : ℕ => y + 1 / (n + 1 : ℝ)) atTop (𝓝 y) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact hx.prodMk_nhds hy'

private theorem rightUpperVertical_frontier {y : ℝ} (hy : y ∈ Icc (1 : ℝ) 2) :
    ((2 : ℝ), y) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (2 + 1 / (n + 1 : ℝ), y)
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inr ⟨by norm_num, hy⟩) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hx, _hy⟩
        linarith [hx.2]
      · rintro ⟨hx, _hy⟩
        linarith [hx.2]
    · rintro ⟨hx, _hy⟩
      linarith [hx.2]
  · have hx : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / (n + 1)) atTop (𝓝 2) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact hx.prodMk_nhds tendsto_const_nhds

private theorem lowerOuter_frontier {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 0) :
    (x, (-2 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (x, -2 - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inl ⟨hx, by norm_num⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.1]
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.1]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.1]
  · have hy : Tendsto (fun n : ℕ => (-2 : ℝ) - 1 / (n + 1)) atTop (𝓝 (-2)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hy

private theorem upperOuter_frontier {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    (x, (2 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n => (x, 2 + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inr ⟨hx, by norm_num⟩) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.2]
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.2]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.2]
  · have hy : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / (n + 1)) atTop (𝓝 2) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact tendsto_const_nhds.prodMk_nhds hy

private theorem lowerSeamLeft_frontier {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) (-1)) :
    (x, (-1 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n =>
    (x - 1 / (n + 1 : ℝ), -1 + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inl ⟨⟨hx.1, by linarith [hx.2]⟩, by norm_num⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.2]
      · rintro ⟨hxq, _hy⟩
        linarith [hxq.1, hx.2]
    · rintro ⟨hxq, _hy⟩
      linarith [hxq.1, hx.2]
  · have hx' : Tendsto (fun n : ℕ => x - 1 / (n + 1 : ℝ)) atTop (𝓝 x) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => (-1 : ℝ) + 1 / (n + 1)) atTop (𝓝 (-1)) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact hx'.prodMk_nhds hy'

private theorem lowerSeamRight_frontier {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (x, (-1 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n =>
    (x + 1 / (n + 1 : ℝ), -1 - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inr ⟨⟨by linarith [hx.1], hx.2⟩, by norm_num⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hxq, _hy⟩
        linarith [hxq.2, hx.1]
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.1]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.1]
  · have hx' : Tendsto (fun n : ℕ => x + 1 / (n + 1 : ℝ)) atTop (𝓝 x) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => (-1 : ℝ) - 1 / (n + 1)) atTop (𝓝 (-1)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact hx'.prodMk_nhds hy'

private theorem upperSeamLeft_frontier {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 0) :
    (x, (1 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n =>
    (x - 1 / (n + 1 : ℝ), 1 + 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inl (Or.inr ⟨⟨hx.1, by linarith [hx.2]⟩, by norm_num⟩)) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.2]
      · rintro ⟨_hx, hyq⟩
        linarith [hyq.2]
    · rintro ⟨hxq, _hy⟩
      linarith [hxq.1, hx.2]
  · have hx' : Tendsto (fun n : ℕ => x - 1 / (n + 1 : ℝ)) atTop (𝓝 x) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    exact hx'.prodMk_nhds hy'

private theorem upperSeamRight_frontier {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    (x, (1 : ℝ)) ∈ frontier carrier := by
  let q : ℕ → PlanePoint := fun n =>
    (x + 1 / (n + 1 : ℝ), 1 - 1 / (n + 1 : ℝ))
  apply mem_frontier_of_escape isClosed_carrier
    (Or.inr ⟨⟨by linarith [hx.1], hx.2⟩, by norm_num⟩) q
  · intro n
    have hd := escapeScale_pos n
    simp only [q, carrier, lowerBand, middleBand, upperBand, mem_union, mem_prod,
      mem_Icc, not_or]
    constructor
    · constructor
      · rintro ⟨hxq, _hy⟩
        linarith [hxq.2, hx.1]
      · rintro ⟨hxq, _hy⟩
        linarith [hxq.2, hx.1]
    · rintro ⟨_hx, hyq⟩
      linarith [hyq.1]
  · have hx' : Tendsto (fun n : ℕ => x + 1 / (n + 1 : ℝ)) atTop (𝓝 x) := by
      simpa only [add_zero] using tendsto_const_nhds.add escapeScale_tendsto
    have hy' : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub escapeScale_tendsto
    exact hx'.prodMk_nhds hy'

/-- Every displayed trace is an actual frontier point; seams and outer ends are
not omitted from the literal accounting. -/
theorem completeTrace_subset_frontier_carrier : completeTrace ⊆ frontier carrier := by
  rintro ⟨x, y⟩ hp
  simp only [completeTrace, verticalTraces, outerTraces, lowerSeam, upperSeam,
    mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc] at hp
  rcases hp with (((hvertical | houter) | hlower) | hupper)
  · rcases hvertical with ((h | h) | h)
    · rcases h with ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · exact leftLowerVertical_frontier hy
      · exact rightLowerVertical_frontier hy
    · rcases h with ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · exact leftMiddleVertical_frontier hy
      · exact rightMiddleVertical_frontier hy
    · rcases h with ⟨hx, hy⟩
      rcases hx with rfl | rfl
      · exact leftUpperVertical_frontier hy
      · exact rightUpperVertical_frontier hy
  · rcases houter with h | h
    · rcases h with ⟨hx, rfl⟩
      exact lowerOuter_frontier hx
    · rcases h with ⟨hx, rfl⟩
      exact upperOuter_frontier hx
  · rcases hlower with ⟨hx, rfl⟩
    rcases hx with hx | hx
    · exact lowerSeamLeft_frontier hx
    · exact lowerSeamRight_frontier hx
  · rcases hupper with ⟨hx, rfl⟩
    rcases hx with hx | hx
    · exact upperSeamLeft_frontier hx
    · exact upperSeamRight_frontier hx

/-- Complete topological-frontier decomposition of the independent specimen. -/
theorem frontier_carrier : frontier carrier = completeTrace :=
  Set.Subset.antisymm frontier_carrier_subset_completeTrace
    completeTrace_subset_frontier_carrier

/-- The lower seam is the one-sided trace symmetric difference modulo exactly
the two finite overlap endpoints, which are already retained by endpoint
graphs. -/
theorem lowerSeam_eq_symmDiff_union_endpoints :
    lowerSeam =
      ((Icc (-2 : ℝ) 0 ∆ Icc (-1 : ℝ) 1) ×ˢ {(-1 : ℝ)}) ∪
        lowerSeamEndpoints := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [lowerSeam, lowerSeamEndpoints, mem_prod, mem_union, mem_Icc,
    mem_singleton_iff, mem_symmDiff, mem_insert_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, rfl⟩
    rcases hx with hx | hx
    · by_cases h : x = -1
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
      · exact Or.inl ⟨Or.inl ⟨⟨hx.1, by linarith [hx.2]⟩,
          fun hmem => h (le_antisymm hx.2 hmem.1)⟩, rfl⟩
    · by_cases h : x = 0
      · exact Or.inr (Or.inr ⟨h, rfl⟩)
      · exact Or.inl ⟨Or.inr ⟨⟨by linarith [hx.1], hx.2⟩,
          fun hmem => h (le_antisymm hmem.2 hx.1)⟩, rfl⟩
  · rintro (h | h)
    · rcases h with ⟨h, rfl⟩
      rcases h with h | h
      · have hxle : x ≤ -1 := by
          by_contra hnot
          apply h.2
          exact ⟨le_of_not_ge hnot, by linarith [h.1.2]⟩
        exact ⟨Or.inl ⟨h.1.1, hxle⟩, rfl⟩
      · have hxge : 0 ≤ x := by
          by_contra hnot
          apply h.2
          exact ⟨by linarith [h.1.1], le_of_not_ge hnot⟩
        exact ⟨Or.inr ⟨hxge, h.1.2⟩, rfl⟩
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inl ⟨by norm_num, le_rfl⟩, rfl⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inr ⟨le_rfl, by norm_num⟩, rfl⟩

/-- Upper-seam symmetric-difference identity modulo its two finite overlap
endpoints. -/
theorem upperSeam_eq_symmDiff_union_endpoints :
    upperSeam =
      ((Icc (-1 : ℝ) 1 ∆ Icc (0 : ℝ) 2) ×ˢ {(1 : ℝ)}) ∪
        upperSeamEndpoints := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [upperSeam, upperSeamEndpoints, mem_prod, mem_union, mem_Icc,
    mem_singleton_iff, mem_symmDiff, mem_insert_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, rfl⟩
    rcases hx with hx | hx
    · by_cases h : x = 0
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
      · exact Or.inl ⟨Or.inl ⟨⟨hx.1, by linarith [hx.2]⟩,
          fun hmem => h (le_antisymm hx.2 hmem.1)⟩, rfl⟩
    · by_cases h : x = 1
      · exact Or.inr (Or.inr ⟨h, rfl⟩)
      · exact Or.inl ⟨Or.inr ⟨⟨by linarith [hx.1], hx.2⟩,
          fun hmem => h (le_antisymm hmem.2 hx.1)⟩, rfl⟩
  · rintro (h | h)
    · rcases h with ⟨h, rfl⟩
      rcases h with h | h
      · have hxle : x ≤ 0 := by
          by_contra hnot
          apply h.2
          exact ⟨le_of_not_ge hnot, by linarith [h.1.2]⟩
        exact ⟨Or.inl ⟨h.1.1, hxle⟩, rfl⟩
      · have hxge : 1 ≤ x := by
          by_contra hnot
          apply h.2
          exact ⟨by linarith [h.1.1], le_of_not_ge hnot⟩
        exact ⟨Or.inr ⟨hxge, h.1.2⟩, rfl⟩
    · rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inl ⟨by norm_num, le_rfl⟩, rfl⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨Or.inr ⟨le_rfl, by norm_num⟩, rfl⟩

/-- The lower-seam correction is genuinely finite. -/
theorem lowerSeamEndpoints_finite : lowerSeamEndpoints.Finite := by
  simp [lowerSeamEndpoints]

/-- The upper-seam correction is genuinely finite. -/
theorem upperSeamEndpoints_finite : upperSeamEndpoints.Finite := by
  simp [upperSeamEndpoints]

/-- The lower finite endpoint correction is `H¹`-null after passage to the
Euclidean plane. -/
theorem hausdorffMeasure_lowerSeamEndpoints :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' lowerSeamEndpoints) = 0 := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  exact (lowerSeamEndpoints_finite.image planeEuclideanHomeomorph).measure_zero μH[1]

/-- The upper finite endpoint correction is `H¹`-null. -/
theorem hausdorffMeasure_upperSeamEndpoints :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' upperSeamEndpoints) = 0 := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  exact (upperSeamEndpoints_finite.image planeEuclideanHomeomorph).measure_zero μH[1]

private theorem isCompact_lowerSeam : IsCompact lowerSeam := by
  exact (isCompact_Icc.union isCompact_Icc).prod isCompact_singleton

private theorem isCompact_upperSeam : IsCompact upperSeam := by
  exact (isCompact_Icc.union isCompact_Icc).prod isCompact_singleton

private theorem hausdorffMeasure_lowerSeam :
    (μH[1] : Measure EuclideanPlane) (planeEuclideanHomeomorph '' lowerSeam) = 2 := by
  rw [show planeEuclideanHomeomorph '' lowerSeam =
      euclideanHorizontalEmbedding (-1) ''
        (Icc (-2 : ℝ) (-1) ∪ Icc (0 : ℝ) 1) by
    ext q
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      change y = -1 at hy
      subst y
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, -1), ⟨hx, rfl⟩, rfl⟩]
  rw [(isometry_euclideanHorizontalEmbedding (-1)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 1)), hausdorffMeasure_real]
  rw [measure_union]
  · norm_num [Real.volume_Icc]
  · rw [Set.disjoint_left]
    intro x hx hz
    linarith [hx.2, hz.1]
  · exact measurableSet_Icc

private theorem hausdorffMeasure_upperSeam :
    (μH[1] : Measure EuclideanPlane) (planeEuclideanHomeomorph '' upperSeam) = 2 := by
  rw [show planeEuclideanHomeomorph '' upperSeam =
      euclideanHorizontalEmbedding 1 ''
        (Icc (-1 : ℝ) 0 ∪ Icc (1 : ℝ) 2) by
    ext q
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      change y = 1 at hy
      subst y
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, 1), ⟨hx, rfl⟩, rfl⟩]
  rw [(isometry_euclideanHorizontalEmbedding 1).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 1)), hausdorffMeasure_real]
  rw [measure_union]
  · norm_num [Real.volume_Icc]
  · rw [Set.disjoint_left]
    intro x hx hz
    linarith [hx.2, hz.1]
  · exact measurableSet_Icc

/-- The lower seam has exact weighted cost two at the actual density-one
interface, not exterior weight `lambda`. -/
theorem weightedTraceCost_two_lowerSeam : weightedTraceCost 2 lowerSeam = 2 := by
  rw [weightedTraceCost_eq_const_mul_hausdorff 2 1 isCompact_lowerSeam]
  · rw [hausdorffMeasure_lowerSeam]
    norm_num
  · rintro ⟨x, y⟩ ⟨_hx, hy⟩
    change y = -1 at hy
    subst y
    exact stripDensity_lower_interface 2 x

/-- The upper seam is independently charged at density one and also costs two. -/
theorem weightedTraceCost_two_upperSeam : weightedTraceCost 2 upperSeam = 2 := by
  rw [weightedTraceCost_eq_const_mul_hausdorff 2 1 isCompact_upperSeam]
  · rw [hausdorffMeasure_upperSeam]
    norm_num
  · rintro ⟨x, y⟩ ⟨_hx, hy⟩
    change y = 1 at hy
    subst y
    exact stripDensity_upper_interface 2 x

end ThreeBandExample
end FiniteBandRearrangement
end CMVRelaxation
