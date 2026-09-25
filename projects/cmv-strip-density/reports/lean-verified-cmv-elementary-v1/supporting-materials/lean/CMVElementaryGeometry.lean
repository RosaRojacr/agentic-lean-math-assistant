/-
Copyright (c) 2026 author. Released under Apache 2.0 license.
-/
import CMVElementary
import TypeThreeAssembly

/-!
# Literal coordinate carriers and the mandatory geometric contract

Area and perimeter below use the copied library's ambient Lebesgue integral and
complete-frontier Euclidean L2 Hausdorff measure. No boundary measure is freely
assigned, and no desired area/perimeter formula is used to define a region.

`geometric_comparison` is the primary root. Its corrected conclusion
is perimeter minus perimeter, not the area-minus-perimeter typo in both printed
Theorem 1 statements. `geometric_realization` proves both complete realization
records, including all regularity and boundary fields. The quantitative comparison
is a separate root; realization alone does not prove it.
-/

open Set MeasureTheory

noncomputable section

namespace CMVElementary

/-- Reflection in the horizontal axis, including the lower exterior cap. -/
def sigma (p : PlanePoint) : PlanePoint := (p.1, -p.2)

def K (lam h : ℝ) : Set PlanePoint :=
  {p | -1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    |p.1| ≤ D lam h / h + Real.sqrt ((1 / h) ^ 2 - p.2 ^ 2)}

def upperCap4 (lam h : ℝ) : Set PlanePoint :=
  {p | 1 ≤ p.2 ∧
    p.1 ^ 2 + (p.2 - (1 - (1 / h) * Real.cos (Real.arccos (h / lam)))) ^ 2 ≤
      (1 / h) ^ 2}

def C (lam h : ℝ) : Set PlanePoint :=
  K lam h ∪ upperCap4 lam h ∪ sigma '' upperCap4 lam h

def K3 (lam r : ℝ) : Set PlanePoint :=
  let q := 2 * r - 1
  {p | -1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    |p.1| ≤ D lam q / r + Real.sqrt ((1 / r) ^ 2 - (p.2 - (1 / r - 1)) ^ 2)}

/-- Disk intersected with `y ≥ 1`: also the major segment when `r < 1/2`. -/
def upperCap3 (lam r : ℝ) : Set PlanePoint :=
  let q := 2 * r - 1
  {p | 1 ≤ p.2 ∧
    p.1 ^ 2 + (p.2 - (1 - (1 / r) * Real.cos (Real.arccos (q / lam)))) ^ 2 ≤
      (1 / r) ^ 2}

def E (lam r : ℝ) : Set PlanePoint := K3 lam r ∪ upperCap3 lam r

/-- Exact contract type of `CMVElementary.geometric_comparison`.
Only the four-arc carrier can be instantiated at one; its competitor has `r < h`. -/
def GeometricStatement : Prop :=
  ∀ lam : ℝ, 1 < lam →
    0 < gamma lam ∧
    ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ r : ℝ, 0 < r ∧ r < h ∧
        WeightedArea lam (E lam r) = WeightedArea lam (C lam h) ∧
        gamma lam / h <
          WeightedPerimeter lam (FrontierMeasure (C lam h)) -
            WeightedPerimeter lam (FrontierMeasure (E lam r)) ∧
        0 < gamma lam / h

/-- Geometric finiteness is to be derived, not supplied by a caller. -/
structure RegionRegularity (lam : ℝ) (F : Set PlanePoint) : Prop where
  closed : IsClosed F
  bounded : Bornology.IsBounded F
  measurable : MeasurableSet F
  area_integrable : IntegrableOn (StripDensity lam) F
  perimeter_integrable : Integrable (StripDensity lam) (FrontierMeasure F)
  frontier_finite : FrontierMeasure F univ < ⊤

/-- Carrier identification and actual integral identities on the whole
four-arc domain, including `h = 1`. -/
structure FourArcRealization (lam h : ℝ) : Prop where
  candidate_bridge : ∃ candidate : FourArcCandidate lam,
    candidate.h = h ∧ candidate.alpha = Real.arccos (h / lam) ∧
      candidate.SatisfiesCMVTypeIVHypotheses ∧ C lam h = candidate.assembly.carrier
  regularity : RegionRegularity lam (C lam h)
  area_formula : WeightedArea lam (C lam h) = A4 lam h
  perimeter_formula : WeightedPerimeter lam (FrontierMeasure (C lam h)) = P4 lam h
  upper_chord_interior :
    {p : PlanePoint | p.2 = 1 ∧ |p.1| < Real.sin (Real.arccos (h / lam)) / h} ⊆
      interior (C lam h)
  lower_chord_interior :
    {p : PlanePoint | p.2 = -1 ∧ |p.1| < Real.sin (Real.arccos (h / lam)) / h} ⊆
      interior (C lam h)
  lower_cap_location : sigma '' upperCap4 lam h ⊆ {p : PlanePoint | p.2 ≤ -1}

/-- Branch-complete carrier identification. The full exposed bottom segment is
retained, including its zero-length case; it is not an internal attaching chord. -/
structure ThreeArcRealization (lam r : ℝ) : Prop where
  assembly_bridge : ∃ assembly : TypeThreeAssembly lam,
    assembly.h = r ∧ E lam r = assembly.carrier
  regularity : RegionRegularity lam (E lam r)
  area_formula : WeightedArea lam (E lam r) = A3 lam r
  perimeter_formula : WeightedPerimeter lam (FrontierMeasure (E lam r)) = P3 lam r
  angle_bounds : 0 < Real.arccos ((2 * r - 1) / lam) ∧
    Real.arccos ((2 * r - 1) / lam) < Real.pi
  major_angle : r < 1 / 2 → Real.pi / 2 < Real.arccos ((2 * r - 1) / lam)
  upper_chord_interior :
    {p : PlanePoint | p.2 = 1 ∧
      |p.1| < Real.sin (Real.arccos ((2 * r - 1) / lam)) / r} ⊆ interior (E lam r)
  bottom_frontier : frontier (E lam r) ∩ {p : PlanePoint | p.2 = -1} =
    {p : PlanePoint | p.2 = -1 ∧ |p.1| ≤ D lam (2 * r - 1) / r}
  semicircle_disk : r = 1 / 2 →
    E lam r = {p : PlanePoint | p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4}

/-- Exact contract type of `CMVElementary.geometric_realization`.
These are unconditional geometric conclusions on the specified domains; the
comparison theorem must not accept these records as extra assumptions. -/
def GeometricRealizationStatement : Prop :=
  ∀ lam : ℝ, 1 < lam →
    (∀ h : ℝ, 0 < h → h ≤ 1 → FourArcRealization lam h) ∧
    (∀ r : ℝ, 0 < r → r < 1 → ThreeArcRealization lam r)


open scoped Topology

namespace GeometryBridge

-- The corrected target is P(C)-P(E), not the printed A(C)-P(E).
theorem sine_gap (lam z : ℝ) :
    Real.sin (Real.arccos (z / lam)) - Real.sin (Real.arccos z) = D lam z := by
  simp only [Real.sin_arccos, D, div_pow]

theorem side_width {lam : ℝ} (a : TypeThreeAssembly lam) :
    a.sideHalfWidth = D lam (2 * a.h - 1) / a.h := by
  rw [TypeThreeAssembly.sideHalfWidth]
  change (1 / a.h) * (Real.sin (Real.arccos ((2 * a.h - 1) / lam)) -
    Real.sin (Real.arccos (2 * a.h - 1))) = _
  rw [sine_gap]
  ring

theorem abs_le_sqrt_iff (x s : ℝ) (hs : 0 ≤ s) :
    |x| ≤ Real.sqrt s ↔ x ^ 2 ≤ s := by
  have heq := Real.sq_sqrt hs
  constructor
  · intro hx
    have := (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg s)).2 hx
    simpa [sq_abs, heq] using this
  · intro hx
    apply (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg s)).1
    simpa [sq_abs, heq] using hx

theorem horizontal_section (x b s : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    |x| ≤ b + Real.sqrt s ↔
      (-b ≤ x ∧ x ≤ b) ∨
      ((x + b) ^ 2 ≤ s ∧ x ≤ -b) ∨
      ((x - b) ^ 2 ≤ s ∧ b ≤ x) := by
  have hn := Real.sqrt_nonneg s
  constructor
  · intro hx
    obtain ⟨hlo, hhi⟩ := abs_le.mp hx
    by_cases hl : x < -b
    · right; left
      refine ⟨(abs_le_sqrt_iff (x + b) s hs).1 ?_, hl.le⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    by_cases hr : b < x
    · right; right
      refine ⟨(abs_le_sqrt_iff (x - b) s hs).1 ?_, hr.le⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨le_of_not_gt hl, le_of_not_gt hr⟩
  · rintro (⟨hlo, hhi⟩ | ⟨hd, hl⟩ | ⟨hd, hr⟩)
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · obtain ⟨hlo, hhi⟩ := abs_le.mp ((abs_le_sqrt_iff (x + b) s hs).2 hd)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · obtain ⟨hlo, hhi⟩ := abs_le.mp ((abs_le_sqrt_iff (x - b) s hs).2 hd)
      exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem K3_core {lam : ℝ} (a : TypeThreeAssembly lam) :
    K3 lam a.h = a.coreCarrier := by
  ext p
  by_cases hy : -1 ≤ p.2 ∧ p.2 ≤ 1
  · have hs : 0 ≤ a.radius ^ 2 - (p.2 - (a.radius - 1)) ^ 2 := by
      have hab : |p.2 - (a.radius - 1)| ≤ |a.radius| := by
        rw [abs_of_pos a.radius_pos]
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, a.one_lt_radius]⟩
      have := sq_le_sq.mpr hab
      linarith
    have hsec := horizontal_section p.1 a.sideHalfWidth
      (a.radius ^ 2 - (p.2 - (a.radius - 1)) ^ 2) a.sideHalfWidth_nonneg hs
    simp only [K3, Set.mem_ofPred_eq, ← side_width a,
      hy.1, hy.2, true_and]
    change |p.1| ≤ a.sideHalfWidth +
      Real.sqrt (a.radius ^ 2 - (p.2 - (a.radius - 1)) ^ 2) ↔ _
    rw [hsec]
    simp only [TypeThreeAssembly.coreCarrier, TypeThreeAssembly.rectangleCarrier,
      TypeThreeAssembly.leftSegmentCarrier, TypeThreeAssembly.rightSegmentCarrier,
      TypeThreeAssembly.leftCenter, TypeThreeAssembly.rightCenter,
      Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, hy.1, hy.2,
      and_true, sub_neg_eq_add]
    constructor
    · rintro (hp | ⟨hd, hx⟩ | ⟨hd, hx⟩)
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr ⟨by linarith, hx⟩)
      · exact Or.inr ⟨by linarith, hx⟩
    · rintro ((hp | ⟨hd, hx⟩) | ⟨hd, hx⟩)
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨by linarith, hx⟩)
      · exact Or.inr (Or.inr ⟨by linarith, hx⟩)
  · constructor
    · intro hp
      exact (hy ⟨hp.1, hp.2.1⟩).elim
    · intro hp
      exact (hy (abs_le.mp (a.coreCarrier_y_bounds hp))).elim

theorem cap3_outer {lam : ℝ} (a : TypeThreeAssembly lam) :
    upperCap3 lam a.h = a.outerCap.carrier := by
  ext p
  simp only [OneSidedCircularCap.carrier, OneSidedCircularCap.radiusSquaredAt,
    OneSidedCircularCap.center, TypeThreeAssembly.outerCap_radius]
  change (1 ≤ p.2 ∧ _) ↔
    ((p.1 - 0) ^ 2 + (p.2 - (1 - a.radius * Real.cos a.outerAngle)) ^ 2 ≤
      a.radius ^ 2 ∧ 1 ≤ p.2)
  simp only [sub_zero]
  exact and_comm

theorem E_assembly {lam : ℝ} (a : TypeThreeAssembly lam) :
    E lam a.h = a.carrier := by
  rw [E, K3_core a, cap3_outer a]
  rfl

theorem E_half_disk (lam : ℝ) :
    E lam (1 / 2) = {p : PlanePoint | p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4} := by
  ext p
  simp only [E, K3, upperCap3, D, Set.mem_union, Set.mem_ofPred_eq]
  norm_num
  constructor
  · rintro (⟨hlo, hhi, hx⟩ | ⟨hy, hd⟩)
    · have hs : 0 ≤ 4 - (p.2 - 1) ^ 2 := by nlinarith
      have := (abs_le_sqrt_iff p.1 _ hs).1 hx
      nlinarith
    · exact hd
  · intro hd
    by_cases hy : p.2 ≤ 1
    · left
      have hlo : -1 ≤ p.2 := by nlinarith [sq_nonneg p.1]
      refine ⟨hlo, hy, ?_⟩
      apply (abs_le_sqrt_iff p.1 _ (by nlinarith [sq_nonneg p.1])).2
      nlinarith
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge hy), hd⟩

theorem half_bottom_section (lam : ℝ) :
    E lam (1 / 2) ∩ {p : PlanePoint | p.2 = -1} = {(0, -1)} := by
  rw [E_half_disk]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hd, hy⟩
    have hx : p.1 = 0 := by rw [hy] at hd; nlinarith [sq_nonneg p.1]
    exact Prod.ext hx hy
  · intro hp
    subst p
    norm_num

theorem E_bottom_section (lam r : ℝ) :
    E lam r ∩ {p : PlanePoint | p.2 = -1} =
      {p : PlanePoint | p.2 = -1 ∧ |p.1| ≤ D lam (2 * r - 1) / r} := by
  ext p
  constructor
  · rintro ⟨(hk | hc), hy⟩
    · refine ⟨hy, ?_⟩
      have hx := hk.2.2
      change |p.1| ≤ D lam (2 * r - 1) / r +
        Real.sqrt ((1 / r) ^ 2 - (p.2 - (1 / r - 1)) ^ 2) at hx
      rw [hy, show (1 / r) ^ 2 - ((-1 : ℝ) - (1 / r - 1)) ^ 2 = 0 by ring,
        Real.sqrt_zero, add_zero] at hx
      exact hx
    · have hh : 1 ≤ p.2 := hc.1
      change p.2 = -1 at hy
      linarith
  · rintro ⟨hy, hx⟩
    refine ⟨Or.inl ?_, hy⟩
    change -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ _
    rw [hy]
    refine ⟨le_rfl, by norm_num, ?_⟩
    change |p.1| ≤ D lam (2 * r - 1) / r +
      Real.sqrt ((1 / r) ^ 2 - ((-1 : ℝ) - (1 / r - 1)) ^ 2)
    simpa only [show (1 / r) ^ 2 - ((-1 : ℝ) - (1 / r - 1)) ^ 2 = 0 by ring,
      Real.sqrt_zero, add_zero] using hx

theorem E_bottom_frontier {lam : ℝ} (a : TypeThreeAssembly lam) :
    frontier (E lam a.h) ∩ {p : PlanePoint | p.2 = -1} =
      {p : PlanePoint | p.2 = -1 ∧ |p.1| ≤ D lam (2 * a.h - 1) / a.h} := by
  apply Set.Subset.antisymm
  · intro p hp
    have hclosed : IsClosed (E lam a.h) := by
      rw [E_assembly a]
      exact a.isClosed_carrier
    rw [← E_bottom_section]
    exact ⟨hclosed.frontier_subset hp.1, hp.2⟩
  · intro p hp
    rw [E_assembly a]
    refine ⟨a.bottomSegmentCarrier_subset_frontier ?_, hp.1⟩
    change p.2 = -1 ∧ |p.1| ≤ a.sideHalfWidth
    rw [side_width]
    exact hp

theorem half_bottom_frontier {lam : ℝ} (hlam : 1 < lam) :
    frontier (E lam (1 / 2)) ∩ {p : PlanePoint | p.2 = -1} = {(0, -1)} := by
  let a : TypeThreeAssembly lam := ⟨1 / 2, hlam, by norm_num, by norm_num⟩
  rw [show (1 / 2 : ℝ) = a.h from rfl, E_bottom_frontier a,
    ← E_bottom_section, show a.h = (1 / 2 : ℝ) from rfl, half_bottom_section]

theorem K_one (lam : ℝ) :
    K lam 1 = {p : PlanePoint | -1 ≤ p.2 ∧ p.2 ≤ 1 ∧
      |p.1| ≤ Real.sqrt (1 - 1 / lam ^ 2) + Real.sqrt (1 - p.2 ^ 2)} := by
  ext p
  simp [K, D]

theorem reflected_cap_below (lam h : ℝ) :
    sigma '' upperCap4 lam h ⊆ {p : PlanePoint | p.2 ≤ -1} := by
  rintro p ⟨q, hq, rfl⟩
  change -q.2 ≤ -1
  exact neg_le_neg hq.1

-- This mass bound uses the public complete-frontier decomposition and exact
-- trace measures; no modeled perimeter sum is used to infer finiteness.
theorem three_frontier_finite {lam : ℝ} (a : TypeThreeAssembly lam) :
    FrontierMeasure a.carrier Set.univ < ⊤ := by
  have hm : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure EuclideanPlane)
      (frontier (planeEuclideanHomeomorph '' a.carrier)) ≠ ⊤ := by
    rw [a.euclidean_frontier]
    apply measure_union_ne_top
    · rw [a.exact_euclidean_leftArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    apply measure_union_ne_top
    · rw [a.exact_euclidean_rightArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    apply measure_union_ne_top
    · rw [exact_euclidean_capTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    · rw [a.exact_euclidean_bottomSegmentCarrier_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
  unfold FrontierMeasure
  rw [Measure.map_apply planeEuclideanHomeomorph.symm.continuous.measurable MeasurableSet.univ]
  simpa using lt_top_iff_ne_top.mpr hm

theorem E_area {lam : ℝ} (a : TypeThreeAssembly lam) :
    WeightedArea lam (E lam a.h) = A3 lam a.h := by
  rw [E_assembly a]
  change a.WeightedArea = _
  rw [a.weightedArea_formula]
  unfold TypeThreeAssembly.scalarWeightedArea TypeThreeAssembly.angleTerm
    TypeThreeAssembly.sineGap TypeThreeAssembly.outerAngle
    TypeThreeAssembly.outerArgument TypeThreeAssembly.innerAngle
    TypeThreeAssembly.shapeParameter
  rw [sine_gap, Real.arccos_eq_pi_div_two_sub_arcsin (2 * a.h - 1)]
  unfold A3 B
  ring

theorem E_perimeter {lam : ℝ} (a : TypeThreeAssembly lam) :
    WeightedPerimeter lam (FrontierMeasure (E lam a.h)) = P3 lam a.h := by
  rw [E_assembly a]
  change a.WeightedPerimeter = _
  rw [a.weightedPerimeter_formula]
  unfold TypeThreeAssembly.scalarWeightedPerimeter TypeThreeAssembly.angleTerm
    TypeThreeAssembly.sineGap TypeThreeAssembly.outerAngle
    TypeThreeAssembly.outerArgument TypeThreeAssembly.innerAngle
    TypeThreeAssembly.shapeParameter
  rw [sine_gap, Real.arccos_eq_pi_div_two_sub_arcsin (2 * a.h - 1)]
  unfold P3 B
  ring

def fourCandidate {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    FourArcCandidate lam where
  h := h
  alpha := Real.arccos (h / lam)
  h_pos := hh
  h_le_one := h1
  alpha_pos := Real.arccos_pos.mpr ((div_lt_one (by linarith)).2 (by linarith))
  alpha_lt_pi_div_two := Real.arccos_lt_pi_div_two.mpr (div_pos hh (by linarith))

theorem fourCandidate_snell {lam : ℝ} (hlam : 1 < lam)
    (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    (fourCandidate hlam h hh h1).SatisfiesCMVTypeIVHypotheses := by
  refine ⟨hlam, ?_⟩
  change lam * Real.cos (Real.arccos (h / lam)) = h
  rw [Real.cos_arccos (by have := div_pos hh (show 0 < lam by linarith); linarith)
    ((div_le_one (by linarith)).2 (by linarith))]
  field_simp


theorem disk_bounded (cx cy R : ℝ) :
    Bornology.IsBounded {p : PlanePoint | (p.1-cx)^2 + (p.2-cy)^2 ≤ R^2} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|cx| + |cy| + |R|, ?_⟩
  intro p hp
  change (p.1-cx)^2 + (p.2-cy)^2 ≤ R^2 at hp
  have hx : |p.1-cx| ≤ |R| := sq_le_sq.mp (by nlinarith [sq_nonneg (p.2-cy)])
  have hy : |p.2-cy| ≤ |R| := sq_le_sq.mp (by nlinarith [sq_nonneg (p.1-cx)])
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  constructor
  · have := abs_add_le (p.1-cx) cx
    rw [sub_add_cancel] at this
    linarith [abs_nonneg cy]
  · have := abs_add_le (p.2-cy) cy
    rw [sub_add_cancel] at this
    linarith [abs_nonneg cx]

theorem cap_bounded (c : OneSidedCircularCap) : Bornology.IsBounded c.carrier :=
  (disk_bounded c.center.1 c.center.2 c.radius).subset (fun _ hp => hp.1)

theorem three_bounded {lam : ℝ} (a : TypeThreeAssembly lam) : Bornology.IsBounded a.carrier := by
  have hr : Bornology.IsBounded a.rectangleCarrier := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|a.sideHalfWidth| + 1, ?_⟩
    intro p hp
    have hx : |p.1| ≤ a.sideHalfWidth := abs_le.mpr hp.1
    have hy : |p.2| ≤ 1 := abs_le.mpr hp.2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
    constructor <;> linarith [le_abs_self a.sideHalfWidth, abs_nonneg a.sideHalfWidth]
  exact ((hr.union ((disk_bounded _ _ _).subset (fun _ hp => hp.1))).union
    ((disk_bounded _ _ _).subset (fun _ hp => hp.1))).union (cap_bounded a.outerCap)

theorem three_regularity {lam : ℝ} (a : TypeThreeAssembly lam) : RegionRegularity lam (E lam a.h) := by
  rw [E_assembly a]
  exact ⟨a.isClosed_carrier, three_bounded a, a.measurableSet_carrier,
    a.integrableOn_carrier, a.integrable_frontierMeasure, three_frontier_finite a⟩

-- Local geometric lemma, using only public cap definitions and identities.
theorem strict_chord_not_arc (c : OneSidedCircularCap) {p : PlanePoint}
    (hy : p.2 = c.baseY) (hx : |p.1-c.midpointX| < c.chord/2) : p ∉ c.arcTrace := by
  intro harc
  have hc : (p.1-c.midpointX)^2 + (c.radius * Real.cos c.theta)^2 = c.radius^2 := by
    cases hs : c.side <;>
      simpa [OneSidedCircularCap.arcTrace, OneSidedCircularCap.radiusSquaredAt,
        OneSidedCircularCap.center, hs, hy] using harc.1
  have ht := congrArg (fun z : ℝ => c.radius^2*z) (Real.sin_sq_add_cos_sq c.theta)
  have hr := congrArg (fun z : ℝ => z^2) c.radius_mul_sin
  have heq : |p.1-c.midpointX| = c.chord/2 := by
    rw [← sq_eq_sq₀ (abs_nonneg _) (by linarith [c.chord_pos]), sq_abs]
    nlinarith
  exact (ne_of_lt hx) heq

theorem three_top_circle {lam : ℝ} (a : TypeThreeAssembly lam) :
    (a.radius * Real.sin a.innerAngle)^2 + (2-a.radius)^2 = a.radius^2 := by
  have hc : a.radius * Real.cos a.innerAngle = 2-a.radius := by
    rw [a.cos_innerAngle, TypeThreeAssembly.shapeParameter]
    nlinarith [a.radius_mul_h]
  have ht := congrArg (fun z : ℝ => a.radius^2*z) (Real.sin_sq_add_cos_sq a.innerAngle)
  nlinarith

theorem three_strict_chord {lam : ℝ} (a : TypeThreeAssembly lam) {p : PlanePoint}
    (hy : p.2 = 1) (hx : |p.1| < a.radius * Real.sin a.outerAngle) :
    p ∈ interior a.carrier := by
  have hnot : p ∉ frontier a.carrier := by
    rw [a.frontier_carrier]
    rintro (hl | hr | hu | hb)
    · have hc := hl.1
      have hs := hl.2.1
      change p.1 ≤ -a.sideHalfWidth at hs
      simp only [TypeThreeAssembly.leftCenter, hy] at hc
      have ht := three_top_circle a
      have hw := a.sideHalfWidth
      have hwidth : a.sideHalfWidth + a.radius * Real.sin a.innerAngle =
          a.radius * Real.sin a.outerAngle := by rw [TypeThreeAssembly.sideHalfWidth]; ring
      have heq : -(p.1+a.sideHalfWidth) = a.radius * Real.sin a.innerAngle := by
        apply (sq_eq_sq₀ (by linarith) (mul_nonneg a.radius_pos.le a.innerSin_pos.le)).mp
        nlinarith
      linarith [(abs_lt.mp hx).1]
    · have hc := hr.1
      have hs := hr.2.1
      change a.sideHalfWidth ≤ p.1 at hs
      simp only [TypeThreeAssembly.rightCenter, hy] at hc
      have ht := three_top_circle a
      have hwidth : a.sideHalfWidth + a.radius * Real.sin a.innerAngle =
          a.radius * Real.sin a.outerAngle := by rw [TypeThreeAssembly.sideHalfWidth]; ring
      have heq : p.1-a.sideHalfWidth = a.radius * Real.sin a.innerAngle := by
        apply (sq_eq_sq₀ (by linarith) (mul_nonneg a.radius_pos.le a.innerSin_pos.le)).mp
        nlinarith
      linarith [(abs_lt.mp hx).2]
    · exact strict_chord_not_arc a.outerCap hy (by
        change |p.1-0| < (2*a.radius*Real.sin a.outerAngle)/2
        simp only [sub_zero]
        linarith) hu
    · have hh : p.2 = -1 := hb.1
      linarith
  have hp : p ∈ a.carrier := Or.inr (a.outerCap.chordCarrier_subset_carrier (by
    change p.2 = 1 ∧ |p.1-0| ≤ (2*a.radius*Real.sin a.outerAngle)/2
    constructor
    · exact hy
    · simp only [sub_zero]
      linarith [hx.le]))
  by_contra hn
  exact hnot ((mem_frontier_iff_notMem_interior hp).mpr hn)

theorem three_realization {lam r : ℝ} (hlam : 1 < lam) (hr : 0 < r) (hr1 : r < 1) :
    ThreeArcRealization lam r := by
  let a : TypeThreeAssembly lam := ⟨r, hlam, hr, hr1⟩
  refine ⟨⟨a, rfl, E_assembly a⟩, three_regularity a, E_area a, E_perimeter a,
    ⟨a.outerAngle_pos, a.outerAngle_lt_pi⟩, ?_, ?_, E_bottom_frontier a, ?_⟩
  · intro hm
    have hn : (2*r-1)/lam < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    have h := Real.arccos_lt_arccos (show -1 ≤ (2*r-1)/lam from a.outerArgument_mem.1.le)
      hn (show (0:ℝ) ≤ 1 by norm_num)
    simpa using h
  · intro p hp
    rw [E_assembly a]
    apply three_strict_chord a hp.1
    simpa [TypeThreeAssembly.radius, TypeThreeAssembly.outerAngle,
      TypeThreeAssembly.outerArgument, TypeThreeAssembly.shapeParameter, a, div_eq_mul_inv,
      mul_comm] using hp.2
  · intro heq
    rw [heq]
    exact E_half_disk lam


theorem offset_section (x b c s : ℝ) (hs : 0 ≤ s) (hbc : b ≤ c)
    (hc : 0 ≤ c) (hcs : c ≤ b + Real.sqrt s) :
    |x| ≤ b + Real.sqrt s ↔
      (-c ≤ x ∧ x ≤ c) ∨
      ((x+b)^2 ≤ s ∧ x ≤ -c) ∨ ((x-b)^2 ≤ s ∧ c ≤ x) := by
  constructor
  · intro hx
    obtain ⟨hlo, hhi⟩ := abs_le.mp hx
    by_cases hl : x < -c
    · right; left
      refine ⟨(abs_le_sqrt_iff (x+b) s hs).mp ?_, hl.le⟩
      exact abs_le.mpr ⟨by linarith, by linarith [Real.sqrt_nonneg s]⟩
    by_cases hr : c < x
    · right; right
      refine ⟨(abs_le_sqrt_iff (x-b) s hs).mp ?_, hr.le⟩
      exact abs_le.mpr ⟨by linarith [Real.sqrt_nonneg s], by linarith⟩
    · exact Or.inl ⟨le_of_not_gt hl, le_of_not_gt hr⟩
  · rintro (⟨hlo,hhi⟩ | ⟨hd,hl⟩ | ⟨hd,hr⟩)
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · obtain ⟨hlo,hhi⟩ := abs_le.mp ((abs_le_sqrt_iff (x+b) s hs).mpr hd)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · obtain ⟨hlo,hhi⟩ := abs_le.mp ((abs_le_sqrt_iff (x-b) s hs).mpr hd)
      exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem core_width (c : StripCore) :
    c.carrier = {p : PlanePoint | |p.2| ≤ 1 ∧
      |p.1| ≤ c.chord/2 - c.radius * Real.cos c.sideAngle +
        Real.sqrt (c.radius^2-p.2^2)} := by
  have hc : 0 ≤ c.radius * Real.cos c.sideAngle := by
    rw [c.cos_sideAngle]
    exact mul_nonneg c.radius_pos.le (Real.sqrt_nonneg _)
  have hr : c.radius * Real.sin c.sideAngle = 1 := by
    rw [c.sin_sideAngle, StripCore.radius]
    field_simp [ne_of_gt c.curvature_pos]
  have ht := congrArg (fun z : ℝ => c.radius^2*z) (Real.sin_sq_add_cos_sq c.sideAngle)
  have hb : (c.radius * Real.cos c.sideAngle)^2 = c.radius^2-1 := by
    nlinarith [sq_nonneg (c.radius * Real.cos c.sideAngle)]
  ext p
  by_cases hy : |p.2| ≤ 1
  · have hy2 : p.2^2 ≤ 1 := by nlinarith [(sq_le_sq₀ (abs_nonneg p.2) (by norm_num : (0:ℝ) ≤ 1)).mpr hy, sq_abs p.2]
    have hs : 0 ≤ c.radius^2-p.2^2 := by nlinarith [sq_nonneg (c.radius * Real.cos c.sideAngle)]
    have hcs : c.radius * Real.cos c.sideAngle ≤ Real.sqrt (c.radius^2-p.2^2) := by
      apply (sq_le_sq₀ hc (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hs, hb]
      linarith
    have he := offset_section p.1 (c.chord/2-c.radius*Real.cos c.sideAngle)
      (c.chord/2) (c.radius^2-p.2^2) hs (by linarith)
      (by linarith [c.chord_pos]) (by linarith)
    simp only [Set.mem_ofPred_eq, hy, true_and]
    rw [he]
    simp only [StripCore.carrier, StripCore.rectangleCarrier, StripCore.leftCapCarrier,
      StripCore.rightCapCarrier, StripCore.leftCenterX, StripCore.rightCenterX,
      Set.mem_union, Set.mem_ofPred_eq, hy, and_true, neg_div]
    constructor
    · rintro ((hp | ⟨hd,hx⟩) | ⟨hd,hx⟩)
      · exact Or.inl hp
      · exact Or.inr (Or.inl ⟨by nlinarith, hx⟩)
      · exact Or.inr (Or.inr ⟨by nlinarith, hx⟩)
    · rintro (hp | ⟨hd,hx⟩ | ⟨hd,hx⟩)
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr ⟨by nlinarith, hx⟩)
      · exact Or.inr ⟨by nlinarith, hx⟩
  · constructor
    · intro hp
      exact (hy (c.carrier_y_bounds hp)).elim
    · intro hp
      exact (hy hp.1).elim

theorem K_core {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    K lam h = (fourCandidate hlam h hh h1).stripCore.carrier := by
  rw [core_width]
  ext p
  simp only [K, Set.mem_ofPred_eq, FourArcCandidate.stripCore, FourArcCandidate.capChord,
    StripCore.radius, StripCore.sideAngle, fourCandidate, Real.cos_arcsin, Real.sin_arccos]
  have hw : 2 * Real.sqrt (1-(h/lam)^2)/h/2 -
      (1/h)*Real.sqrt (1-h^2) = D lam h / h := by
    unfold D
    rw [div_pow]
    ring
  rw [hw]
  simp only [abs_le]
  tauto

theorem cap4_upper {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    upperCap4 lam h = (fourCandidate hlam h hh h1).assembly.upperCap.carrier := by
  let a := fourCandidate hlam h hh h1
  have hr : a.assembly.upperCap.radius = 1/h := a.four_arcs_common_radius.1
  dsimp [a] at hr
  ext p
  simp only [OneSidedCircularCap.carrier, OneSidedCircularCap.radiusSquaredAt,
    OneSidedCircularCap.center, hr]
  change (1 ≤ p.2 ∧ _) ↔ ((p.1-0)^2 +
    (p.2-(1-(1/h)*Real.cos (Real.arccos (h/lam))))^2 ≤ (1/h)^2 ∧ 1 ≤ p.2)
  simp only [sub_zero]
  exact and_comm

theorem cap4_lower {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    sigma '' upperCap4 lam h = (fourCandidate hlam h hh h1).assembly.lowerCap.carrier := by
  let a := fourCandidate hlam h hh h1
  have hr : a.assembly.lowerCap.radius = 1/h := a.four_arcs_common_radius.2
  dsimp [a] at hr
  ext p
  simp only [OneSidedCircularCap.carrier, OneSidedCircularCap.radiusSquaredAt,
    OneSidedCircularCap.center, hr]
  change (∃ q ∈ upperCap4 lam h, sigma q = p) ↔
    ((p.1-0)^2 + (p.2-(-1+(1/h)*Real.cos (Real.arccos (h/lam))))^2 ≤ (1/h)^2 ∧ p.2 ≤ -1)
  constructor
  · rintro ⟨q,hq,rfl⟩
    change _ ≤ _ ∧ -q.2 ≤ -1
    have hd := hq.2
    change q.1^2+(q.2-(1-(1/h)*Real.cos (Real.arccos (h/lam))))^2 ≤ (1/h)^2 at hd
    dsimp [sigma]
    constructor
    · nlinarith [hd]
    · linarith [hq.1]
  · rintro ⟨hd,hy⟩
    refine ⟨sigma p, ?_, ?_⟩
    · change 1 ≤ -p.2 ∧ _
      constructor
      · linarith
      · change p.1^2+(-p.2-(1-(1/h)*Real.cos (Real.arccos (h/lam))))^2 ≤ (1/h)^2
        nlinarith [hd]
    · simp [sigma]

theorem C_assembly {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    C lam h = (fourCandidate hlam h hh h1).assembly.carrier := by
  rw [C, K_core hlam h hh h1, cap4_lower hlam h hh h1, cap4_upper hlam h hh h1]
  rfl

theorem core_bounded (c : StripCore) : Bornology.IsBounded c.carrier := by
  have hr : Bornology.IsBounded c.rectangleCarrier := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨|c.chord|/2+1, ?_⟩
    intro p hp
    have hx : |p.1| ≤ c.chord/2 := abs_le.mpr ⟨by linarith [hp.1], hp.2.1⟩
    have hy : |p.2| ≤ 1 := hp.2.2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
    constructor <;> linarith [le_abs_self c.chord, abs_nonneg c.chord]
  have hl : Bornology.IsBounded c.leftCapCarrier :=
    (disk_bounded c.leftCenterX 0 c.radius).subset (fun p hp => by
      simpa only [Set.mem_ofPred_eq, sub_zero] using hp.1)
  have hh : Bornology.IsBounded c.rightCapCarrier :=
    (disk_bounded c.rightCenterX 0 c.radius).subset (fun p hp => by
      simpa only [Set.mem_ofPred_eq, sub_zero] using hp.1)
  exact (hr.union hl).union hh

theorem four_euclidean_frontier_finite (a : FourArcAssembly) :
    (Measure.hausdorffMeasure 1 : Measure EuclideanPlane)
      (frontier (planeEuclideanHomeomorph '' a.carrier)) ≠ ⊤ := by
  rw [fourArc_euclidean_frontier]
  apply measure_union_ne_top
  · rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top
  · rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top <;>
    rw [exact_euclidean_capTrace_hausdorffMeasure] <;>
    exact ENNReal.ofReal_ne_top

theorem four_regularity (lam : ℝ) (a : FourArcAssembly) : RegionRegularity lam a.carrier := by
  refine ⟨a.isClosed_carrier,
    ((core_bounded a.core).union (cap_bounded a.upperCap)).union (cap_bounded a.lowerCap),
    a.measurableSet_carrier, ?_, ?_, ?_⟩
  · exact ((core_integrableOn lam a.core).union (cap_integrableOn lam a.upperCap)).union
      (cap_integrableOn lam a.lowerCap)
  · unfold FrontierMeasure
    rw [integrable_map_measure (measurable_stripDensity lam).aestronglyMeasurable
      planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable]
    exact euclideanStripDensity_integrableOn_of_measure_ne_top lam (four_euclidean_frontier_finite a)
  · unfold FrontierMeasure
    rw [Measure.map_apply planeEuclideanHomeomorph.symm.continuous.measurable MeasurableSet.univ]
    simpa using lt_top_iff_ne_top.mpr (four_euclidean_frontier_finite a)

theorem four_upper_chord (a : FourArcAssembly) {p : PlanePoint}
    (hy : p.2 = 1) (hx : |p.1| < a.core.chord/2) : p ∈ interior a.carrier := by
  have hnot : p ∉ frontier a.carrier := by
    rw [a.frontier_carrier]
    rintro (hl | hr | hu | hb)
    · linarith [(abs_lt.mp hx).1, hl.2.1]
    · linarith [(abs_lt.mp hx).2, hr.2.1]
    · exact strict_chord_not_arc a.upperCap hy (by simpa [FourArcAssembly.upperCap] using hx) hu
    · have hh : p.2 ≤ -1 := hb.2
      linarith
  have hp : p ∈ a.carrier := Or.inl (Or.inr (a.upperCap.chordCarrier_subset_carrier (by
    simpa [FourArcAssembly.upperCap, OneSidedCircularCap.chordCarrier] using And.intro hy hx.le)))
  by_contra hn
  exact hnot ((mem_frontier_iff_notMem_interior hp).mpr hn)

theorem four_lower_chord (a : FourArcAssembly) {p : PlanePoint}
    (hy : p.2 = -1) (hx : |p.1| < a.core.chord/2) : p ∈ interior a.carrier := by
  have hnot : p ∉ frontier a.carrier := by
    rw [a.frontier_carrier]
    rintro (hl | hr | hu | hb)
    · linarith [(abs_lt.mp hx).1, hl.2.1]
    · linarith [(abs_lt.mp hx).2, hr.2.1]
    · have hh : 1 ≤ p.2 := hu.2
      linarith
    · exact strict_chord_not_arc a.lowerCap hy (by simpa [FourArcAssembly.lowerCap] using hx) hb
  have hp : p ∈ a.carrier := Or.inr (a.lowerCap.chordCarrier_subset_carrier (by
    simpa [FourArcAssembly.lowerCap, OneSidedCircularCap.chordCarrier] using And.intro hy hx.le))
  by_contra hn
  exact hnot ((mem_frontier_iff_notMem_interior hp).mpr hn)

theorem C_area {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    WeightedArea lam (C lam h) = A4 lam h := by
  rw [C_assembly hlam h hh h1]
  let a := fourCandidate hlam h hh h1
  change a.WeightedArea = _
  rw [a.candidate_area_formula (fourCandidate_snell hlam h hh h1)]
  have hc : Real.cos a.beta = h := by
    change Real.cos (Real.pi/2-Real.arcsin h) = h
    rw [Real.cos_pi_div_two_sub, Real.sin_arcsin (by linarith) h1]
  rw [hc]
  change 4 * Real.sin (Real.arccos (h/lam))/h +
    2*(lam*Real.arccos (h/lam)-Real.sin (Real.arccos (h/lam))*h)/h^2 +
    2*(Real.arcsin h-h*Real.sqrt (1-h^2))/h^2 = _
  rw [Real.sin_arccos]
  unfold A4 B D
  rw [div_pow]
  field_simp
  ring

theorem C_perimeter {lam : ℝ} (hlam : 1 < lam) (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) :
    WeightedPerimeter lam (FrontierMeasure (C lam h)) = P4 lam h := by
  rw [C_assembly hlam h hh h1]
  let a := fourCandidate hlam h hh h1
  change a.WeightedPerimeter = _
  rw [a.candidate_perimeter_formula (fourCandidate_snell hlam h hh h1)]
  change 4*lam*Real.arccos (h/lam)/h + 4*Real.arcsin h/h = _
  unfold P4 B
  ring

theorem four_realization {lam h : ℝ} (hlam : 1 < lam) (hh : 0 < h) (h1 : h ≤ 1) :
    FourArcRealization lam h := by
  let a := fourCandidate hlam h hh h1
  refine ⟨⟨a, rfl, rfl, fourCandidate_snell hlam h hh h1, C_assembly hlam h hh h1⟩,
    ?_, C_area hlam h hh h1, C_perimeter hlam h hh h1, ?_, ?_, reflected_cap_below lam h⟩
  · rw [C_assembly hlam h hh h1]
    exact four_regularity lam a.assembly
  · intro p hp
    rw [C_assembly hlam h hh h1]
    apply four_upper_chord a.assembly hp.1
    change |p.1| < (2*Real.sin (Real.arccos (h/lam))/h)/2
    have hx := hp.2
    convert hx using 1
    ring
  · intro p hp
    rw [C_assembly hlam h hh h1]
    apply four_lower_chord a.assembly hp.1
    change |p.1| < (2*Real.sin (Real.arccos (h/lam))/h)/2
    have hx := hp.2
    convert hx using 1
    ring


end GeometryBridge

/-- Unconditional, branch-complete realization of the literal coordinate regions.
The area and perimeter fields descend from the actual integral/frontier theorems. -/
theorem geometric_realization : GeometricRealizationStatement := by
  intro lam hlam
  exact ⟨fun _ hh h1 => GeometryBridge.four_realization hlam hh h1,
    fun _ hr hr1 => GeometryBridge.three_realization hlam hr hr1⟩

/-- Corrected quantitative comparison for the literal closed carriers.
The scalar witness lies strictly below one, even when the four-arc parameter is
one; both measure identities come from unconditional geometric realizations. -/
theorem geometric_comparison : GeometricStatement := by
  intro lam hlam
  obtain ⟨hgamma, hscalar⟩ := scalar_comparison lam hlam
  refine ⟨hgamma, ?_⟩
  intro h hh h1
  obtain ⟨r, hr, hrh, harea, hperimeter, hmargin⟩ := hscalar h hh h1
  have hr1 : r < 1 := hrh.trans_le h1
  have hfour := (geometric_realization lam hlam).1 h hh h1
  have hthree := (geometric_realization lam hlam).2 r hr hr1
  refine ⟨r, hr, hrh, ?_, ?_, hmargin⟩
  · rw [hthree.area_formula, hfour.area_formula]
    exact harea
  · rw [hfour.perimeter_formula, hthree.perimeter_formula]
    exact hperimeter

end CMVElementary
