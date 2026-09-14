/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryGlobalTransition

/-!
# Nonconvex step-polygon specimen for the local boundary atlas

The specimen is the literal open L-shaped polygon.  Its horizontal sections
have a jump at the shelf height.  The reentrant corner is retained, rather than
rounded or omitted.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace StepPolygon

open CMVRelaxation

/-- The lower horizontal arm of the open L-shaped polygon. -/
def lowerArm : Set PlanePoint := Ioo 0 2 ×ˢ Ioo 0 1

/-- The left vertical arm of the open L-shaped polygon. -/
def leftArm : Set PlanePoint := Ioo 0 1 ×ˢ Ioo 0 2

/-- A literal bounded nonconvex step-shaped open polygon. -/
def carrier : Set PlanePoint := lowerArm ∪ leftArm

@[simp] theorem mem_lowerArm (p : PlanePoint) :
    p ∈ lowerArm ↔ 0 < p.1 ∧ p.1 < 2 ∧ 0 < p.2 ∧ p.2 < 1 := by
  simp [lowerArm, and_assoc]

@[simp] theorem mem_leftArm (p : PlanePoint) :
    p ∈ leftArm ↔ 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 2 := by
  simp [leftArm, and_assoc]

@[simp] theorem mem_carrier (p : PlanePoint) :
    p ∈ carrier ↔
      (0 < p.1 ∧ p.1 < 2 ∧ 0 < p.2 ∧ p.2 < 1) ∨
      (0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 2) := by
  simp [carrier]

/-- Openness is derived from the two literal open rectangles. -/
theorem isOpen_carrier : IsOpen carrier := by
  exact (isOpen_Ioo.prod isOpen_Ioo).union (isOpen_Ioo.prod isOpen_Ioo)

/-- The polygon is nonempty. -/
theorem carrier_nonempty : carrier.Nonempty := by
  exact ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), by norm_num⟩

/-- The literal polygon lies in a fixed compact square. -/
theorem carrier_subset_square : carrier ⊆ Icc 0 2 ×ˢ Icc 0 2 := by
  intro p hp
  rcases hp with hp | hp
  · exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le.trans (by norm_num)⟩⟩
  · exact ⟨⟨hp.1.1.le, hp.1.2.le.trans (by norm_num)⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

/-- Boundedness follows from the fixed square, not from an assumed polygon
trace. -/
theorem isBounded_carrier : Bornology.IsBounded carrier :=
  (isCompact_Icc.prod isCompact_Icc).isBounded.subset carrier_subset_square

/-- The two open arms overlap in an actual open square, so the polygon is
connected. -/
theorem isConnected_carrier : IsConnected carrier := by
  have hlower : IsConnected lowerArm :=
    (isConnected_Ioo (by norm_num) : IsConnected (Ioo (0 : ℝ) 2)).prod
      (isConnected_Ioo (by norm_num) : IsConnected (Ioo (0 : ℝ) 1))
  have hleft : IsConnected leftArm :=
    (isConnected_Ioo (by norm_num) : IsConnected (Ioo (0 : ℝ) 1)).prod
      (isConnected_Ioo (by norm_num) : IsConnected (Ioo (0 : ℝ) 2))
  have hinter : (lowerArm ∩ leftArm).Nonempty := by
    exact ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), by norm_num [lowerArm, leftArm]⟩
  exact hlower.union hinter hleft

/-- Below the shelf, the section is the full width-two interval. -/
theorem horizontalSection_eq_wide {y : ℝ} (hy : y ∈ Ioo 0 1) :
    CMVSourceClassification.horizontalSection carrier y = Ioo 0 2 := by
  ext x
  simp only [CMVSourceClassification.horizontalSection, mem_carrier, mem_Ioo,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.1, h.2.1.trans (by norm_num)⟩
  · intro hx
    exact Or.inl ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- At and above the shelf, while below height two, the section is the
width-one interval. -/
theorem horizontalSection_eq_narrow {y : ℝ}
    (hy0 : 0 < y) (hy1 : 1 ≤ y) (hy2 : y < 2) :
    CMVSourceClassification.horizontalSection carrier y = Ioo 0 1 := by
  ext x
  simp only [CMVSourceClassification.horizontalSection, mem_carrier, mem_Ioo,
    Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact False.elim ((not_lt_of_ge hy1) h.2.2.2)
    · exact ⟨h.1, h.2.1⟩
  · intro hx
    exact Or.inr ⟨hx.1, hx.2, hy0, hy2⟩

/-- Outside the two active height ranges, the section is empty. -/
theorem horizontalSection_eq_empty {y : ℝ} (hy : y ≤ 0 ∨ 2 ≤ y) :
    CMVSourceClassification.horizontalSection carrier y = ∅ := by
  ext x
  simp only [CMVSourceClassification.horizontalSection, mem_carrier,
    Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro (h | h)
  · rcases hy with hy | hy
    · exact (not_lt_of_ge hy) h.2.2.1
    · exact (not_lt_of_ge hy) (h.2.2.2.trans (by norm_num))
  · rcases hy with hy | hy
    · exact (not_lt_of_ge hy) h.2.2.1
    · exact (not_lt_of_ge hy) h.2.2.2

/-- Every literal horizontal section is empty or an open interval, including
the discontinuous shelf height `y = 1`. -/
theorem horizontalSection_empty_or_Ioo (y : ℝ) :
    CMVSourceClassification.horizontalSection carrier y = ∅ ∨
      (∃ a b : ℝ, a < b ∧
        CMVSourceClassification.horizontalSection carrier y = Ioo a b) := by
  by_cases hy0 : y ≤ 0
  · exact Or.inl (horizontalSection_eq_empty (Or.inl hy0))
  by_cases hy2 : 2 ≤ y
  · exact Or.inl (horizontalSection_eq_empty (Or.inr hy2))
  have hy0' : 0 < y := lt_of_not_ge hy0
  have hy2' : y < 2 := lt_of_not_ge hy2
  by_cases hy1 : y < 1
  · exact Or.inr ⟨0, 2, by norm_num,
      horizontalSection_eq_wide ⟨hy0', hy1⟩⟩
  · exact Or.inr ⟨0, 1, by norm_num,
      horizontalSection_eq_narrow hy0' (le_of_not_gt hy1) hy2'⟩

/-- The required AE interval-section premise is derived from the literal set;
in fact the conclusion holds at every height. -/
theorem hasAEIntervalHorizontalSections :
    CMVRelaxation.HasAEIntervalHorizontalSections carrier := by
  filter_upwards [] with y
  rcases horizontalSection_empty_or_Ioo y with hempty | ⟨a, b, hab, hsection⟩
  · exact ⟨∅, ordConnected_empty,
      Filter.Eventually.of_forall (fun _ => by rw [hempty])⟩
  · exact ⟨Ioo a b, ordConnected_Ioo, Filter.Eventually.of_forall
      (fun x => by rw [hsection])⟩

/-- A global homeomorphism flattening a positive quadrant (or its complement)
to a strict upper (or lower) half-plane.  Its second coordinate is `min x y`. -/
def quadrantFlatten : PlanePoint ≃ₜ PlanePoint where
  toFun p := (p.1 - p.2, min p.1 p.2)
  invFun q := (q.2 + max q.1 0, q.2 + max (-q.1) 0)
  left_inv := by
    intro p
    rcases le_total p.1 p.2 with hxy | hyx
    · have hu : p.1 - p.2 ≤ 0 := sub_nonpos.mpr hxy
      have hneg : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hxy
      apply Prod.ext
      · simp [min_eq_left hxy, max_eq_right hu]
      · simp [min_eq_left hxy, max_eq_left hneg]
    · have hu : 0 ≤ p.1 - p.2 := sub_nonneg.mpr hyx
      have hneg : p.2 - p.1 ≤ 0 := sub_nonpos.mpr hyx
      apply Prod.ext
      · simp [min_eq_right hyx, max_eq_left hu]
      · simp [min_eq_right hyx, max_eq_right hneg]
  right_inv := by
    intro q
    rcases le_total q.1 0 with hu | hu
    · have hneg : 0 ≤ -q.1 := neg_nonneg.mpr hu
      have hmin : q.2 ≤ q.2 - q.1 := by linarith
      apply Prod.ext
      · simp [max_eq_right hu, max_eq_left hneg]
      · simp [max_eq_right hu, max_eq_left hneg]
        exact hu
    · have hneg : -q.1 ≤ 0 := neg_nonpos.mpr hu
      have hmin : q.2 ≤ q.2 + q.1 := by linarith
      apply Prod.ext
      · simp [max_eq_left hu, max_eq_right hneg]
      · simp [max_eq_left hu, max_eq_right hneg, min_eq_right hmin]
  continuous_toFun :=
    (continuous_fst.sub continuous_snd).prodMk (continuous_fst.min continuous_snd)
  continuous_invFun :=
    (continuous_snd.add (continuous_fst.max continuous_const)).prodMk
      (continuous_snd.add (continuous_fst.neg.max continuous_const))


/-- Closure of the literal two-rectangle union. -/
theorem closure_carrier :
    closure carrier =
      (Icc 0 2 ×ˢ Icc 0 1) ∪ (Icc 0 1 ×ˢ Icc 0 2) := by
  rw [carrier, closure_union, lowerArm, leftArm, closure_prod_eq,
    closure_prod_eq]
  norm_num

/-- The six closed sides of the L-shaped polygon, including the horizontal
shelf and its reentrant endpoint. -/
def boundary : Set PlanePoint :=
  {p |
    (p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2) ∨
    (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 2) ∨
    (p.1 = 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 2) ∨
    (1 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 = 1) ∨
    (p.1 = 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) ∨
    (0 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 = 0)}

/-- The displayed six sides are exactly the complete topological frontier of
the set, not a supplied polygon trace. -/
theorem frontier_carrier : frontier carrier = boundary := by
  rw [isOpen_carrier.frontier_eq, closure_carrier]
  ext p
  simp only [boundary, Set.mem_sdiff, mem_union, mem_prod, mem_Icc, mem_carrier,
    mem_ofPred_eq]
  constructor
  · rintro ⟨hA | hB, hnot⟩
    · rcases hA with ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
      by_cases hx0 : p.1 = 0
      · exact Or.inl ⟨hx0, hylo, hyhi.trans (by norm_num)⟩
      by_cases hy0 : p.2 = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hxlo, hxhi, hy0⟩))))
      by_cases hx2 : p.1 = 2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hx2, hylo, hyhi⟩))))
      by_cases hy1 : p.2 = 1
      · have hx1 : 1 ≤ p.1 := by
          by_contra hx
          apply hnot
          right
          exact ⟨lt_of_le_of_ne hxlo (Ne.symm hx0), lt_of_not_ge hx,
            lt_of_le_of_ne hylo (Ne.symm hy0), by linarith⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx1, hxhi, hy1⟩)))
      exfalso
      apply hnot
      left
      exact ⟨lt_of_le_of_ne hxlo (Ne.symm hx0), lt_of_le_of_ne hxhi hx2,
        lt_of_le_of_ne hylo (Ne.symm hy0), lt_of_le_of_ne hyhi hy1⟩
    · rcases hB with ⟨⟨hxlo, hxhi⟩, hylo, hyhi⟩
      by_cases hx0 : p.1 = 0
      · exact Or.inl ⟨hx0, hylo, hyhi⟩
      by_cases hy0 : p.2 = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hxlo, hxhi.trans (by norm_num), hy0⟩))))
      by_cases hy2 : p.2 = 2
      · exact Or.inr (Or.inl ⟨hxlo, hxhi, hy2⟩)
      by_cases hx1 : p.1 = 1
      · have hy1 : 1 ≤ p.2 := by
          by_contra hy
          apply hnot
          left
          exact ⟨lt_of_le_of_ne hxlo (Ne.symm hx0), by linarith,
            lt_of_le_of_ne hylo (Ne.symm hy0), lt_of_not_ge hy⟩
        exact Or.inr (Or.inr (Or.inl ⟨hx1, hy1, hyhi⟩))
      exfalso
      apply hnot
      right
      exact ⟨lt_of_le_of_ne hxlo (Ne.symm hx0), lt_of_le_of_ne hxhi hx1,
        lt_of_le_of_ne hylo (Ne.symm hy0), lt_of_le_of_ne hyhi hy2⟩
  · intro h
    rcases h with hleft | htop | hinnerVertical | hshelf | hright | hbottom
    · refine ⟨?_, ?_⟩
      · right
        exact ⟨⟨by linarith [hleft.1], by linarith [hleft.1]⟩,
          by linarith [hleft.2.1], by linarith [hleft.2.2]⟩
      · rintro (hc | hc) <;> linarith
    · refine ⟨?_, ?_⟩
      · right
        exact ⟨⟨by linarith [htop.1], by linarith [htop.2.1]⟩,
          by linarith [htop.2.2], by linarith [htop.2.2]⟩
      · rintro (hc | hc) <;> linarith
    · refine ⟨?_, ?_⟩
      · right
        exact ⟨⟨by linarith [hinnerVertical.1], by linarith [hinnerVertical.1]⟩,
          by linarith [hinnerVertical.2.1], by linarith [hinnerVertical.2.2]⟩
      · rintro (hc | hc) <;> linarith
    · refine ⟨?_, ?_⟩
      · left
        exact ⟨⟨by linarith [hshelf.1], by linarith [hshelf.2.1]⟩,
          by linarith [hshelf.2.2], by linarith [hshelf.2.2]⟩
      · rintro (hc | hc) <;> linarith
    · refine ⟨?_, ?_⟩
      · left
        exact ⟨⟨by linarith [hright.1], by linarith [hright.1]⟩,
          by linarith [hright.2.1], by linarith [hright.2.2]⟩
      · rintro (hc | hc) <;> linarith
    · refine ⟨?_, ?_⟩
      · left
        exact ⟨⟨by linarith [hbottom.1], by linarith [hbottom.2.1]⟩,
          by linarith [hbottom.2.2], by linarith [hbottom.2.2]⟩
      · rintro (hc | hc) <;> linarith

private theorem boundary_not_mem_interior_closure {p : PlanePoint}
    (hp : p ∈ boundary) :
    p ∉ interior (closure carrier) := by
  intro hpInterior
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior p hpInterior
  rw [closure_carrier] at hball
  change
    (p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2) ∨
      (0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 2) ∨
      (p.1 = 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 2) ∨
      (1 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 = 1) ∨
      (p.1 = 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) ∨
      (0 ≤ p.1 ∧ p.1 ≤ 2 ∧ p.2 = 0) at hp
  rcases hp with hleft | htop | hinnerVertical | hshelf | hright | hbottom
  · have hqBall :
        ((p.1 - r / 2, p.2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith
  · have hqBall :
        ((p.1, p.2 + r / 2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith
  · have hqBall :
        ((p.1 + r / 2, p.2 + r / 2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith
  · have hqBall :
        ((p.1 + r / 2, p.2 + r / 2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith
  · have hqBall :
        ((p.1 + r / 2, p.2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith
  · have hqBall :
        ((p.1, p.2 - r / 2) : PlanePoint) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    have hq := interior_subset (hball hqBall)
    simp only [mem_union, mem_prod, mem_Icc] at hq
    rcases hq with hq | hq <;> linarith

/-- The L shape is regular open.  This is proved from the six derived
frontier pieces; no regularity is postulated in the specimen. -/
theorem interior_closure_carrier :
    interior (closure carrier) = carrier := by
  apply Subset.antisymm
  · intro p hp
    by_contra hnot
    have hpFrontier : p ∈ frontier carrier := by
      rw [isOpen_carrier.frontier_eq]
      exact ⟨interior_subset hp, hnot⟩
    apply boundary_not_mem_interior_closure
      (by simpa only [frontier_carrier] using hpFrontier)
    exact hp
  · exact interior_maximal subset_closure isOpen_carrier

/-- The canonical almost-everywhere open selector fixes this literal
specimen exactly. -/
theorem aeOpenRepresentative_carrier :
    aeOpenRepresentative carrier = carrier := by
  apply Subset.antisymm
  · have hsubset :
        aeOpenRepresentative carrier ⊆ interior (closure carrier) :=
      interior_maximal (aeOpenRepresentative_subset_closure_self carrier)
        (isOpen_aeOpenRepresentative carrier)
    simpa only [interior_closure_carrier] using hsubset
  · exact open_subset_aeOpenRepresentative_self isOpen_carrier

/-- The shelf is a genuine boundary interval of the selected representative. -/
theorem shelf_subset_selected_frontier :
    Icc (1 : ℝ) 2 ×ˢ {1} ⊆
      frontier (aeOpenRepresentative carrier) := by
  rw [aeOpenRepresentative_carrier, frontier_carrier]
  intro p hp
  exact Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hp.1.1, hp.1.2, hp.2⟩)))
@[simp] theorem quadrantFlatten_apply (p : PlanePoint) :
    quadrantFlatten p = (p.1 - p.2, min p.1 p.2) := by
  rfl

/-- The flattening map sends the open positive quadrant to the upper model. -/
theorem quadrantFlatten_mem_upper_iff (p : PlanePoint) :
    quadrantFlatten p ∈ OccupiedHalfPlane.upper.carrier ↔
      0 < p.1 ∧ 0 < p.2 := by
  simp [OccupiedHalfPlane.carrier]

/-- The same map sends the complement-side reentrant sector to the lower
model. -/
theorem quadrantFlatten_mem_lower_iff (p : PlanePoint) :
    quadrantFlatten p ∈ OccupiedHalfPlane.lower.carrier ↔
      p.1 < 0 ∨ p.2 < 0 := by
  simp [OccupiedHalfPlane.carrier]

/-- Signed coordinate frames needed by the six axis-aligned sides. -/
inductive Frame where
  | identity
  | reflectFirst
  | reflectSecond
  | reflectBoth
  | swap
  | clockwise

namespace Frame

def apply : Frame → PlanePoint → PlanePoint
  | .identity, q => q
  | .reflectFirst, q => (-q.1, q.2)
  | .reflectSecond, q => (q.1, -q.2)
  | .reflectBoth, q => (-q.1, -q.2)
  | .swap, q => (q.2, q.1)
  | .clockwise, q => (q.2, -q.1)

def inverse : Frame → PlanePoint → PlanePoint
  | .identity, q => q
  | .reflectFirst, q => (-q.1, q.2)
  | .reflectSecond, q => (q.1, -q.2)
  | .reflectBoth, q => (-q.1, -q.2)
  | .swap, q => (q.2, q.1)
  | .clockwise, q => (-q.2, q.1)

end Frame

/-- Translation to a boundary basepoint followed by a signed coordinate
frame. -/
def frameCoordinate (frame : Frame) (c : PlanePoint) :
    PlanePoint ≃ₜ PlanePoint where
  toFun q := frame.apply (q.1 - c.1, q.2 - c.2)
  invFun q :=
    let v := frame.inverse q
    (c.1 + v.1, c.2 + v.2)
  left_inv := by
    intro q
    cases frame <;> apply Prod.ext <;>
      simp [Frame.apply, Frame.inverse]
  right_inv := by
    intro q
    cases frame <;> apply Prod.ext <;>
      simp [Frame.apply, Frame.inverse]
  continuous_toFun := by
    cases frame <;>
      simp only [Frame.apply] <;>
      fun_prop
  continuous_invFun := by
    cases frame <;>
      simp only [Frame.inverse] <;>
      fun_prop

@[simp] theorem frameCoordinate_apply (frame : Frame) (c q : PlanePoint) :
    frameCoordinate frame c q =
      frame.apply (q.1 - c.1, q.2 - c.2) := by
  rfl

@[simp] theorem frameCoordinate_base (frame : Frame) (c : PlanePoint) :
    frameCoordinate frame c c = (0, 0) := by
  cases frame <;> simp [Frame.apply]

/-- The displayed carrier is genuinely nonconvex. -/
theorem not_convex_carrier : ¬ Convex ℝ carrier := by
  intro hconvex
  have ha : ((3 / 2, 1 / 2) : PlanePoint) ∈ carrier := by
    norm_num [carrier, lowerArm, leftArm]
  have hb : ((1 / 2, 3 / 2) : PlanePoint) ∈ carrier := by
    norm_num [carrier, lowerArm, leftArm]
  have hm := hconvex.lineMap_mem ha hb
    (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
  norm_num [AffineMap.lineMap_apply_module, carrier, lowerArm, leftArm] at hm

private theorem local_bottom {q : PlanePoint}
    (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ Ioo (-1) 1) :
    0 < q.2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx0, hx2⟩, _hyNeg, hy1⟩
  constructor
  · intro hy0
    exact (mem_carrier q).2 (Or.inl ⟨hx0, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact hqLower.2.2.1
    · exact hqLeft.2.2.1

private theorem local_right {q : PlanePoint}
    (hq : q ∈ Ioo (1 : ℝ) 3 ×ˢ Ioo 0 1) :
    q.1 < 2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx1, _hx3⟩, hy0, hy1⟩
  constructor
  · intro hx2
    exact (mem_carrier q).2 (Or.inl ⟨by linarith, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact hqLower.2.1
    · linarith [hqLeft.2.1]

private theorem local_shelf {q : PlanePoint}
    (hq : q ∈ Ioo (1 : ℝ) 2 ×ˢ Ioo 0 2) :
    q.2 < 1 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx1, hx2⟩, hy0, _hy2⟩
  constructor
  · intro hy1
    exact (mem_carrier q).2 (Or.inl ⟨by linarith, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact hqLower.2.2.2
    · linarith [hqLeft.2.1]

private theorem local_innerVertical {q : PlanePoint}
    (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ Ioo 1 2) :
    q.1 < 1 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx0, _hx2⟩, hy1, hy2⟩
  constructor
  · intro hx1
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, by linarith, hy2⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · linarith [hqLower.2.2.2]
    · exact hqLeft.2.1

private theorem local_top {q : PlanePoint}
    (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo 1 3) :
    q.2 < 2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx0, hx1⟩, hy1, _hy3⟩
  constructor
  · intro hy2
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, by linarith, hy2⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · linarith [hqLower.2.2.2]
    · exact hqLeft.2.2.2

private theorem local_left {q : PlanePoint}
    (hq : q ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 2) :
    0 < q.1 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨_hxNeg, hx1⟩, hy0, hy2⟩
  constructor
  · intro hx0
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, hy0, hy2⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact hqLower.1
    · exact hqLeft.1

private theorem local_lowerLeftCorner {q : PlanePoint}
    (hq : q ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1) 1) :
    0 < q.1 ∧ 0 < q.2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨_hxNeg, hx1⟩, _hyNeg, hy1⟩
  constructor
  · rintro ⟨hx0, hy0⟩
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, hy0, by linarith⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact ⟨hqLower.1, hqLower.2.2.1⟩
    · exact ⟨hqLeft.1, hqLeft.2.2.1⟩

private theorem local_lowerRightCorner {q : PlanePoint}
    (hq : q ∈ Ioo (1 : ℝ) 3 ×ˢ Ioo (-1) 1) :
    q.1 < 2 ∧ 0 < q.2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx1, _hx3⟩, _hyNeg, hy1⟩
  constructor
  · rintro ⟨hx2, hy0⟩
    exact (mem_carrier q).2 (Or.inl ⟨by linarith, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact ⟨hqLower.2.1, hqLower.2.2.1⟩
    · linarith [hqLeft.2.1]

private theorem local_upperRightCorner {q : PlanePoint}
    (hq : q ∈ Ioo (1 : ℝ) 3 ×ˢ Ioo 0 2) :
    q.1 < 2 ∧ q.2 < 1 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx1, _hx3⟩, hy0, _hy2⟩
  constructor
  · rintro ⟨hx2, hy1⟩
    exact (mem_carrier q).2 (Or.inl ⟨by linarith, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact ⟨hqLower.2.1, hqLower.2.2.2⟩
    · linarith [hqLeft.2.1]

private theorem local_reentrantCorner {q : PlanePoint}
    (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ Ioo 0 2) :
    q.1 < 1 ∨ q.2 < 1 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx0, hx2⟩, hy0, hy2⟩
  constructor
  · rintro (hx1 | hy1)
    · exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, hy0, hy2⟩)
    · exact (mem_carrier q).2 (Or.inl ⟨hx0, hx2, hy0, hy1⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · exact Or.inr hqLower.2.2.2
    · exact Or.inl hqLeft.2.1

private theorem local_upperInnerCorner {q : PlanePoint}
    (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ Ioo 1 3) :
    q.1 < 1 ∧ q.2 < 2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨hx0, _hx2⟩, hy1, _hy3⟩
  constructor
  · rintro ⟨hx1, hy2⟩
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, by linarith, hy2⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · linarith [hqLower.2.2.2]
    · exact ⟨hqLeft.2.1, hqLeft.2.2.2⟩

private theorem local_upperLeftCorner {q : PlanePoint}
    (hq : q ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo 1 3) :
    0 < q.1 ∧ q.2 < 2 ↔ q ∈ carrier := by
  rcases hq with ⟨⟨_hxNeg, hx1⟩, hy1, _hy3⟩
  constructor
  · rintro ⟨hx0, hy2⟩
    exact (mem_carrier q).2 (Or.inr ⟨hx0, hx1, by linarith, hy2⟩)
  · intro hqCarrier
    rcases (mem_carrier q).1 hqCarrier with hqLower | hqLeft
    · linarith [hqLower.2.2.2]
    · exact ⟨hqLeft.1, hqLeft.2.2.2⟩

private noncomputable def lowerLeftCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 0) (hy : p.1.2 = 0) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    ((frameCoordinate .identity p.1).trans quadrantFlatten)
    (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1) 1)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by simp [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .identity p.1 q) ∈
            OccupiedHalfPlane.upper.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_upper_iff]
      simpa [Frame.apply, hx, hy] using local_lowerLeftCorner hq)

private noncomputable def bottomChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx0 : 0 < p.1.1) (hx2 : p.1.1 < 2) (hy : p.1.2 = 0) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .identity p.1)
    (Ioo (0 : ℝ) 2 ×ˢ Ioo (-1) 1)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨⟨hx0, hx2⟩, by simp [hy]⟩)
    (frameCoordinate_base .identity p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hy] using
        local_bottom hq)

private noncomputable def lowerRightCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 2) (hy : p.1.2 = 0) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    ((frameCoordinate .reflectFirst p.1).trans quadrantFlatten)
    (Ioo (1 : ℝ) 3 ×ˢ Ioo (-1) 1)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by norm_num [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .reflectFirst p.1 q) ∈
            OccupiedHalfPlane.upper.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_upper_iff]
      simpa [Frame.apply, hx, hy] using local_lowerRightCorner hq)

private noncomputable def rightChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 2) (hy0 : 0 < p.1.2) (hy1 : p.1.2 < 1) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .clockwise p.1)
    (Ioo (1 : ℝ) 3 ×ˢ Ioo 0 1)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨by norm_num [hx], ⟨hy0, hy1⟩⟩)
    (frameCoordinate_base .clockwise p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hx] using
        local_right hq)

private noncomputable def upperRightCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 2) (hy : p.1.2 = 1) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    ((frameCoordinate .reflectBoth p.1).trans quadrantFlatten)
    (Ioo (1 : ℝ) 3 ×ˢ Ioo 0 2)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by norm_num [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .reflectBoth p.1 q) ∈
            OccupiedHalfPlane.upper.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_upper_iff]
      simpa [Frame.apply, hx, hy] using local_upperRightCorner hq)

private noncomputable def shelfChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx1 : 1 < p.1.1) (hx2 : p.1.1 < 2) (hy : p.1.2 = 1) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .reflectSecond p.1)
    (Ioo (1 : ℝ) 2 ×ˢ Ioo 0 2)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨⟨hx1, hx2⟩, by simp [hy]⟩)
    (frameCoordinate_base .reflectSecond p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hy] using
        local_shelf hq)

private noncomputable def reentrantCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 1) (hy : p.1.2 = 1) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .lower
    ((frameCoordinate .identity p.1).trans quadrantFlatten)
    (Ioo (0 : ℝ) 2 ×ˢ Ioo 0 2)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by simp [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .identity p.1 q) ∈
            OccupiedHalfPlane.lower.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_lower_iff]
      simpa [Frame.apply, hx, hy] using local_reentrantCorner hq)

private noncomputable def innerVerticalChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 1) (hy1 : 1 < p.1.2) (hy2 : p.1.2 < 2) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .clockwise p.1)
    (Ioo (0 : ℝ) 2 ×ˢ Ioo 1 2)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨by simp [hx], ⟨hy1, hy2⟩⟩)
    (frameCoordinate_base .clockwise p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hx] using
        local_innerVertical hq)

private noncomputable def upperInnerCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 1) (hy : p.1.2 = 2) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    ((frameCoordinate .reflectBoth p.1).trans quadrantFlatten)
    (Ioo (0 : ℝ) 2 ×ˢ Ioo 1 3)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by norm_num [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .reflectBoth p.1 q) ∈
            OccupiedHalfPlane.upper.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_upper_iff]
      simpa [Frame.apply, hx, hy] using local_upperInnerCorner hq)

private noncomputable def topChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx0 : 0 < p.1.1) (hx1 : p.1.1 < 1) (hy : p.1.2 = 2) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .reflectSecond p.1)
    (Ioo (0 : ℝ) 1 ×ˢ Ioo 1 3)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨⟨hx0, hx1⟩, by norm_num [hy]⟩)
    (frameCoordinate_base .reflectSecond p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hy] using
        local_top hq)

private noncomputable def upperLeftCornerChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 0) (hy : p.1.2 = 2) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    ((frameCoordinate .reflectSecond p.1).trans quadrantFlatten)
    (Ioo (-1 : ℝ) 1 ×ˢ Ioo 1 3)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by norm_num [hx, hy])
    (by simp [Frame.apply])
    (by
      intro q hq
      change
        quadrantFlatten (frameCoordinate .reflectSecond p.1 q) ∈
            OccupiedHalfPlane.upper.carrier ↔ q ∈ carrier
      rw [quadrantFlatten_mem_upper_iff]
      simpa [Frame.apply, hx, hy] using local_upperLeftCorner hq)

private noncomputable def leftChart
    (p : {q : PlanePoint // q ∈ frontier carrier})
    (hx : p.1.1 = 0) (hy0 : 0 < p.1.2) (hy2 : p.1.2 < 2) :
    PointwiseHalfSpaceChart carrier p :=
  PointwiseHalfSpaceChart.ofHomeomorph .upper
    (frameCoordinate .swap p.1)
    (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 2)
    (isOpen_Ioo.prod isOpen_Ioo)
    (by exact ⟨by simp [hx], ⟨hy0, hy2⟩⟩)
    (frameCoordinate_base .swap p.1)
    (by
      intro q hq
      simpa [OccupiedHalfPlane.carrier, Frame.apply, hx] using
        local_left hq)

/-- A pointwise ambient half-space chart exists at every point of the complete,
derived frontier.  The reentrant corner receives the lower-side orientation;
all convex corners and open sides receive the upper-side orientation. -/
private theorem pointwiseChart_nonempty
    (p : {q : PlanePoint // q ∈ frontier carrier}) :
    Nonempty (PointwiseHalfSpaceChart carrier p) := by
  have hp : p.1 ∈ boundary := by
    rw [← frontier_carrier]
    exact p.property
  change
    (p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ p.1.2 ≤ 2) ∨
      (0 ≤ p.1.1 ∧ p.1.1 ≤ 1 ∧ p.1.2 = 2) ∨
      (p.1.1 = 1 ∧ 1 ≤ p.1.2 ∧ p.1.2 ≤ 2) ∨
      (1 ≤ p.1.1 ∧ p.1.1 ≤ 2 ∧ p.1.2 = 1) ∨
      (p.1.1 = 2 ∧ 0 ≤ p.1.2 ∧ p.1.2 ≤ 1) ∨
      (0 ≤ p.1.1 ∧ p.1.1 ≤ 2 ∧ p.1.2 = 0) at hp
  rcases hp with hleft | htop | hinnerVertical | hshelf | hright | hbottom
  · rcases hleft with ⟨hx, hy0, hy2⟩
    by_cases hyZero : p.1.2 = 0
    · exact ⟨lowerLeftCornerChart p hx hyZero⟩
    by_cases hyTwo : p.1.2 = 2
    · exact ⟨upperLeftCornerChart p hx hyTwo⟩
    exact ⟨leftChart p hx
      (lt_of_le_of_ne hy0 (Ne.symm hyZero))
      (lt_of_le_of_ne hy2 hyTwo)⟩
  · rcases htop with ⟨hx0, hx1, hy⟩
    by_cases hxZero : p.1.1 = 0
    · exact ⟨upperLeftCornerChart p hxZero hy⟩
    by_cases hxOne : p.1.1 = 1
    · exact ⟨upperInnerCornerChart p hxOne hy⟩
    exact ⟨topChart p
      (lt_of_le_of_ne hx0 (Ne.symm hxZero))
      (lt_of_le_of_ne hx1 hxOne) hy⟩
  · rcases hinnerVertical with ⟨hx, hy1, hy2⟩
    by_cases hyOne : p.1.2 = 1
    · exact ⟨reentrantCornerChart p hx hyOne⟩
    by_cases hyTwo : p.1.2 = 2
    · exact ⟨upperInnerCornerChart p hx hyTwo⟩
    exact ⟨innerVerticalChart p hx
      (lt_of_le_of_ne hy1 (Ne.symm hyOne))
      (lt_of_le_of_ne hy2 hyTwo)⟩
  · rcases hshelf with ⟨hx1, hx2, hy⟩
    by_cases hxOne : p.1.1 = 1
    · exact ⟨reentrantCornerChart p hxOne hy⟩
    by_cases hxTwo : p.1.1 = 2
    · exact ⟨upperRightCornerChart p hxTwo hy⟩
    exact ⟨shelfChart p
      (lt_of_le_of_ne hx1 (Ne.symm hxOne))
      (lt_of_le_of_ne hx2 hxTwo) hy⟩
  · rcases hright with ⟨hx, hy0, hy1⟩
    by_cases hyZero : p.1.2 = 0
    · exact ⟨lowerRightCornerChart p hx hyZero⟩
    by_cases hyOne : p.1.2 = 1
    · exact ⟨upperRightCornerChart p hx hyOne⟩
    exact ⟨rightChart p hx
      (lt_of_le_of_ne hy0 (Ne.symm hyZero))
      (lt_of_le_of_ne hy1 hyOne)⟩
  · rcases hbottom with ⟨hx0, hx2, hy⟩
    by_cases hxZero : p.1.1 = 0
    · exact ⟨lowerLeftCornerChart p hxZero hy⟩
    by_cases hxTwo : p.1.1 = 2
    · exact ⟨lowerRightCornerChart p hxTwo hy⟩
    exact ⟨bottomChart p
      (lt_of_le_of_ne hx0 (Ne.symm hxZero))
      (lt_of_le_of_ne hx2 hxTwo) hy⟩

/-- The literal polygon's complete pointwise atlas. -/
noncomputable def boundaryAtlas : BoundaryHalfSpaceAtlas carrier where
  chart := fun p => Classical.choice (pointwiseChart_nonempty p)


/-- The reentrant shelf endpoint as a point of the derived complete frontier. -/
def reentrantPoint :
    {q : PlanePoint // q ∈ frontier carrier} :=
  ⟨(1, 1), by
    rw [frontier_carrier]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, by norm_num⟩))⟩

/-- Explicit lower-oriented ambient chart at the reentrant corner. -/
noncomputable def reentrantChart :
    PointwiseHalfSpaceChart carrier reentrantPoint :=
  reentrantCornerChart reentrantPoint rfl rfl

@[simp] theorem reentrantChart_side :
    reentrantChart.side = .lower := rfl

/-- The reentrant corner therefore supplies a genuine local frontier interval,
not only an abstract pointwise germ. -/
theorem reentrant_actualInterval_nonempty :
    Nonempty (ActualFrontierIntervalChart carrier reentrantPoint) :=
  reentrantChart.exists_actualFrontierIntervalChart

/-- The same pointwise atlas, now at the canonically selected representative. -/
noncomputable def selectedBoundaryAtlas :
    BoundaryHalfSpaceAtlas (aeOpenRepresentative carrier) := by
  rw [aeOpenRepresentative_carrier]
  exact boundaryAtlas

/-- Every topology hypothesis used by the generic producer is realized by the
literal nonconvex set itself. -/
noncomputable def selectedTopologyInput :
    SelectedBoundaryTopologyInput carrier carrier where
  representative_nonempty := carrier_nonempty
  representative_open := isOpen_carrier
  representative_bounded := isBounded_carrier
  representative_connected := isConnected_carrier
  carrier_ae := Filter.Eventually.of_forall (fun _ => rfl)
  interval_sections := hasAEIntervalHorizontalSections
  local_atlas := selectedBoundaryAtlas

/-- End-to-end output: all-height interval sections and a finite refinement of
actual local frontier intervals for the nonconvex specimen. -/
noncomputable def selectedAtlasOutput :
    SelectedBoundaryAtlasOutput carrier :=
  selectedTopologyInput.produce


open BoundaryHalfSpaceAtlas
/-- The generic topology producer derives a finite component decomposition of
the literal polygon's actual frontier. -/
noncomputable def finiteComponentDecomposition :
    FiniteFrontierComponentDecomposition carrier :=
  boundaryAtlas.finiteFrontierComponentDecomposition isBounded_carrier

/-- The compactness-derived component family exhausts all six literal sides,
including the shelf and reentrant corner. -/
theorem finiteComponentDecomposition_exhausts :
    (⋃ i : finiteComponentDecomposition.index,
        componentAt (finiteComponentDecomposition.center i)) =
      frontier carrier :=
  finiteComponentDecomposition.iUnion_componentAt_eq_frontier

/-- The actual frontier of the nonconvex specimen is locally path connected,
with no global trace supplied to the topology producer. -/
theorem frontier_locallyPathConnected :
    LocallyPathConnectedSpace (FrontierSpace carrier) :=
  boundaryAtlas.frontierLocallyPathConnectedSpace

/-- Every compactness-derived component of the polygon frontier is infinite,
including the component through the reentrant corner. -/
theorem componentAt_infinite (p : FrontierSpace carrier) :
    (componentAt p).Infinite :=
  boundaryAtlas.infinite_componentAt p

/-- The component through any polygon frontier point leaves that point's
chosen local interval chart. -/
theorem component_exits_intervalAt_window (p : FrontierSpace carrier) :
    ∃ q : PlanePoint, q ∈ componentAt p ∧
      q ∉ (boundaryAtlas.intervalAt p).window :=
  boundaryAtlas.exists_mem_componentAt_not_mem_window isBounded_carrier
    (boundaryAtlas.intervalAt p)

/-- Every selected polygon chart has exactly two connected local arms, both
incident to the chart base. -/
theorem intervalAt_twoBranchLocalTopology (p : FrontierSpace carrier) :
    let A := boundaryAtlas.intervalAt p
    IsConnected A.negativeBranch ∧
      IsConnected A.positiveBranch ∧
      Disjoint A.negativeBranch A.positiveBranch ∧
      A.negativeBranch ∪ A.positiveBranch = {A.baseInLocalDomain}ᶜ ∧
      A.baseInLocalDomain ∈ closure A.negativeBranch ∧
      A.baseInLocalDomain ∈ closure A.positiveBranch :=
  (boundaryAtlas.intervalAt p).twoBranchLocalTopology

/-- Even at the reentrant corner and shelf endpoints, deleting one actual
frontier point leaves at most the two global components selected by its local
arms. -/
theorem puncturedComponentCount_le_two (p : FrontierSpace carrier) :
    Nat.card (ConnectedComponents (PuncturedFrontierComponent p)) ≤ 2 :=
  boundaryAtlas.punctured_connectedComponents_natCard_le_two
    (boundaryAtlas.intervalAt p)

end StepPolygon
end CMVBoundaryLocalAtlas
