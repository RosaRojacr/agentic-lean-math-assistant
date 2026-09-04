/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FourArcCandidate
import GFunction

/-!
# The CMV two-cap-to-one-cap substitution

The central strip carrier and its two side arcs are retained.  The lower
exterior cap is removed, exposing its density-one interface chord.  The upper
exterior cap is replaced on the same chord by the unique upper-side cap with
twice the old Euclidean area.  `θOf` supplies all minor, semicircular, and major
branches in one constructor.
-/

open Set
open Real

noncomputable section

namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Half-central-angle of the doubled-area cap. -/
def replacementAngle : ℝ := θOf (2 * candidate.capX)

theorem replacementAngle_mem : candidate.replacementAngle ∈ Ioo 0 π := by
  exact θOf_mem (mul_pos (by norm_num) candidate.capX_pos)

theorem replacementAngle_pos : 0 < candidate.replacementAngle :=
  candidate.replacementAngle_mem.1

theorem replacementAngle_lt_pi : candidate.replacementAngle < π :=
  candidate.replacementAngle_mem.2

/-- The replacement angle realizes exactly twice the normalized old cap area. -/
theorem replacementAngle_area :
    area candidate.replacementAngle = 2 * candidate.capX := by
  exact area_θOf (mul_pos (by norm_num) candidate.capX_pos)

/-- Uniqueness on the accepted positive-area branch. -/
theorem replacementAngle_unique {theta : ℝ} (htheta : theta ∈ Ioo 0 π)
    (harea : area theta = 2 * candidate.capX) :
    theta = candidate.replacementAngle := by
  apply area_strictMonoOn.injOn htheta candidate.replacementAngle_mem
  rw [harea, candidate.replacementAngle_area]

/-- The actual retained-core-plus-upper-cap assembly. -/
def CapReplacement : ReplacementAssembly where
  core := candidate.stripCore
  replacementAngle := candidate.replacementAngle
  replacementAngle_pos := candidate.replacementAngle_pos
  replacementAngle_lt_pi := candidate.replacementAngle_lt_pi

/-- The inserted upper cap is definitionally the reusable positive-area cap
constructor at normalized area `2x`. -/
theorem replacement_upperCap_eq_ofNormalizedArea :
    candidate.CapReplacement.upperCap =
      OneSidedCircularCap.ofNormalizedArea
        candidate.capChord (2 * candidate.capX) 0 1 .upper
        candidate.capChord_pos
        (mul_pos (by norm_num) candidate.capX_pos) := by
  rfl

/-- The cap substitution as a general admissible competitor.  It has no Snell
or stationarity field. -/
def capReplacementRegion : AdmissibleCompetitor lam :=
  .replacement candidate.CapReplacement

@[simp] theorem capReplacement_core :
    candidate.CapReplacement.core = candidate.stripCore := rfl

@[simp] theorem capReplacement_angle :
    candidate.CapReplacement.replacementAngle = candidate.replacementAngle := rfl

/-- The inserted coordinate cap has Euclidean area exactly `2A`. -/
theorem replacement_cap_area :
    candidate.CapReplacement.upperCap.euclideanArea =
      2 * candidate.capArea := by
  rw [OneSidedCircularCap.euclideanArea]
  change candidate.capChord ^ 2 * area candidate.replacementAngle =
    2 * candidate.capArea
  rw [candidate.replacementAngle_area, capX]
  field_simp [candidate.capChord_ne]

/-- Its arc length is the exact Morgan scaling `L * arc (2x)`. -/
theorem replacement_cap_arc_length :
    candidate.CapReplacement.upperCap.arcLength =
      candidate.capChord * arc (2 * candidate.capX) := by
  rfl

/-- The exposed lower interface segment has Euclidean and weighted cost `L`. -/
theorem exposed_lower_chord_length :
    candidate.CapReplacement.exposedLowerChord.euclideanLength =
      candidate.capChord := rfl

/-- The lower chord lies on the density-one branch, including its endpoints. -/
theorem exposed_lower_chord_density_one {p : PlanePoint}
    (hp : p ∈ candidate.CapReplacement.exposedLowerChord.carrier) :
    StripDensity lam p = 1 := by
  have hy : p.2 = -1 := hp.1
  rw [StripDensity, hy]
  norm_num

/-- The exposed segment is an actual subset of the coordinate boundary, not
disconnected metric data. -/
theorem exposed_lower_chord_on_frontier :
    candidate.CapReplacement.exposedLowerChord.carrier ⊆
      frontier candidate.capReplacementRegion.carrier := by
  simpa [capReplacementRegion, AdmissibleCompetitor.carrier] using
    candidate.CapReplacement.exposedLowerChord_subset_frontier

/-- The competitor has a measurable coordinate carrier. -/
theorem capReplacement_measurable :
    MeasurableSet candidate.capReplacementRegion.carrier :=
  candidate.capReplacementRegion.measurableSet_carrier

/-- Its cap interior is strictly above the upper interface. -/
theorem replacement_cap_interior_above :
    candidate.CapReplacement.upperCap.interiorCarrier ⊆
      {p : PlanePoint | 1 < p.2} :=
  candidate.CapReplacement.upperCap_interior_above

/-- Every non-endpoint point on the inserted arc is strictly above `y = 1`, on
both the minor and major branches. -/
theorem replacement_arc_above {t : ℝ}
    (ht : |t| < candidate.replacementAngle) :
    1 < (candidate.CapReplacement.upperCap.arcPoint t).2 := by
  simpa [CapReplacement, ReplacementAssembly.upperCap] using
    candidate.CapReplacement.upperCap.arcPoint_in_open_side ht

/-- The replacement arc is simple on its complete minor/semicircular/major
parameter interval. -/
theorem replacement_arc_injOn :
    Set.InjOn candidate.CapReplacement.upperCap.arcPoint
      (Icc (-candidate.replacementAngle) candidate.replacementAngle) :=
  candidate.CapReplacement.upperCap.arcPoint_injOn

/-- The closed replacement cap is in `y ≥ 1`. -/
theorem replacement_cap_closure_above {p : PlanePoint}
    (hp : p ∈ candidate.CapReplacement.upperCap.carrier) :
    1 ≤ p.2 := hp.2

/-- The topological closure of the closed cap carrier remains in `y ≥ 1`. -/
theorem replacement_cap_topological_closure_above {p : PlanePoint}
    (hp : p ∈ closure candidate.CapReplacement.upperCap.carrier) :
    1 ≤ p.2 := by
  rw [candidate.CapReplacement.upperCap.isClosed_carrier.closure_eq] at hp
  exact hp.2

/-- The retained core and inserted closed cap can meet only on the upper
interface. -/
theorem replacement_meets_core_only_on_interface :
    candidate.stripCore.carrier ∩
      candidate.CapReplacement.upperCap.carrier ⊆
        {p : PlanePoint | p.2 = 1} :=
  candidate.CapReplacement.core_inter_upperCap_subset_interface

/-- Exact set-level incidence: any overlap is on the finite attachment chord,
not merely somewhere on its supporting interface line. -/
theorem replacement_meets_core_only_on_chord :
    candidate.stripCore.carrier ∩
      candidate.CapReplacement.upperCap.carrier ⊆
        candidate.CapReplacement.upperCap.chordCarrier :=
  candidate.CapReplacement.core_inter_upperCap_subset_chord

/-- Exact set-level attachment along the complete finite upper chord. -/
theorem replacement_meets_core_exactly_on_chord :
    candidate.stripCore.carrier ∩
      candidate.CapReplacement.upperCap.carrier =
        candidate.CapReplacement.upperCap.chordCarrier :=
  candidate.CapReplacement.core_inter_upperCap_eq_chord

/-- No cap interior point overlaps the retained core. -/
theorem replacement_interior_disjoint_core :
    candidate.stripCore.carrier ∩
      candidate.CapReplacement.upperCap.interiorCarrier = ∅ :=
  candidate.CapReplacement.core_inter_upperCap_interior_eq_empty

/-- The replacement covers every branch: no minor-cap restriction is present. -/
theorem replacement_branch_trichotomy :
    candidate.replacementAngle < π / 2 ∨
    candidate.replacementAngle = π / 2 ∨
    π / 2 < candidate.replacementAngle := by
  rcases lt_trichotomy candidate.replacementAngle (π / 2) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Exact branch classification in terms of the old normalized area. -/
theorem replacement_minor_iff :
    candidate.replacementAngle < π / 2 ↔ candidate.capX < π / 16 := by
  constructor
  · intro hangle
    by_contra hx
    have hx' : π / 8 ≤ 2 * candidate.capX := by
      have := le_of_not_gt hx
      linarith
    have htheta := pi_div_two_le_θOf hx'
    exact (not_lt_of_ge htheta) hangle
  · intro hx
    rw [replacementAngle]
    apply θOf_lt_pi_div_two (mul_pos (by norm_num) candidate.capX_pos)
    linarith

theorem replacement_semicircle_iff :
    candidate.replacementAngle = π / 2 ↔ candidate.capX = π / 16 := by
  constructor
  · intro h
    have harea := candidate.replacementAngle_area
    rw [h, area_pi_div_two] at harea
    linarith
  · intro h
    rw [replacementAngle, h]
    have harg : 2 * (π / 16) = π / 8 := by ring
    rw [harg, θOf_pi_div_eight]

theorem replacement_major_iff :
    π / 2 < candidate.replacementAngle ↔ π / 16 < candidate.capX := by
  constructor
  · intro hangle
    rcases lt_trichotomy candidate.capX (π / 16) with hx | hx | hx
    · have hminor := candidate.replacement_minor_iff.mpr hx
      exact False.elim (lt_asymm hangle hminor)
    · have hsemi := candidate.replacement_semicircle_iff.mpr hx
      exact False.elim ((ne_of_gt hangle) hsemi)
    · exact hx
  · intro hx
    rcases candidate.replacement_branch_trichotomy with hminor | hsemi | hmajor
    · have hx' := candidate.replacement_minor_iff.mp hminor
      exact False.elim (lt_asymm hx hx')
    · have hx' := candidate.replacement_semicircle_iff.mp hsemi
      exact False.elim ((ne_of_lt hx) hx'.symm)
    · exact hmajor

end FourArcCandidate
