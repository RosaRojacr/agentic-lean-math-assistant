/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourComplementTopology

/-!
# Complement topology of raw four-arc carriers

This module applies the centered-section path construction to every literal raw
four-arc carrier in the closed geometric domain.  The interior route contracts
horizontally to the symmetry axis and then follows its vertical spine.  The
exterior route is the explicit horizontal/vertical escape construction from
`CMVFigureFourComplementTopology`.
-/

open Set
open Real

noncomputable section

namespace CMVSourceClassification.RawFourArcCoordinates

open CMVFigureFourComplementTopology
open CMVSourceClassification

variable (raw : RawFourArcCoordinates)

/-- Height of the upper pole, and the negative of the lower pole. -/
def verticalExtent : ℝ :=
  1 + raw.sourceRadius * (1 - cos raw.exteriorHalfAngle)

/-- Coordinate membership after undoing the arbitrary horizontal placement. -/
theorem mem_carrier_iff_centered_coordinates (x y : ℝ) :
    (x, y) ∈ raw.carrier ↔
      (x - raw.horizontalPlacement, y) ∈ raw.centeredCarrier := by
  unfold carrier
  constructor
  · rintro ⟨p, hp, heq⟩
    have hx : p.1 = x - raw.horizontalPlacement := by
      have hcoord := congrArg Prod.fst heq
      simp only [horizontalTranslation_apply] at hcoord
      linarith
    have hy : p.2 = y := by
      have hcoord := congrArg Prod.snd heq
      simpa only [horizontalTranslation_apply] using hcoord
    rw [← show p = (x - raw.horizontalPlacement, y) from Prod.ext hx hy]
    exact hp
  · intro hp
    refine ⟨(x - raw.horizontalPlacement, y), hp, ?_⟩
    rw [horizontalTranslation_apply]
    apply Prod.ext <;> simp

private theorem sourceRadius_pos_of_geometry
    (h : raw.SatisfiesClosedGeometry) : 0 < raw.sourceRadius :=
  lt_of_lt_of_le zero_lt_one h.radius_ge_one

private theorem sin_exteriorHalfAngle_pos
    (h : raw.SatisfiesClosedGeometry) :
    0 < sin raw.exteriorHalfAngle :=
  Real.sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
    (lt_trans h.exteriorHalfAngle_lt_pi_div_two
      (by linarith [Real.pi_pos]))

private theorem cos_exteriorHalfAngle_pos
    (h : raw.SatisfiesClosedGeometry) :
    0 < cos raw.exteriorHalfAngle :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h.exteriorHalfAngle_pos],
    h.exteriorHalfAngle_lt_pi_div_two⟩

private theorem cos_exteriorHalfAngle_lt_one
    (h : raw.SatisfiesClosedGeometry) :
    cos raw.exteriorHalfAngle < 1 := by
  have htrig := Real.sin_sq_add_cos_sq raw.exteriorHalfAngle
  have hsin := raw.sin_exteriorHalfAngle_pos h
  nlinarith [sq_nonneg (cos raw.exteriorHalfAngle)]

/-- The two poles lie strictly outside the strip interfaces. -/
theorem verticalExtent_gt_one
    (h : raw.SatisfiesClosedGeometry) : 1 < raw.verticalExtent := by
  unfold verticalExtent
  exact lt_add_of_pos_right 1 (mul_pos (raw.sourceRadius_pos_of_geometry h)
    (sub_pos.mpr (raw.cos_exteriorHalfAngle_lt_one h)))

/-- Every literal horizontal section has the centered closed-interval shape
used by the spine and escape constructions, including interface heights and
poles. -/
theorem hasCenteredClosedSections
    (h : raw.SatisfiesClosedGeometry) :
    HasCenteredClosedSections raw.carrier raw.horizontalPlacement :=
  raw.horizontalSection_empty_or_centered_interval h

/-- The literal raw carrier is bounded for every horizontal placement. -/
theorem isBounded_carrier
    (h : raw.SatisfiesClosedGeometry) : Bornology.IsBounded raw.carrier := by
  rw [raw.carrier_eq_horizontalTranslation_candidate (lam := 1) h]
  exact (CMVFigureFour.isometry_horizontalTranslation raw.horizontalPlacement).lipschitz
    |>.isBounded_image
      (CMVFigureFour.isBounded_fourArcAssembly_carrier
        (raw.toFourArcCandidate (lam := 1) h).assembly)

/-- Exact global vertical bounds of the literal closed carrier. -/
theorem carrier_vertical_bounds
    (h : raw.SatisfiesClosedGeometry) {p : PlanePoint}
    (hp : p ∈ raw.carrier) :
    -raw.verticalExtent ≤ p.2 ∧ p.2 ≤ raw.verticalExtent := by
  have hR := raw.sourceRadius_pos_of_geometry h
  have hE := (raw.verticalExtent_gt_one h).le
  rw [raw.mem_carrier_iff_centered_coordinates] at hp
  simp only [centeredCarrier, rectangleCarrier, leftSegmentCarrier,
    rightSegmentCarrier, upperCapCarrier, lowerCapCarrier, leftCenter,
    rightCenter, upperCenter, lowerCenter, Set.mem_union, Set.mem_ofPred_eq,
    sub_zero] at hp
  rcases hp with (((hrect | hleft) | hright) | hupper) | hlower
  · exact ⟨by linarith [abs_le.mp hrect.2.2 |>.1],
      by linarith [abs_le.mp hrect.2.2 |>.2]⟩
  · exact ⟨by linarith [abs_le.mp hleft.2.2 |>.1],
      by linarith [abs_le.mp hleft.2.2 |>.2]⟩
  · exact ⟨by linarith [abs_le.mp hright.2.2 |>.1],
      by linarith [abs_le.mp hright.2.2 |>.2]⟩
  · constructor
    · linarith [hupper.2]
    · have hySq :
          (p.2 - (1 - raw.sourceRadius * cos raw.exteriorHalfAngle)) ^ 2 ≤
            raw.sourceRadius ^ 2 := by
        nlinarith [hupper.1,
          sq_nonneg (p.1 - raw.horizontalPlacement)]
      unfold verticalExtent
      nlinarith [sq_nonneg
        (p.2 - (1 - raw.sourceRadius * cos raw.exteriorHalfAngle) +
          raw.sourceRadius)]
  · constructor
    · have hySq :
          (p.2 - (-1 + raw.sourceRadius * cos raw.exteriorHalfAngle)) ^ 2 ≤
            raw.sourceRadius ^ 2 := by
        nlinarith [hlower.1,
          sq_nonneg (p.1 - raw.horizontalPlacement)]
      unfold verticalExtent
      nlinarith [sq_nonneg
        (p.2 - (-1 + raw.sourceRadius * cos raw.exteriorHalfAngle) -
          raw.sourceRadius)]
    · linarith [hlower.2]

private theorem continuous_lowerDiskValue :
    Continuous (fun q : PlanePoint =>
      (q.1 - raw.horizontalPlacement) ^ 2 +
        (q.2 - raw.lowerCenter.2) ^ 2) := by
  fun_prop

private theorem continuous_upperDiskValue :
    Continuous (fun q : PlanePoint =>
      (q.1 - raw.horizontalPlacement) ^ 2 +
        (q.2 - raw.upperCenter.2) ^ 2) := by
  fun_prop

/-- The symmetry-axis point at every strict height between the poles is an
interior point.  Open neighborhoods are supplied separately in the strip,
in each cap, and across both strip/cap interfaces. -/
theorem axis_mem_interior_of_abs_lt_verticalExtent
    (h : raw.SatisfiesClosedGeometry) {y : ℝ}
    (hy : |y| < raw.verticalExtent) :
    (raw.horizontalPlacement, y) ∈ interior raw.carrier := by
  have hR := raw.sourceRadius_pos_of_geometry h
  have hsin := raw.sin_exteriorHalfAngle_pos h
  have hcos := raw.cos_exteriorHalfAngle_pos h
  have hwidth : 0 < raw.outerHalfWidth := by
    exact mul_pos hR hsin
  have hE := raw.verticalExtent_gt_one h
  have htrig := Real.sin_sq_add_cos_sq raw.exteriorHalfAngle
  have hcapAtInterface :
      (raw.sourceRadius * cos raw.exteriorHalfAngle) ^ 2 <
        raw.sourceRadius ^ 2 := by
    nlinarith [mul_pos hR hsin, mul_pos hR hcos,
      sq_nonneg (raw.sourceRadius * sin raw.exteriorHalfAngle)]
  have interior_of_open_subset {U : Set PlanePoint}
      (hUopen : IsOpen U) (haxis : (raw.horizontalPlacement, y) ∈ U)
      (hUK : U ⊆ raw.carrier) :
      (raw.horizontalPlacement, y) ∈ interior raw.carrier := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hUopen.mem_nhds haxis) hUK
  rcases lt_trichotomy y (-1) with hyLower | rfl | hyAboveLower
  · let U : Set PlanePoint := {q |
        (q.1 - raw.horizontalPlacement) ^ 2 +
            (q.2 - raw.lowerCenter.2) ^ 2 < raw.sourceRadius ^ 2 ∧
          q.2 < -1}
    apply interior_of_open_subset (U := U)
    · dsimp [U]
      apply IsOpen.inter
      · exact isOpen_lt raw.continuous_lowerDiskValue continuous_const
      · exact isOpen_lt continuous_snd continuous_const
    · constructor
      · have hyLow := (abs_lt.mp hy).1
        have hyCenterUpper :
            y - (-1 + raw.sourceRadius * cos raw.exteriorHalfAngle) < 0 := by
          nlinarith [mul_pos hR hcos]
        have hyCenterLower :
            -raw.sourceRadius <
              y - (-1 + raw.sourceRadius * cos raw.exteriorHalfAngle) := by
          unfold verticalExtent at hyLow
          linarith
        simp only [lowerCenter]
        nlinarith
      · exact hyLower
    · intro q hq
      rw [raw.mem_carrier_iff_centered_coordinates]
      apply Or.inr
      exact ⟨by simpa [lowerCenter] using hq.1.le, hq.2.le⟩
  · let U : Set PlanePoint := {q |
        raw.horizontalPlacement - raw.outerHalfWidth < q.1 ∧
          q.1 < raw.horizontalPlacement + raw.outerHalfWidth ∧
          (q.1 - raw.horizontalPlacement) ^ 2 +
              (q.2 - raw.lowerCenter.2) ^ 2 < raw.sourceRadius ^ 2 ∧
            q.2 < 0}
    apply interior_of_open_subset (U := U)
    · dsimp [U]
      apply IsOpen.inter
      · exact isOpen_lt continuous_const continuous_fst
      · apply IsOpen.inter
        · exact isOpen_lt continuous_fst continuous_const
        · apply IsOpen.inter
          · exact isOpen_lt raw.continuous_lowerDiskValue continuous_const
          · exact isOpen_lt continuous_snd continuous_const
    · refine ⟨by linarith, by linarith, ?_, by norm_num⟩
      simp only [lowerCenter]
      simpa [sq] using hcapAtInterface
    · intro q hq
      rw [raw.mem_carrier_iff_centered_coordinates]
      by_cases hqy : q.2 ≤ -1
      · exact Or.inr ⟨by simpa [lowerCenter] using hq.2.2.1.le, hqy⟩
      · apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inl
        constructor
        · linarith [hq.1]
        · constructor
          · linarith [hq.2.1]
          · rw [abs_le]
            exact ⟨(lt_of_not_ge hqy).le, by linarith [hq.2.2.2]⟩
  · rcases lt_trichotomy y 1 with hyStrip | rfl | hyUpper
    · let U : Set PlanePoint := {q |
          raw.horizontalPlacement - raw.outerHalfWidth < q.1 ∧
            q.1 < raw.horizontalPlacement + raw.outerHalfWidth ∧
              |q.2| < 1}
      apply interior_of_open_subset (U := U)
      · dsimp [U]
        apply IsOpen.inter
        · exact isOpen_lt continuous_const continuous_fst
        · apply IsOpen.inter
          · exact isOpen_lt continuous_fst continuous_const
          · exact isOpen_lt continuous_snd.abs continuous_const
      · exact ⟨by linarith, by linarith,
          abs_lt.2 ⟨hyAboveLower, hyStrip⟩⟩
      · intro q hq
        rw [raw.mem_carrier_iff_centered_coordinates]
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact ⟨by linarith [hq.1], by linarith [hq.2.1], hq.2.2.le⟩
    · let U : Set PlanePoint := {q |
          raw.horizontalPlacement - raw.outerHalfWidth < q.1 ∧
            q.1 < raw.horizontalPlacement + raw.outerHalfWidth ∧
            (q.1 - raw.horizontalPlacement) ^ 2 +
                (q.2 - raw.upperCenter.2) ^ 2 < raw.sourceRadius ^ 2 ∧
              0 < q.2}
      apply interior_of_open_subset (U := U)
      · dsimp [U]
        apply IsOpen.inter
        · exact isOpen_lt continuous_const continuous_fst
        · apply IsOpen.inter
          · exact isOpen_lt continuous_fst continuous_const
          · apply IsOpen.inter
            · exact isOpen_lt raw.continuous_upperDiskValue continuous_const
            · exact isOpen_lt continuous_const continuous_snd
      · refine ⟨by linarith, by linarith, ?_, by norm_num⟩
        simp only [upperCenter]
        simpa [sq] using hcapAtInterface
      · intro q hq
        rw [raw.mem_carrier_iff_centered_coordinates]
        by_cases hqy : q.2 ≤ 1
        · apply Or.inl
          apply Or.inl
          apply Or.inl
          apply Or.inl
          constructor
          · linarith [hq.1]
          · constructor
            · linarith [hq.2.1]
            · rw [abs_le]
              exact ⟨by linarith [hq.2.2.2], hqy⟩
        · exact Or.inl (Or.inr
            ⟨by simpa [upperCenter] using hq.2.2.1.le, le_of_not_ge hqy⟩)
    · let U : Set PlanePoint := {q |
          (q.1 - raw.horizontalPlacement) ^ 2 +
              (q.2 - raw.upperCenter.2) ^ 2 < raw.sourceRadius ^ 2 ∧
            1 < q.2}
      apply interior_of_open_subset (U := U)
      · dsimp [U]
        apply IsOpen.inter
        · exact isOpen_lt raw.continuous_upperDiskValue continuous_const
        · exact isOpen_lt continuous_const continuous_snd
      · constructor
        · have hyHigh := (abs_lt.mp hy).2
          have hyCenterLower :
              0 < y - (1 - raw.sourceRadius * cos raw.exteriorHalfAngle) := by
            nlinarith [mul_pos hR hcos]
          have hyCenterUpper :
              y - (1 - raw.sourceRadius * cos raw.exteriorHalfAngle) <
                raw.sourceRadius := by
            unfold verticalExtent at hyHigh
            linarith
          simp only [upperCenter]
          nlinarith
        · exact hyUpper
      · intro q hq
        rw [raw.mem_carrier_iff_centered_coordinates]
        exact Or.inl (Or.inr
          ⟨by simpa [upperCenter] using hq.1.le, hq.2.le⟩)


/-- Interior points lie strictly between the two poles. -/
theorem interior_vertical_bounds
    (h : raw.SatisfiesClosedGeometry) {p : PlanePoint}
    (hp : p ∈ interior raw.carrier) :
    |p.2| < raw.verticalExtent := by
  have hclosedBounds :=
    raw.carrier_vertical_bounds h (interior_subset hp)
  rw [abs_lt]
  constructor
  · by_contra hnot
    have hpEq : p.2 = -raw.verticalExtent := by
      exact le_antisymm (le_of_not_gt hnot) hclosedBounds.1
    obtain ⟨epsilon, hepsilon, hball⟩ :=
      Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
    let q : PlanePoint := (p.1, p.2 - epsilon / 2)
    have hqball : q ∈ Metric.ball p epsilon := by
      rw [Metric.mem_ball, Prod.dist_eq]
      dsimp [q]
      rw [dist_self, max_eq_right (dist_nonneg : 0 ≤ dist (p.2 - epsilon / 2) p.2),
        Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hqBounds := raw.carrier_vertical_bounds h
      (interior_subset (hball hqball))
    dsimp [q] at hqBounds
    linarith
  · by_contra hnot
    have hpEq : p.2 = raw.verticalExtent := by
      exact le_antisymm hclosedBounds.2 (le_of_not_gt hnot)
    obtain ⟨epsilon, hepsilon, hball⟩ :=
      Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
    let q : PlanePoint := (p.1, p.2 + epsilon / 2)
    have hqball : q ∈ Metric.ball p epsilon := by
      rw [Metric.mem_ball, Prod.dist_eq]
      dsimp [q]
      rw [dist_self, max_eq_right (dist_nonneg : 0 ≤ dist (p.2 + epsilon / 2) p.2),
        Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    have hqBounds := raw.carrier_vertical_bounds h
      (interior_subset (hball hqball))
    dsimp [q] at hqBounds
    linarith

/-- The literal vertical spine joins the horizontal projection of an interior
point to the common interior base point on the symmetry axis. -/
theorem interior_vertical_spine_joinedIn
    (h : raw.SatisfiesClosedGeometry) {p : PlanePoint}
    (hp : p ∈ interior raw.carrier) :
    JoinedIn (interior raw.carrier)
      (raw.horizontalPlacement, p.2)
      (raw.horizontalPlacement, 0) := by
  have hpHeight := raw.interior_vertical_bounds h hp
  apply JoinedIn.of_segment_subset
  rw [segment_subset_iff]
  intro a b ha hb hab
  have ha1 : a ≤ 1 := by linarith
  have hscaled : |a * p.2| < raw.verticalExtent := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_of_le_one_left (abs_nonneg p.2) ha1).trans_lt hpHeight
  convert raw.axis_mem_interior_of_abs_lt_verticalExtent h hscaled using 1
  apply Prod.ext
  · dsimp
    rw [show b = 1 - a by linarith]
    ring
  · dsimp
    ring

/-- Named interior spine path: horizontal contraction followed by the vertical
axis segment reaches the same base point from every interior point. -/
theorem interior_spine_joinedIn
    (h : raw.SatisfiesClosedGeometry) {p : PlanePoint}
    (hp : p ∈ interior raw.carrier) :
    JoinedIn (interior raw.carrier) p
      (raw.horizontalPlacement, 0) :=
  (CMVFigureFourComplementTopology.interior_horizontal_spine_joinedIn
      (raw.hasCenteredClosedSections h) hp).trans
    (raw.interior_vertical_spine_joinedIn h hp)

/-- The literal open interior is nonempty. -/
theorem interior_carrier_nonempty
    (h : raw.SatisfiesClosedGeometry) :
    (interior raw.carrier).Nonempty :=
  ⟨(raw.horizontalPlacement, 0),
    raw.axis_mem_interior_of_abs_lt_verticalExtent h
      (by rw [abs_zero]; linarith [raw.verticalExtent_gt_one h])⟩

/-- The interior is path-connected by the explicit horizontal/vertical spine
paths. -/
theorem isPathConnected_interior_carrier
    (h : raw.SatisfiesClosedGeometry) :
    IsPathConnected (interior raw.carrier) := by
  refine ⟨(raw.horizontalPlacement, 0),
    raw.axis_mem_interior_of_abs_lt_verticalExtent h
      (by rw [abs_zero]; linarith [raw.verticalExtent_gt_one h]), ?_⟩
  intro p hp
  exact (raw.interior_spine_joinedIn h hp).symm

/-- The exterior is path-connected by horizontal escape to one side, vertical
escape past a norm bound, and a common horizontal segment above the carrier. -/
theorem isPathConnected_compl_carrier
    (h : raw.SatisfiesClosedGeometry) :
    IsPathConnected raw.carrierᶜ :=
  CMVFigureFourComplementTopology.isPathConnected_compl_of_bounded_centeredSections
    (raw.isBounded_carrier h) (raw.hasCenteredClosedSections h)

/-- The exterior is nonempty. -/
theorem compl_carrier_nonempty
    (h : raw.SatisfiesClosedGeometry) : raw.carrierᶜ.Nonempty :=
  (raw.isPathConnected_compl_carrier h).nonempty

/-- The topological exterior equals the literal complement because the raw
carrier is closed. -/
theorem interior_compl_carrier_eq :
    interior raw.carrierᶜ = raw.carrierᶜ :=
  raw.isClosed_carrier.isOpen_compl.interior_eq

/-- The topological exterior is path-connected. -/
theorem isPathConnected_exterior_carrier
    (h : raw.SatisfiesClosedGeometry) :
    IsPathConnected (interior raw.carrierᶜ) := by
  rw [raw.interior_compl_carrier_eq]
  exact raw.isPathConnected_compl_carrier h

/-- The topological exterior is nonempty. -/
theorem exterior_carrier_nonempty
    (h : raw.SatisfiesClosedGeometry) :
    (interior raw.carrierᶜ).Nonempty :=
  (raw.isPathConnected_exterior_carrier h).nonempty

/-- One common exterior anchor is joined to every exterior point by the
explicit horizontal/vertical escape construction. -/
theorem exists_exterior_escape_anchor
    (h : raw.SatisfiesClosedGeometry) :
    ∃ anchor : PlanePoint, anchor ∈ raw.carrierᶜ ∧
      ∀ p ∈ raw.carrierᶜ, JoinedIn raw.carrierᶜ p anchor := by
  let connected := raw.isPathConnected_compl_carrier h
  let anchor := connected.nonempty.choose
  exact ⟨anchor, connected.nonempty.choose_spec, fun p hp =>
    connected.joinedIn p hp anchor connected.nonempty.choose_spec⟩

/-- Removing the complete frontier leaves exactly the disjoint interior and
exterior.  This statement includes all four junctions and both poles because it
uses the topological frontier of the full literal carrier. -/
theorem compl_frontier_carrier_eq_interior_union_exterior :
    (frontier raw.carrier)ᶜ =
      interior raw.carrier ∪ raw.carrierᶜ := by
  rw [compl_frontier_eq_union_interior,
    raw.isClosed_carrier.isOpen_compl.interior_eq]

/-- The interior and exterior pieces of the frontier complement are disjoint. -/
theorem disjoint_interior_carrier_compl :
    Disjoint (interior raw.carrier) raw.carrierᶜ := by
  rw [Set.disjoint_left]
  intro p hpInterior hpExterior
  exact hpExterior (interior_subset hpInterior)
end CMVSourceClassification.RawFourArcCoordinates
