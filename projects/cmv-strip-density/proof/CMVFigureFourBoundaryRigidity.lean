/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourRawComplementTopology

/-!
# Boundary-only rigidity for CMV Figure 4

A bounded open set with the literal four-arc frontier is forced to be the
interior of the closed four-arc carrier.  The proof uses the two connected
components of the complete-frontier complement; it does not use horizontal
sections or local circle-side orientations.
-/

open Set Real MeasureTheory

noncomputable section

namespace CMVFigureFourBoundaryRigidity

open CMVSourceClassification

/-- A bounded open set is determined by a common frontier with a bounded closed
target whose interior and exterior are connected and whose interior is
nonempty.  The two connected pieces are derived from the target, rather than
assumed as components of the source. -/
theorem boundedOpen_eq_interior_of_frontier_eq_of_two_components
    {U K : Set PlanePoint}
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hKclosed : IsClosed K) (hKbounded : Bornology.IsBounded K)
    (hfrontier : frontier U = frontier K)
    (hinterior : IsPreconnected (interior K))
    (hexterior : IsPreconnected Kᶜ)
    (hinterior_nonempty : (interior K).Nonempty) :
    U = interior K := by
  have hphases : (frontier U)ᶜ = U ∪ interior Uᶜ := by
    rw [compl_frontier_eq_union_interior, hUopen.interior_eq]
  have htargetPhases : (frontier K)ᶜ = interior K ∪ Kᶜ := by
    rw [compl_frontier_eq_union_interior,
      hKclosed.isOpen_compl.interior_eq]
  have hdisjoint : Disjoint U (interior Uᶜ) := by
    rw [Set.disjoint_left]
    intro p hpU hpExterior
    exact (interior_subset hpExterior) hpU
  have hbothBounded : Bornology.IsBounded (U ∪ K) :=
    hUbounded.union hKbounded
  obtain ⟨R, _, hbounded⟩ := hbothBounded.subset_closedBall_lt 0 0
  obtain ⟨p, hpNorm⟩ := NormedSpace.exists_lt_norm ℝ PlanePoint R
  have hpOutside : p ∈ (Metric.closedBall 0 R)ᶜ := by
    simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      using hpNorm
  have hpK : p ∈ Kᶜ := by
    intro hp
    exact hpOutside (hbounded (Or.inr hp))
  have hpUExterior : p ∈ interior Uᶜ := by
    apply interior_maximal
      (s := Uᶜ)
      (t := (Metric.closedBall 0 R)ᶜ)
      (fun q hq hqU => hq (hbounded (Or.inl hqU)))
      Metric.isClosed_closedBall.isOpen_compl
    exact hpOutside
  have hexteriorCover : Kᶜ ⊆ U ∪ interior Uᶜ := by
    intro q hqK
    rw [← hphases]
    intro hqFrontier
    have hqTargetFrontier : q ∈ frontier K := by
      rw [← hfrontier]
      exact hqFrontier
    exact hqK (hKclosed.frontier_subset hqTargetFrontier)
  have hexteriorSubset : Kᶜ ⊆ interior Uᶜ :=
    hexterior.subset_right_of_subset_union hUopen isOpen_interior hdisjoint
      hexteriorCover ⟨p, hpK, hpUExterior⟩
  have hUsubset : U ⊆ interior K := by
    intro q hqU
    have hqNotFrontier : q ∈ (frontier U)ᶜ := by
      intro hqFrontier
      have hqEmpty : q ∈ U ∩ frontier U := ⟨hqU, hqFrontier⟩
      rw [hUopen.inter_frontier_eq] at hqEmpty
      exact hqEmpty
    have hqTarget : q ∈ (frontier K)ᶜ := by
      rwa [← hfrontier]
    rw [htargetPhases] at hqTarget
    rcases hqTarget with hqInterior | hqExterior
    · exact hqInterior
    · exact False.elim ((interior_subset (hexteriorSubset hqExterior)) hqU)
  have hKnonempty : K.Nonempty :=
    hinterior_nonempty.mono interior_subset
  have hKneUniv : K ≠ (Set.univ : Set PlanePoint) := by
    intro hKuniv
    exact hpK (hKuniv ▸ mem_univ p)
  have htargetFrontierNonempty : (frontier K).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hKnonempty, hKneUniv⟩
  have hsourceFrontierNonempty : (frontier U).Nonempty := by
    rwa [hfrontier]
  have hUnonempty : U.Nonempty := by
    by_contra hUempty
    have hUeq : U = ∅ := not_nonempty_iff_eq_empty.mp hUempty
    rw [hUeq] at hsourceFrontierNonempty
    simpa using hsourceFrontierNonempty
  obtain ⟨q, hqU⟩ := hUnonempty
  have hinteriorCover : interior K ⊆ U ∪ interior Uᶜ := by
    intro z hzInterior
    have hzTarget : z ∈ (frontier K)ᶜ := by
      rw [htargetPhases]
      exact Or.inl hzInterior
    have hzSource : z ∈ (frontier U)ᶜ := by
      rwa [hfrontier]
    rwa [hphases] at hzSource
  have hinteriorSubset : interior K ⊆ U :=
    hinterior.subset_left_of_subset_union hUopen isOpen_interior hdisjoint
      hinteriorCover ⟨q, hUsubset hqU, hqU⟩
  exact Set.Subset.antisymm hUsubset hinteriorSubset

end CMVFigureFourBoundaryRigidity

namespace CMVFigureFourTargetGeometry.RawFourArcCoordinates

open CMVSourceClassification
open CMVFigureFour

variable (raw : RawFourArcCoordinates)

/-- The complete frontier of the horizontally placed raw carrier is exactly the
four placed supporting-circle traces. -/
theorem frontier_carrier_eq_four_circles
    (h : raw.SatisfiesClosedGeometry) :
    frontier raw.carrier =
      exteriorCircleTrace .upper (placedUpperCenter raw) raw.sourceRadius ∪
        exteriorCircleTrace .lower (placedLowerCenter raw) raw.sourceRadius ∪
          stripCircleTrace .left (placedLeftCenter raw) raw.sourceRadius ∪
            stripCircleTrace .right (placedRightCenter raw) raw.sourceRadius := by
  let candidate : FourArcCandidate (1 : ℝ) := raw.toFourArcCandidate h
  have hR0 : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hcoreRadius : candidate.assembly.core.radius = raw.sourceRadius := by
    simp only [candidate, FourArcCandidate.assembly_core,
      FourArcCandidate.stripCore, StripCore.radius,
      CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
      CMVSourceClassification.RawFourArcCoordinates.curvature]
    field_simp [ne_of_gt hR0]
  have hchord : candidate.assembly.core.chord / 2 = raw.outerHalfWidth := by
    simp only [candidate, FourArcCandidate.assembly_core,
      FourArcCandidate.stripCore, FourArcCandidate.capChord,
      CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
      CMVSourceClassification.RawFourArcCoordinates.outerHalfWidth,
      CMVSourceClassification.RawFourArcCoordinates.curvature]
    field_simp [ne_of_gt hR0]
  have hcoreCos :
      cos candidate.assembly.core.sideAngle = raw.innerRadial := by
    rw [StripCore.cos_sideAngle]
    rfl
  have hleftCenter :
      (candidate.assembly.core.leftCenterX, 0) = raw.leftCenter := by
    apply Prod.ext
    · rw [StripCore.leftCenterX,
        show -candidate.assembly.core.chord / 2 =
          -(candidate.assembly.core.chord / 2) by ring,
        hchord, hcoreRadius, hcoreCos]
      simp only [CMVSourceClassification.RawFourArcCoordinates.leftCenter,
        CMVSourceClassification.RawFourArcCoordinates.sideCenterOffset,
        CMVSourceClassification.RawFourArcCoordinates.outerHalfWidth]
      ring
    · rfl
  have hrightCenter :
      (candidate.assembly.core.rightCenterX, 0) = raw.rightCenter := by
    apply Prod.ext
    · rw [StripCore.rightCenterX, hchord, hcoreRadius, hcoreCos]
      simp only [CMVSourceClassification.RawFourArcCoordinates.rightCenter,
        CMVSourceClassification.RawFourArcCoordinates.sideCenterOffset,
        CMVSourceClassification.RawFourArcCoordinates.outerHalfWidth]
      ring
    · rfl
  have hupperRadius :
      candidate.assembly.upperCap.radius = raw.sourceRadius := by
    rw [candidate.four_arcs_common_radius.1]
    exact hcoreRadius
  have hlowerRadius :
      candidate.assembly.lowerCap.radius = raw.sourceRadius := by
    rw [candidate.four_arcs_common_radius.2]
    exact hcoreRadius
  have hupperCenter :
      candidate.assembly.upperCap.center = raw.upperCenter := by
    change (0, 1 - candidate.assembly.upperCap.radius *
      cos raw.exteriorHalfAngle) = raw.upperCenter
    rw [hupperRadius]
    rfl
  have hlowerCenter :
      candidate.assembly.lowerCap.center = raw.lowerCenter := by
    change (0, -1 + candidate.assembly.lowerCap.radius *
      cos raw.exteriorHalfAngle) = raw.lowerCenter
    rw [hlowerRadius]
    rfl
  calc
    frontier raw.carrier =
        frontier (horizontalTranslation raw.horizontalPlacement ''
          candidate.assembly.carrier) := by
      rw [show raw.carrier = horizontalTranslation raw.horizontalPlacement ''
          candidate.assembly.carrier from
        raw.carrier_eq_horizontalTranslation_candidate h]
    _ = horizontalTranslation raw.horizontalPlacement ''
          frontier candidate.assembly.carrier :=
      ((horizontalTranslation raw.horizontalPlacement).image_frontier
        candidate.assembly.carrier).symm
    _ = horizontalTranslation raw.horizontalPlacement ''
          candidate.assembly.boundaryTrace := by
      rw [candidate.assembly.frontier_carrier]
    _ = exteriorCircleTrace .upper (placedUpperCenter raw) raw.sourceRadius ∪
        exteriorCircleTrace .lower (placedLowerCenter raw) raw.sourceRadius ∪
          stripCircleTrace .left (placedLeftCenter raw) raw.sourceRadius ∪
            stripCircleTrace .right (placedRightCenter raw) raw.sourceRadius := by
      rw [FourArcAssembly.boundaryTrace, image_union, image_union, image_union,
        CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace,
        CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace,
        CMVFigureFour.FourArcAssembly.upperArcTrace_eq_exteriorCircleTrace,
        CMVFigureFour.FourArcAssembly.lowerArcTrace_eq_exteriorCircleTrace,
        CMVFigureFour.horizontalTranslation_image_stripCircleTrace,
        CMVFigureFour.horizontalTranslation_image_stripCircleTrace,
        CMVFigureFour.horizontalTranslation_image_exteriorCircleTrace,
        CMVFigureFour.horizontalTranslation_image_exteriorCircleTrace,
        hleftCenter, hrightCenter, hupperCenter, hlowerCenter,
        hcoreRadius, hupperRadius, hlowerRadius]
      simp only [placedLeftCenter, placedRightCenter, placedUpperCenter,
        placedLowerCenter]
      ac_rfl

/-- The complete frontier of the horizontally placed raw target is
planar-null.  This transports the existing assembly-level nullity through the
literal raw-to-candidate identity; no frontier component is discarded. -/
theorem volume_frontier_carrier
    (h : raw.SatisfiesClosedGeometry) :
    volume (frontier raw.carrier) = 0 := by
  let candidate : FourArcCandidate (1 : ℝ) := raw.toFourArcCandidate h
  have hfrontier :
      frontier raw.carrier =
        horizontalTranslation raw.horizontalPlacement ''
          frontier candidate.assembly.carrier := by
    rw [raw.carrier_eq_horizontalTranslation_candidate (lam := 1) h]
    exact
      ((horizontalTranslation raw.horizontalPlacement).image_frontier
        candidate.assembly.carrier).symm
  rw [hfrontier]
  have hvolume :=
    (measurePreserving_horizontalTranslation raw.horizontalPlacement)
      |>.setLIntegral_comp_emb
        (horizontalTranslation raw.horizontalPlacement).measurableEmbedding
        (fun _ : PlanePoint => (1 : ENNReal))
        (frontier candidate.assembly.carrier)
  calc
    volume
        (horizontalTranslation raw.horizontalPlacement ''
          frontier candidate.assembly.carrier) =
        volume (frontier candidate.assembly.carrier) := by
      simpa using hvolume.symm
    _ = 0 := CMVFigureFour.volume_frontier_fourArcAssembly candidate.assembly

/-- The interior and closed raw target agree almost everywhere, including at
source radius one and at arbitrary horizontal placement. -/
theorem interior_carrier_ae_eq_carrier
    (h : raw.SatisfiesClosedGeometry) :
    interior raw.carrier =ᵐ[volume] raw.carrier := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpInterior, hpNotCarrier⟩
      exact (hpNotCarrier (interior_subset hpInterior)).elim
    · exact measure_empty
  · apply measure_mono_null (t := frontier raw.carrier)
    · rintro p ⟨hpCarrier, hpNotInterior⟩
      rw [mem_frontier_iff_notMem_interior hpCarrier]
      exact hpNotInterior
    · exact volume_frontier_carrier raw h

end CMVFigureFourTargetGeometry.RawFourArcCoordinates

namespace CMVFigureFour.SourceGeometry

open CMVSourceClassification
open CMVFigureFourTargetGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- The source representative and its derived literal raw target have exactly
the same complete topological frontier. -/
theorem frontier_representative_eq_raw_carrier :
    frontier g.representative =
      frontier g.toRawFourArcCoordinates.carrier := by
  rw [g.frontier_eq_four_circles,
    CMVFigureFourTargetGeometry.RawFourArcCoordinates.frontier_carrier_eq_four_circles
      g.toRawFourArcCoordinates
        g.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry,
    SourceAlignment.upperCenter_eq_placedUpperCenter g,
    SourceAlignment.lowerCenter_eq_placedLowerCenter g,
    SourceAlignment.leftStripCenter_eq_placedLeftCenter g,
    SourceAlignment.rightStripCenter_eq_placedRightCenter g]
  rfl

/-- Boundary-only reconstruction of every frozen Figure-4 representative,
including the source-radius-one branch. -/
theorem representative_eq_interior_raw_carrier :
    g.representative = interior g.toRawFourArcCoordinates.carrier := by
  let raw := g.toRawFourArcCoordinates
  have hgeometry : raw.SatisfiesClosedGeometry :=
    g.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry
  apply CMVFigureFourBoundaryRigidity.boundedOpen_eq_interior_of_frontier_eq_of_two_components
    g.sourceRepresentative.representative_open
    g.sourceRepresentative.representative_bounded
    raw.isClosed_carrier
    (raw.isBounded_carrier hgeometry)
    g.frontier_representative_eq_raw_carrier
    (raw.isPathConnected_interior_carrier hgeometry).isConnected.isPreconnected
    (raw.isPathConnected_compl_carrier hgeometry).isConnected.isPreconnected
    (raw.interior_carrier_nonempty hgeometry)

end CMVFigureFour.SourceGeometry
