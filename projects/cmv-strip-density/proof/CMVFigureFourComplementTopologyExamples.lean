/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourRawComplementTopology
import CMVFigureFourBilateralExamples

/-!
# Actual applications of four-arc complement topology

The universal closed-geometry theorem is applied to the existing bilateral
strict and radius-one specimens after arbitrary horizontal translation.
-/

open Set

noncomputable section

namespace CMVFigureFour.Examples

open CMVSourceClassification
open CMVSourceClassification.RawFourArcCoordinates

/-- Every translated strict (`R = 2`) actual source has path-connected interior
and exterior. -/
theorem strictBilateralSourceAt_complement_topology (t : ℝ) :
    IsPathConnected
        (interior (strictBilateralSourceAt t).toRawFourArcCoordinates.carrier) ∧
      IsPathConnected
        (interior (strictBilateralSourceAt t).toRawFourArcCoordinates.carrierᶜ) := by
  let raw := (strictBilateralSourceAt t).toRawFourArcCoordinates
  have hgeometry : raw.SatisfiesClosedGeometry :=
    (strictBilateralSourceAt t).toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry
  exact ⟨raw.isPathConnected_interior_carrier hgeometry,
    raw.isPathConnected_exterior_carrier hgeometry⟩

/-- Every translated exact endpoint (`R = 1`) actual source has path-connected
interior and exterior; this is an application at radius one, not a limit. -/
theorem endpointBilateralSourceAt_complement_topology (t : ℝ) :
    IsPathConnected
        (interior (endpointBilateralSourceAt t).toRawFourArcCoordinates.carrier) ∧
      IsPathConnected
        (interior (endpointBilateralSourceAt t).toRawFourArcCoordinates.carrierᶜ) := by
  let raw := (endpointBilateralSourceAt t).toRawFourArcCoordinates
  have hgeometry : raw.SatisfiesClosedGeometry :=
    (endpointBilateralSourceAt t).toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry
  exact ⟨raw.isPathConnected_interior_carrier hgeometry,
    raw.isPathConnected_exterior_carrier hgeometry⟩

/-- Concrete nonzero placement of the strict actual specimen. -/
theorem strictTranslated_complement_topology :
    IsPathConnected
        (interior (strictBilateralSourceAt (-3)).toRawFourArcCoordinates.carrier) ∧
      IsPathConnected
        (interior
          (strictBilateralSourceAt (-3)).toRawFourArcCoordinates.carrierᶜ) :=
  strictBilateralSourceAt_complement_topology (-3)

/-- Concrete nonzero placement of the radius-one actual specimen. -/
theorem endpointTranslated_complement_topology :
    IsPathConnected
        (interior (endpointBilateralSourceAt 7).toRawFourArcCoordinates.carrier) ∧
      IsPathConnected
        (interior
          (endpointBilateralSourceAt 7).toRawFourArcCoordinates.carrierᶜ) :=
  endpointBilateralSourceAt_complement_topology 7

end CMVFigureFour.Examples
