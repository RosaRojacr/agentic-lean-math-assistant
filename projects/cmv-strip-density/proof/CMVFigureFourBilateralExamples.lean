/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourScalarReduction

/-!
# Concrete bilateral Figure-4 sources

The strict radius-two and closed radius-one coordinate witnesses are realized as
literal four-arc carriers with bounded open interiors.  Horizontal translation
then supplies every placement; vertical reflection is derived by the bilateral
producer rather than stored in either specimen.
-/

open Set

noncomputable section

namespace CMVFigureFour
namespace Examples

/-- The strict `lambda = 2`, `R = 2` source with literal closed carrier and
actual bounded open representative. -/
def strictBilateralSource : BilateralSourceIncidence 2 :=
  BilateralSourceIncidence.ofFourArcCandidate
    (strictRaw.toFourArcCandidate
      strictRaw_satisfiesClosedSnell.toGeometry)
    (strictRaw.toFourArcCandidate_satisfiesCMVTypeIVHypotheses
      strictRaw_satisfiesClosedSnell)

/-- The closed `lambda = 2`, `R = 1` endpoint source.  This is an actual
specimen, not a limiting statement. -/
def endpointBilateralSource : BilateralSourceIncidence 2 :=
  BilateralSourceIncidence.ofFourArcCandidate
    (endpointRaw.toFourArcCandidate
      endpointRaw_satisfiesClosedSnell.toGeometry)
    (endpointRaw.toFourArcCandidate_satisfiesCMVTypeIVHypotheses
      endpointRaw_satisfiesClosedSnell)

@[simp] theorem strictBilateralSource_sourceRadius :
    strictBilateralSource.sourceRadius = 2 := by
  simp [strictBilateralSource,
    BilateralSourceIncidence.ofFourArcCandidate,
    FourArcCandidate.assembly, FourArcCandidate.stripCore,
    StripCore.radius, CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
    CMVSourceClassification.RawFourArcCoordinates.curvature, strictRaw]

@[simp] theorem endpointBilateralSource_sourceRadius :
    endpointBilateralSource.sourceRadius = 1 := by
  simp [endpointBilateralSource,
    BilateralSourceIncidence.ofFourArcCandidate,
    FourArcCandidate.assembly, FourArcCandidate.stripCore,
    StripCore.radius, CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
    CMVSourceClassification.RawFourArcCoordinates.curvature, endpointRaw]

/-- The existing source-side scalar consumer accepts the strict actual
specimen. -/
theorem strictBilateralSource_derivedRadius :
    1 ≤ strictBilateralSource.sourceRadius :=
  strictBilateralSource.derived_sourceRadius_ge_one

/-- The same source-side scalar consumer reaches the exact endpoint specimen. -/
theorem endpointBilateralSource_derivedRadius :
    1 ≤ endpointBilateralSource.sourceRadius :=
  endpointBilateralSource.derived_sourceRadius_ge_one

/-- The endpoint actual source reaches the unchanged closed-Snell coordinate
consumer, not a separate raw-only argument. -/
theorem endpointBilateralSource_satisfiesClosedSnell :
    endpointBilateralSource.toRawFourArcCoordinates.SatisfiesClosedSnell 2 :=
  endpointBilateralSource.toRawFourArcCoordinates_satisfiesClosedSnell

/-- Arbitrary horizontal placement of the strict specimen. -/
def strictBilateralSourceAt (t : ℝ) : BilateralSourceIncidence 2 :=
  strictBilateralSource.horizontalTranslate t

/-- Arbitrary horizontal placement of the endpoint specimen. -/
def endpointBilateralSourceAt (t : ℝ) : BilateralSourceIncidence 2 :=
  endpointBilateralSource.horizontalTranslate t

@[simp] theorem strictBilateralSourceAt_sourceRadius (t : ℝ) :
    (strictBilateralSourceAt t).sourceRadius = 2 := by
  simp [strictBilateralSourceAt,
    BilateralSourceIncidence.horizontalTranslate]

@[simp] theorem endpointBilateralSourceAt_sourceRadius (t : ℝ) :
    (endpointBilateralSourceAt t).sourceRadius = 1 := by
  simp [endpointBilateralSourceAt,
    BilateralSourceIncidence.horizontalTranslate]

@[simp] theorem strictBilateralSourceAt_symmetryAxisX (t : ℝ) :
    (strictBilateralSourceAt t).symmetryAxisX =
      strictBilateralSource.symmetryAxisX + t := by
  simp [strictBilateralSourceAt]

@[simp] theorem endpointBilateralSourceAt_symmetryAxisX (t : ℝ) :
    (endpointBilateralSourceAt t).symmetryAxisX =
      endpointBilateralSource.symmetryAxisX + t := by
  simp [endpointBilateralSourceAt]

/-- Every translated strict specimen carries the producer-derived reflection;
no reflection premise is supplied by the example. -/
theorem strictBilateralSourceAt_rightStripCenter_reflection (t : ℝ) :
    (strictBilateralSourceAt t).rightStripCenter =
      verticalReflection (strictBilateralSourceAt t).symmetryAxisX
        (strictBilateralSourceAt t).leftStripCenter :=
  (strictBilateralSourceAt t).rightStripCenter_reflection

/-- Every translated endpoint specimen also carries the producer-derived
reflection, including at exact source radius one. -/
theorem endpointBilateralSourceAt_rightStripCenter_reflection (t : ℝ) :
    (endpointBilateralSourceAt t).rightStripCenter =
      verticalReflection (endpointBilateralSourceAt t).symmetryAxisX
        (endpointBilateralSourceAt t).leftStripCenter :=
  (endpointBilateralSourceAt t).rightStripCenter_reflection

end Examples
end CMVFigureFour
