/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourBoundaryRigidity
import CMVAEOpenRepresentative
import CMVTypeThreeSourceExclusion

/-!
# Source exclusion from Figure-4 boundary rigidity

Boundary-only reconstruction identifies the bounded open representative with the
literal raw target interior.  Complete-frontier planar nullity then upgrades
that exact representative equality to almost-everywhere agreement between the
actual source and the closed raw carrier.  The existing recovered type-(iii)
consumer excludes that source at every admissible density.
-/

open Set MeasureTheory

noncomputable section

namespace CMVFigureFour.SourceGeometry

open CMVFigureFourTargetGeometry
open CMVRelaxation
open CMVRelaxation.TypeThreeSourceExclusion

variable {lam : ℝ} (g : SourceGeometry lam)

/-- Every frozen Figure-4 actual source agrees almost everywhere with its
closed, horizontally placed raw target.  The actual source itself need not be
bounded; only the stored open representative is used by boundary rigidity. -/
theorem sourceCarrier_ae_raw_carrier :
    g.sourceCarrier =ᵐ[volume] g.toRawFourArcCoordinates.carrier := by
  have hrepresentative :
      g.representative =ᵐ[volume]
        interior g.toRawFourArcCoordinates.carrier :=
    Filter.EventuallyEq.of_eq g.representative_eq_interior_raw_carrier
  exact g.sourceRepresentative.source_ae_representative.trans
    (hrepresentative.trans
      (CMVFigureFourTargetGeometry.RawFourArcCoordinates.interior_carrier_ae_eq_carrier
        g.toRawFourArcCoordinates
        g.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry))

/-- Boundary-only Figure-4 reconstruction feeds the unchanged all-density raw
closed-geometric non-minimizer consumer.  No source boundedness, normalization,
recovery, finiteness, compatibility, model coverage, section, or frontier
premise is supplied by the caller. -/
theorem sourceCarrier_not_isMinimizer :
    ¬ (relaxedSourceSemantics lam).IsMinimizer g.sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_ae_rawFourArcClassification
    g.density_jump
    ⟨g.toRawFourArcCoordinates,
      g.toRawFourArcCoordinates_satisfiesClosedSnell.toGeometry,
      g.sourceCarrier_ae_raw_carrier⟩

/-- Any carrier in the same planar measure class as a frozen Figure-4 source is
also excluded.  This is the consumer needed by a GMT classifier, which naturally
produces almost-everywhere rather than pointwise carrier identification. -/
theorem aeEquivalentCarrier_not_isMinimizer
    {E : Set PlanePoint} (hE : E =ᵐ[volume] g.sourceCarrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer E := by
  intro hmin
  exact g.sourceCarrier_not_isMinimizer
    ((relaxedSourceSemantics_isMinimizer_congr_ae lam hE).mp hmin)

end CMVFigureFour.SourceGeometry

namespace CMVFigureFour.BilateralSourceIncidence

open CMVRelaxation

variable {lam : ℝ} (g : BilateralSourceIncidence lam)

/-- The symmetry-free bilateral source producer inherits the exact same
almost-everywhere closed-target reconstruction through `toSourceGeometry`. -/
theorem sourceCarrier_ae_raw_carrier :
    g.sourceCarrier =ᵐ[volume] g.toRawFourArcCoordinates.carrier :=
  g.toSourceGeometry.sourceCarrier_ae_raw_carrier

/-- Every bilateral Figure-4 source satisfying the frozen primitive incidence
signature is excluded at every admissible density, including source radius one. -/
theorem sourceCarrier_not_isMinimizer :
    ¬ (relaxedSourceSemantics lam).IsMinimizer g.sourceCarrier :=
  g.toSourceGeometry.sourceCarrier_not_isMinimizer

/-- The symmetry-free bilateral producer has the same measure-class consumer;
universal classification need only identify its carrier almost everywhere. -/
theorem aeEquivalentCarrier_not_isMinimizer
    {E : Set PlanePoint} (hE : E =ᵐ[volume] g.sourceCarrier) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer E :=
  g.toSourceGeometry.aeEquivalentCarrier_not_isMinimizer hE

end CMVFigureFour.BilateralSourceIncidence
