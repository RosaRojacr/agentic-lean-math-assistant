/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRightSideExhaustion

/-!
# Closed-curvature four-arc patch gate

The shared four-arc upper-cap and right-side exhaustions specialized to the
literal `h = 1`, `alpha = arccos (1 / lambda)` candidate.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section


namespace CMVRelaxation

/-- Shared upper-cap patches on the literal closed-curvature candidate.  The
windows and both collars belong to `RigidProjectionPatch` over the literal
assembly carrier; the family charges one global smooth cost. -/
theorem exists_endpoint_upperCap_patch_family_and_bound
    {lam eta : ℝ} (hlam : 1 < lam) (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
        RigidProjectionPatch lam (FourArcCandidate.endpoint hlam).assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = lam) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal (2 * lam * Real.arccos (1 / lam)) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U
                (FourArcCandidate.endpoint hlam).assembly.carrier := by
  simpa only [FourArcCandidate.endpoint_upperCap_weightedArcLength hlam] using
    (FourArcUpperCap.exists_upperCap_patch_family_and_bound
      (FourArcCandidate.endpoint hlam) hlam heta)

/-- Shared right-side patches on the literal closed-curvature candidate.  Every
window lies strictly right of the cap chord and strictly inside the strip, and
the family charges one global smooth cost. -/
theorem exists_endpoint_rightSide_patch_family_and_bound
    {lam eta : ℝ} (hlam : 1 < lam) (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
        RigidProjectionPatch lam (FourArcCandidate.endpoint hlam).assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = 1) ∧
      (∀ i, (P i).window ⊆
        {p : PlanePoint |
          (FourArcCandidate.endpoint hlam).capChord / 2 < p.1 ∧ |p.2| < 1}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal Real.pi ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U
                (FourArcCandidate.endpoint hlam).assembly.carrier := by
  simpa only [FourArcCandidate.endpoint_rightSide_arcLength hlam] using
    (FourArcRightSide.exists_rightSide_patch_family_and_bound
      (FourArcCandidate.endpoint hlam) heta)

end CMVRelaxation
