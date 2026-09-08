/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenQuadratic

/-!
# Exact cubic divisibility of the cleared frozen third-row path
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

/-- Exact cubic divisibility of the cleared frozen-path error. -/
theorem X_cube_mul_frozenPathClearedError_divX_divX_divX
    (q : Fin 3 → ℝ) :
    X ^ 3 * (frozenPathClearedError q).divX.divX.divX =
      frozenPathClearedError q := by
  have h0 := frozenPathClearedError_coeff_zero q
  have h1 := frozenPathClearedError_coeff_one q
  have h2 := frozenPathClearedError_coeff_two q
  have hd0 : ((frozenPathClearedError q).divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h1
  have hd1 : ((frozenPathClearedError q).divX.divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h2
  have hx2 :
      X * (frozenPathClearedError q).divX.divX.divX =
        (frozenPathClearedError q).divX.divX := by
    simpa [hd1] using X_mul_divX_add (frozenPathClearedError q).divX.divX
  have hx1 :
      X * (frozenPathClearedError q).divX.divX =
        (frozenPathClearedError q).divX := by
    simpa [hd0] using X_mul_divX_add (frozenPathClearedError q).divX
  have hx0 :
      X * (frozenPathClearedError q).divX =
        frozenPathClearedError q := by
    simpa [h0] using X_mul_divX_add (frozenPathClearedError q)
  calc
    X ^ 3 * (frozenPathClearedError q).divX.divX.divX =
        X * (X * (X *
          (frozenPathClearedError q).divX.divX.divX)) := by
      simp [pow_succ, mul_assoc]
    _ = X * (X * (frozenPathClearedError q).divX.divX) := by rw [hx2]
    _ = X * (frozenPathClearedError q).divX := by rw [hx1]
    _ = frozenPathClearedError q := hx0

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
