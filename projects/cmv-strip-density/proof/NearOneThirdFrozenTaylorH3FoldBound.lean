/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenTaylorMajorantAlgebra

/-! # Taylor certificate for the fold branch of the frozen H3 majorant -/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell
section FrozenPolynomial
namespace FrozenTaylorMajorant

open TaylorMajorant

/-- The `16 * fold` branch after the two H3 normalization shifts. -/
def h3FoldRaw (q : Fin 3 → ℝ) (hq : InEndpointBox q) :=
  ((nat 16).mul (algFold (z q hq))).divXTwo

/-- Exact nonnegative polynomial carried by the shifted fold branch. -/
def h3FoldMajorantPolynomial : ℝ[X] :=
  Polynomial.C 2080 + Polynomial.C 4480 * Polynomial.X +
    Polynomial.C 4864 * Polynomial.X ^ 2 +
    Polynomial.C 14976 * Polynomial.X ^ 3 +
    Polynomial.C 30560 * Polynomial.X ^ 4 +
    Polynomial.C 57664 * Polynomial.X ^ 5 +
    Polynomial.C 27648 * Polynomial.X ^ 6 +
    Polynomial.C 46656 * Polynomial.X ^ 7

private theorem divX_X_mul (p : ℝ[X]) : (Polynomial.X * p).divX = p := by
  ext n
  simp [Polynomial.coeff_divX]

@[simp] private theorem divX_X_real :
    (Polynomial.X : ℝ[X]).divX = 1 := by
  simpa using (Polynomial.divX_X_pow (R := ℝ) (n := 1))
set_option maxHeartbeats 0 in
theorem h3FoldRaw_majorant_eq (q : Fin 3 → ℝ) (hq : InEndpointBox q) :

    (h3FoldRaw q hq).pm.majorant = h3FoldMajorantPolynomial := by
  change (((nat 16).mul (algFold (z q hq))).pm.majorant).divX.divX =
    h3FoldMajorantPolynomial
  rw [show ((nat 16).mul (algFold (z q hq))).pm.majorant =
      Polynomial.C 128 + Polynomial.X * Polynomial.C 512 +
        Polynomial.X * (Polynomial.X * h3FoldMajorantPolynomial) by
    simp [algFold, algFoldRaw, algA, algAraw, z, piC, one, nat,
      oneSubX2, oneAddX2, TaylorMajorant.reindex,
      TaylorMajorant.boundedC, TaylorMajorant.C, TaylorMajorant.X,
      TaylorMajorant.add, TaylorMajorant.neg, TaylorMajorant.sub,
      TaylorMajorant.mul, TaylorMajorant.pow,
      PolynomialMajorant.C, PolynomialMajorant.X, PolynomialMajorant.add,
      PolynomialMajorant.neg, PolynomialMajorant.mul,
      NearOneRescaledFirstCell.boundedC,
      Polynomial.C_ofNat, h3FoldMajorantPolynomial]
    ring]
  simp [Polynomial.divX_add, divX_X_mul]

private theorem h3FoldRaw_bounds (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (h3FoldRaw q hq).taylor.b0 ≤ 2080 ∧
    (h3FoldRaw q hq).taylor.b1 ≤ 4480 ∧
    (h3FoldRaw q hq).taylor.b2 ≤ 4864 ∧
    (h3FoldRaw q hq).taylor.b3 ≤ 14976 ∧
    (h3FoldRaw q hq).taylor.remainder ≤ 30561 := by
  change (h3FoldRaw q hq).pm.majorant.coeff 0 ≤ 2080 ∧
    (h3FoldRaw q hq).pm.majorant.coeff 1 ≤ 4480 ∧
    (h3FoldRaw q hq).pm.majorant.coeff 2 ≤ 4864 ∧
    (h3FoldRaw q hq).pm.majorant.coeff 3 ≤ 14976 ∧
    (h3FoldRaw q hq).pm.majorant.divX.divX.divX.divX.eval
      cubicTaylorRadius ≤ 30561
  rw [h3FoldRaw_majorant_eq]
  simp [h3FoldMajorantPolynomial, cubicTaylorRadius, divX_X_real,
    Polynomial.divX_add, Polynomial.divX_X_pow] <;> norm_num

/-- Rationally widened fold-branch Taylor certificate. -/
def h3Fold (q : Fin 3 → ℝ) (hq : InEndpointBox q) := by
  rcases h3FoldRaw_bounds q hq with ⟨h0, h1, h2, h3, hr⟩
  exact (h3FoldRaw q hq).widen 2080 4480 4864 14976 30561
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    h0 h1 h2 h3 hr

end FrozenTaylorMajorant
end FrozenPolynomial
end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
