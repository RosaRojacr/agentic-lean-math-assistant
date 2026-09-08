/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneFirstCellSource
import SameCurvatureArea

/-!
# Strict reduced-gap sign in the first near-one cell

This module rewrites the reduced perimeter gap in principal tangent-half-angle
coordinates, removes its exact fourth-order cusp zero by polynomial division,
and proves that the resulting endpoint value is negative on the complete first
cell.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open scoped Topology
open Filter

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

/-- The reduced radical gap after replacing all square roots by their positive
principal tangent-half-angle expressions. -/
def sourceReducedGap (s z a b : ℝ) : ℝ :=
  let h₃ := (1 + halfCos (wCoord s a)) / 2
  let h₄ := halfCos s
  (h₃ - h₄) / h₄ *
      (1 / halfSin s - 1 / halfSin (yCoord s z)) +
    h₃ / h₄ * (halfSin (yCoord s z) - halfSin s) -
    (halfSin (vCoord s z a b) - halfSin (wCoord s a))

/-- A positive clearing denominator for `sourceReducedGap` on the endpoint
chart. -/
def reducedGapDenominator (s z a b : ℝ) : ℝ :=
  2 * aCoord s z * (1 + wCoord s a ^ 2) * (1 - s ^ 2) *
    (1 + yCoord s z ^ 2) * (1 + vCoord s z a b ^ 2)

/-- After the universal `s²` cancellation in the reduced gap, this polynomial
is the remaining numerator. -/
def reducedGapNumeratorBar (s z a b : ℝ) : ℝ :=
  let A := aCoord s z
  let R := rCoord s a
  let E := eCoord s z a b
  let Y := yCoord s z
  let W := wCoord s a
  let V := vCoord s z a b
  (2 - R ^ 2 + s ^ 2 * R ^ 2) * z * (1 - s ^ 2 * A) *
      (1 + Y ^ 2) * (1 + V ^ 2) +
    4 * z * (1 - s ^ 2 * A) * A * (1 + V ^ 2) -
    4 * E * (1 - V * W) * A * (1 - s ^ 2) * (1 + Y ^ 2)

set_option maxHeartbeats 0 in
-- Clearing the nested rational half-angle expressions exceeds the default budget.
/-- Exact rational clearing of the source reduced gap. -/
theorem reducedGap_clearing_identity {s z a b : ℝ}
    (hs : s ≠ 0) (hA : aCoord s z ≠ 0) (hsOne : 1 - s ^ 2 ≠ 0) :
    reducedGapDenominator s z a b * sourceReducedGap s z a b =
      s ^ 2 * reducedGapNumeratorBar s z a b := by
  have hA' : 1 + s * z ≠ 0 := by
    simpa only [aCoord] using hA
  unfold reducedGapDenominator sourceReducedGap reducedGapNumeratorBar
  simp only [halfCos, halfSin, yCoord, wCoord, vCoord, aCoord, rCoord,
    eCoord]
  field_simp [hs, hA', hsOne]
  ring

/-- Polynomial lift of `reducedGapNumeratorBar` along the exact physical
`tangentCenteredPoint s (s²q)` path. -/
def reducedGapBarPathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  let Z := rescaledZPathPolynomial q
  let Aphys := rescaledAPathPolynomial q
  let Bphys := rescaledBPathPolynomial q
  let A := 1 + X * Z
  let R := 2 + X * Aphys
  let E := 6 * Aphys - 2 * Z + X * Bphys
  let Y := X * A
  let W := X * R
  let V := X * (R + X * E)
  (2 - R ^ 2 + X ^ 2 * R ^ 2) * Z * (1 - X ^ 2 * A) *
      (1 + Y ^ 2) * (1 + V ^ 2) +
    4 * Z * (1 - X ^ 2 * A) * A * (1 + V ^ 2) -
    4 * E * (1 - V * W) * A * (1 - X ^ 2) * (1 + Y ^ 2)

set_option maxHeartbeats 0 in
-- Normalizing the lifted degree-33 polynomial exceeds the default budget.
/-- Evaluating the lifted polynomial gives the actual numerator bar. -/
theorem reducedGapBarPathPolynomial_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (reducedGapBarPathPolynomial q).eval s =
      reducedGapNumeratorBar s (endpointPhysicalPoint s q 0)
        (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) := by
  simp [reducedGapBarPathPolynomial, reducedGapNumeratorBar,
    endpointPhysicalPoint, aCoord, rCoord, eCoord, yCoord, wCoord, vCoord]

/-- The lifted reduced-gap numerator has no constant term. -/
theorem reducedGapBarPathPolynomial_coeff_zero (q : Fin 3 → ℝ) :
    (reducedGapBarPathPolynomial q).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [reducedGapBarPathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial]
  ring

set_option maxHeartbeats 0 in
-- Differentiating and normalizing the lifted polynomial exceeds the default budget.
/-- The tangent-centered path also cancels the linear term. -/
theorem reducedGapBarPathPolynomial_coeff_one (q : Fin 3 → ℝ) :
    (reducedGapBarPathPolynomial q).coeff 1 = 0 := by
  let p := reducedGapBarPathPolynomial q
  have hcoeff : p.derivative.coeff 0 = p.coeff 1 := by
    simpa using coeff_derivative p 0
  rw [← hcoeff, coeff_zero_eq_eval_zero]
  simp [p, reducedGapBarPathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial, derivative_pow]
  ring

set_option maxHeartbeats 0 in
-- The exact second-coefficient calculation exceeds the default budget.
/-- Exact fourth-order endpoint coefficient of the cleared reduced gap. -/
theorem reducedGapBarPathPolynomial_coeff_two (q : Fin 3 → ℝ) :
    (reducedGapBarPathPolynomial q).coeff 2 =
      (108288 * π - 2087 * π ^ 3 - 10368 * q 1) / 432 := by
  let p := reducedGapBarPathPolynomial q
  have hcoeff : p.derivative.derivative.coeff 0 = 2 * p.coeff 2 := by
    rw [coeff_derivative, coeff_derivative]
    norm_num
    ring
  rw [← show p.derivative.derivative.coeff 0 / 2 = p.coeff 2 by
    rw [hcoeff]
    ring, coeff_zero_eq_eval_zero]
  simp [p, reducedGapBarPathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial, derivative_pow]
  ring

/-- Double exact division by `X` removes the remaining tangent-path zero. -/
theorem X_sq_mul_reducedGapBarPathPolynomial_divX_divX
    (q : Fin 3 → ℝ) :
    X ^ 2 * (reducedGapBarPathPolynomial q).divX.divX =
      reducedGapBarPathPolynomial q := by
  have h0 := reducedGapBarPathPolynomial_coeff_zero q
  have h1 := reducedGapBarPathPolynomial_coeff_one q
  have hd0 : ((reducedGapBarPathPolynomial q).divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h1
  have hx1 :
      X * (reducedGapBarPathPolynomial q).divX.divX =
        (reducedGapBarPathPolynomial q).divX := by
    simpa [hd0] using X_mul_divX_add (reducedGapBarPathPolynomial q).divX
  have hx0 :
      X * (reducedGapBarPathPolynomial q).divX =
        reducedGapBarPathPolynomial q := by
    simpa [h0] using X_mul_divX_add (reducedGapBarPathPolynomial q)
  calc
    X ^ 2 * (reducedGapBarPathPolynomial q).divX.divX =
        X * (X * (reducedGapBarPathPolynomial q).divX.divX) := by
          simp [pow_two, mul_assoc]
    _ = X * (reducedGapBarPathPolynomial q).divX := by rw [hx1]
    _ = reducedGapBarPathPolynomial q := hx0

/-- Pole-free fourth-order rescaling of the cleared reduced gap. -/
def poleFreeReducedGap (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  ((reducedGapBarPathPolynomial q).divX.divX).eval s

/-- Exact factorization of the numerator bar along the rescaled path. -/
theorem reducedGapNumeratorBar_rescaled_factorization
    (s : ℝ) (q : Fin 3 → ℝ) :
    reducedGapNumeratorBar s (endpointPhysicalPoint s q 0)
        (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) =
      s ^ 2 * poleFreeReducedGap s q := by
  rw [← reducedGapBarPathPolynomial_eval]
  have hrecon :=
    X_sq_mul_reducedGapBarPathPolynomial_divX_divX q
  have heval := congrArg (fun p : ℝ[X] => p.eval s) hrecon
  simpa only [eval_mul, eval_pow, eval_X, poleFreeReducedGap] using heval.symm

/-- Exact endpoint value of the pole-free reduced gap. -/
@[simp] theorem poleFreeReducedGap_zero (q : Fin 3 → ℝ) :
    poleFreeReducedGap 0 q =
      (108288 * π - 2087 * π ^ 3 - 10368 * q 1) / 432 := by
  change (reducedGapBarPathPolynomial q).divX.divX.eval 0 = _
  rw [← coeff_zero_eq_eval_zero, coeff_divX, coeff_divX]
  simpa using reducedGapBarPathPolynomial_coeff_two q


private theorem halfSin_pos {x : ℝ} (hx : 0 < x) :
    0 < halfSin x := by
  unfold halfSin
  positivity

private theorem halfCos_sq_add_halfSin_sq (x : ℝ) :
    halfCos x ^ 2 + halfSin x ^ 2 = 1 := by
  unfold halfCos halfSin
  field_simp
  ring

private theorem sqrt_one_sub_halfCos_sq {x : ℝ} (hx : 0 < x) :
    sqrt (1 - halfCos x ^ 2) = halfSin x := by
  rw [show 1 - halfCos x ^ 2 = halfSin x ^ 2 by
    linarith [halfCos_sq_add_halfSin_sq x],
    Real.sqrt_sq_eq_abs, abs_of_pos (halfSin_pos hx)]

private theorem sqrt_sq_sub_halfCos_sq {lam x h : ℝ}
    (hlam : 0 < lam) (hx : 0 < x)
    (hrel : h = lam * halfCos x) :
    sqrt (lam ^ 2 - h ^ 2) = lam * halfSin x := by
  rw [show lam ^ 2 - h ^ 2 = (lam * halfSin x) ^ 2 by
    rw [hrel]
    calc
      lam ^ 2 - (lam * halfCos x) ^ 2 =
          lam ^ 2 * (1 - halfCos x ^ 2) := by ring
      _ = lam ^ 2 * halfSin x ^ 2 := by
        rw [show 1 - halfCos x ^ 2 = halfSin x ^ 2 by
          linarith [halfCos_sq_add_halfSin_sq x]]
      _ = (lam * halfSin x) ^ 2 := by ring,
    Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam (halfSin_pos hx))]

/-- On the positive principal chart, the analytic reduced radical gap is
exactly its rational source-coordinate form. -/
theorem reducedFoldGap_eq_sourceReducedGap {s z a b : ℝ}
    (hs0 : 0 < s)
    (hy0 : 0 < yCoord s z) (hy1 : yCoord s z < 1)
    (hw0 : 0 < wCoord s a) (hv0 : 0 < vCoord s z a b)
    (hlam : 1 < density s z)
    (hcosine : sourceCosineResidual s z a b = 0) :
    LeanSuffixAnalytic.reducedFoldGap (density s z)
        ((1 + halfCos (wCoord s a)) / 2) (halfCos s) =
      sourceReducedGap s z a b := by
  have hlamPos : 0 < density s z := lt_trans (by norm_num) hlam
  have hcosYPos : 0 < halfCos (yCoord s z) := by
    unfold halfCos
    exact div_pos (by nlinarith) (by positivity)
  have hcosXY :
      halfCos s = density s z * halfCos (yCoord s z) := by
    rw [density]
    field_simp [ne_of_gt hcosYPos]
  have hcosWV :
      halfCos (wCoord s a) =
        density s z * halfCos (vCoord s z a b) := by
    unfold sourceCosineResidual at hcosine
    rw [hcosXY] at hcosine
    nlinarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape
          ((1 + halfCos (wCoord s a)) / 2) =
        halfCos (wCoord s a) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hsqrtS :
      sqrt (1 - halfCos s ^ 2) = halfSin s :=
    sqrt_one_sub_halfCos_sq hs0
  have hsqrtW :
      sqrt (1 - halfCos (wCoord s a) ^ 2) =
        halfSin (wCoord s a) :=
    sqrt_one_sub_halfCos_sq hw0
  have hsqrtLamS :
      sqrt (density s z ^ 2 - halfCos s ^ 2) =
        density s z * halfSin (yCoord s z) :=
    sqrt_sq_sub_halfCos_sq hlamPos hy0 hcosXY
  have hsqrtLamW :
      sqrt (density s z ^ 2 - halfCos (wCoord s a) ^ 2) =
        density s z * halfSin (vCoord s z a b) :=
    sqrt_sq_sub_halfCos_sq hlamPos hv0 hcosWV
  unfold LeanSuffixAnalytic.reducedFoldGap
    LeanSuffixAnalytic.typeFourDelta LeanSuffixAnalytic.typeThreeDelta
    sourceReducedGap
  rw [hshape, hsqrtS, hsqrtW, hsqrtLamS, hsqrtLamW]
  field_simp [ne_of_gt hlamPos]

private def GapCC {α : Type*} [TopologicalSpace α]
    (P : α → ℝ[X]) : Prop :=
  ∀ n, Continuous (fun x => (P x).coeff n)

private lemma gapCC_const {α : Type*} [TopologicalSpace α] (p : ℝ[X]) :
    GapCC (fun _ : α => p) := fun _ => continuous_const

private lemma gapCC_C {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : GapCC (fun x => C (f x)) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hf
  · simp only [coeff_C, if_neg hn]
    exact continuous_const

private lemma gapCC_add {α : Type*} [TopologicalSpace α]
    {P Q : α → ℝ[X]} (hP : GapCC P) (hQ : GapCC Q) :
    GapCC (fun x => P x + Q x) := by
  intro n
  change Continuous (fun x => (P x).coeff n + (Q x).coeff n)
  exact (hP n).add (hQ n)

private lemma gapCC_neg {α : Type*} [TopologicalSpace α]
    {P : α → ℝ[X]} (hP : GapCC P) : GapCC (fun x => -P x) := by
  intro n
  change Continuous (fun x => -(P x).coeff n)
  exact (hP n).neg

private lemma gapCC_sub {α : Type*} [TopologicalSpace α]
    {P Q : α → ℝ[X]} (hP : GapCC P) (hQ : GapCC Q) :
    GapCC (fun x => P x - Q x) := by
  simpa only [sub_eq_add_neg] using gapCC_add hP (gapCC_neg hQ)

private lemma gapCC_mul {α : Type*} [TopologicalSpace α]
    {P Q : α → ℝ[X]} (hP : GapCC P) (hQ : GapCC Q) :
    GapCC (fun x => P x * Q x) := by
  intro n
  simp_rw [coeff_mul]
  exact continuous_finsetSum _ fun k _ => (hP k.1).mul (hQ k.2)

private lemma gapCC_pow {α : Type*} [TopologicalSpace α]
    {P : α → ℝ[X]} (hP : GapCC P) (n : ℕ) :
    GapCC (fun x => P x ^ n) := by
  induction n with
  | zero =>
      simpa using
        (gapCC_const (1 : ℝ[X]) : GapCC (fun _ : α => (1 : ℝ[X])))
  | succ n ih => simpa [pow_succ] using gapCC_mul ih hP

private lemma gapCC_divX {α : Type*} [TopologicalSpace α]
    {P : α → ℝ[X]} (hP : GapCC P) :
    GapCC (fun x => (P x).divX) := by
  intro n
  simpa only [coeff_divX] using hP (n + 1)

set_option maxHeartbeats 0 in
-- Elaborating coefficientwise continuity of the degree-33 expression exceeds the default budget.
private lemma reducedGapBarPathPolynomial_gapCC :
    GapCC reducedGapBarPathPolynomial := by
  let Z := rescaledZPathPolynomial
  let Aphys := rescaledAPathPolynomial
  let Bphys := rescaledBPathPolynomial
  let A := fun q => 1 + X * Z q
  let R := fun q => 2 + X * Aphys q
  let E := fun q => 6 * Aphys q - 2 * Z q + X * Bphys q
  let Y := fun q => X * A q
  let W := fun q => X * R q
  let V := fun q => X * (R q + X * E q)
  have hZ : GapCC Z := by
    exact gapCC_add
      (gapCC_add (gapCC_const _) (gapCC_mul (gapCC_const _) (gapCC_const _)))
      (gapCC_mul (gapCC_C (continuous_apply 0)) (gapCC_const _))
  have hAphys : GapCC Aphys := by
    exact gapCC_add
      (gapCC_add (gapCC_const _) (gapCC_mul (gapCC_const _) (gapCC_const _)))
      (gapCC_mul (gapCC_C (by fun_prop)) (gapCC_const _))
  have hBphys : GapCC Bphys := by
    exact gapCC_add
      (gapCC_add (gapCC_const _) (gapCC_mul (gapCC_const _) (gapCC_const _)))
      (gapCC_mul (gapCC_C (by fun_prop)) (gapCC_const _))
  have hA : GapCC A :=
    gapCC_add (gapCC_const _) (gapCC_mul (gapCC_const _) hZ)
  have hR : GapCC R :=
    gapCC_add (gapCC_const _) (gapCC_mul (gapCC_const _) hAphys)
  have hE : GapCC E :=
    gapCC_add
      (gapCC_sub (gapCC_mul (gapCC_const _) hAphys)
        (gapCC_mul (gapCC_const _) hZ))
      (gapCC_mul (gapCC_const _) hBphys)
  have hY : GapCC Y := gapCC_mul (gapCC_const _) hA
  have hW : GapCC W := gapCC_mul (gapCC_const _) hR
  have hV : GapCC V :=
    gapCC_mul (gapCC_const _)
      (gapCC_add hR (gapCC_mul (gapCC_const _) hE))
  have hFirstGrouped : GapCC (fun q =>
      ((2 - R q ^ 2 + X ^ 2 * R q ^ 2) * Z q *
        (1 - X ^ 2 * A q)) *
          ((1 + Y q ^ 2) * (1 + V q ^ 2))) :=
    gapCC_mul
      (gapCC_mul
        (gapCC_mul
          (gapCC_add
            (gapCC_sub (gapCC_const _) (gapCC_pow hR 2))
            (gapCC_mul (gapCC_const _) (gapCC_pow hR 2)))
          hZ)
        (gapCC_sub (gapCC_const _)
          (gapCC_mul (gapCC_const _) hA)))
      (gapCC_mul
        (gapCC_add (gapCC_const _) (gapCC_pow hY 2))
        (gapCC_add (gapCC_const _) (gapCC_pow hV 2)))
  have hFirst : GapCC (fun q =>
      (2 - R q ^ 2 + X ^ 2 * R q ^ 2) * Z q *
        (1 - X ^ 2 * A q) * (1 + Y q ^ 2) * (1 + V q ^ 2)) := by
    simpa only [mul_assoc] using hFirstGrouped
  have hSecond : GapCC (fun q =>
      4 * Z q * (1 - X ^ 2 * A q) * A q * (1 + V q ^ 2)) :=
    gapCC_mul
      (gapCC_mul
        (gapCC_mul
          (gapCC_mul (gapCC_const _) hZ)
          (gapCC_sub (gapCC_const _)
            (gapCC_mul (gapCC_const _) hA)))
        hA)
      (gapCC_add (gapCC_const _) (gapCC_pow hV 2))
  have hThird : GapCC (fun q =>
      4 * E q * (1 - V q * W q) * A q * (1 - X ^ 2) *
        (1 + Y q ^ 2)) :=
    gapCC_mul
      (gapCC_mul
        (gapCC_mul
          (gapCC_mul
            (gapCC_mul (gapCC_const _) hE)
            (gapCC_sub (gapCC_const _) (gapCC_mul hV hW)))
          hA)
        (gapCC_const _))
      (gapCC_add (gapCC_const _) (gapCC_pow hY 2))
  have hAll := gapCC_sub (gapCC_add hFirst hSecond) hThird
  unfold GapCC at hAll ⊢
  intro n
  simpa only [reducedGapBarPathPolynomial, Z, Aphys, Bphys, A, R, E, Y, W, V]
    using hAll n

private def GapDegree (p : ℝ[X]) (n : ℕ) : Prop := p.natDegree ≤ n

private lemma gapDegree_nat (n : ℕ) : GapDegree (n : ℝ[X]) 0 := by
  simp [GapDegree]

private lemma gapDegree_X : GapDegree (X : ℝ[X]) 1 := by
  simp [GapDegree]

private lemma gapDegree_add {p q : ℝ[X]} {m n : ℕ}
    (hp : GapDegree p m) (hq : GapDegree q n) :
    GapDegree (p + q) (max m n) :=
  natDegree_add_le p q |>.trans <| max_le_max hp hq

private lemma gapDegree_sub {p q : ℝ[X]} {m n : ℕ}
    (hp : GapDegree p m) (hq : GapDegree q n) :
    GapDegree (p - q) (max m n) :=
  natDegree_sub_le p q |>.trans <| max_le_max hp hq

private lemma gapDegree_mul {p q : ℝ[X]} {m n : ℕ}
    (hp : GapDegree p m) (hq : GapDegree q n) :
    GapDegree (p * q) (m + n) :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private lemma gapDegree_pow {p : ℝ[X]} {m : ℕ}
    (hp : GapDegree p m) (n : ℕ) :
    GapDegree (p ^ n) (n * m) :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left n hp)

private lemma gapDegree_C (x : ℝ) : GapDegree (C x) 0 := by
  simp [GapDegree]

private lemma gapDegree_rescaledZ (q : Fin 3 → ℝ) :
    GapDegree (rescaledZPathPolynomial q) 2 := by
  unfold rescaledZPathPolynomial
  unfold GapDegree
  compute_degree

private lemma gapDegree_rescaledA (q : Fin 3 → ℝ) :
    GapDegree (rescaledAPathPolynomial q) 2 := by
  unfold rescaledAPathPolynomial
  unfold GapDegree
  compute_degree

private lemma gapDegree_rescaledB (q : Fin 3 → ℝ) :
    GapDegree (rescaledBPathPolynomial q) 2 := by
  unfold rescaledBPathPolynomial
  unfold GapDegree
  compute_degree

private lemma reducedGapBarPathPolynomial_degree (q : Fin 3 → ℝ) :
    (reducedGapBarPathPolynomial q).natDegree < 34 := by
  let Z := rescaledZPathPolynomial q
  let Aphys := rescaledAPathPolynomial q
  let Bphys := rescaledBPathPolynomial q
  let A := 1 + X * Z
  let R := 2 + X * Aphys
  let E := 6 * Aphys - 2 * Z + X * Bphys
  let Y := X * A
  let W := X * R
  let V := X * (R + X * E)
  have hZ : GapDegree Z 2 := gapDegree_rescaledZ q
  have hAphys : GapDegree Aphys 2 := gapDegree_rescaledA q
  have hBphys : GapDegree Bphys 2 := gapDegree_rescaledB q
  have hA : GapDegree A 3 := by
    have h := gapDegree_add (gapDegree_nat 1)
      (gapDegree_mul gapDegree_X hZ)
    norm_num at h ⊢
    exact h
  have hR : GapDegree R 3 := by
    have h := gapDegree_add (gapDegree_nat 2)
      (gapDegree_mul gapDegree_X hAphys)
    norm_num at h ⊢
    exact h
  have hE : GapDegree E 3 := by
    have h := gapDegree_add
      (gapDegree_sub
        (gapDegree_mul (gapDegree_nat 6) hAphys)
        (gapDegree_mul (gapDegree_nat 2) hZ))
      (gapDegree_mul gapDegree_X hBphys)
    norm_num at h ⊢
    exact h
  have hY : GapDegree Y 4 := by
    simpa using gapDegree_mul gapDegree_X hA
  have hW : GapDegree W 4 := by
    simpa using gapDegree_mul gapDegree_X hR
  have hV : GapDegree V 5 := by
    have h := gapDegree_mul gapDegree_X
      (gapDegree_add hR (gapDegree_mul gapDegree_X hE))
    norm_num at h ⊢
    exact h
  have hF : GapDegree (2 - R ^ 2 + X ^ 2 * R ^ 2) 8 := by
    have h := gapDegree_add
      (gapDegree_sub (gapDegree_nat 2) (gapDegree_pow hR 2))
      (gapDegree_mul (gapDegree_pow gapDegree_X 2) (gapDegree_pow hR 2))
    norm_num at h ⊢
    exact h
  have hT : GapDegree (1 - X ^ 2 * A) 5 := by
    have h := gapDegree_sub (gapDegree_nat 1)
      (gapDegree_mul (gapDegree_pow gapDegree_X 2) hA)
    norm_num at h ⊢
    exact h
  have hYsq : GapDegree (1 + Y ^ 2) 8 := by
    have h := gapDegree_add (gapDegree_nat 1) (gapDegree_pow hY 2)
    norm_num at h ⊢
    exact h
  have hVsq : GapDegree (1 + V ^ 2) 10 := by
    have h := gapDegree_add (gapDegree_nat 1) (gapDegree_pow hV 2)
    norm_num at h ⊢
    exact h
  have hFirst : GapDegree
      ((2 - R ^ 2 + X ^ 2 * R ^ 2) * Z *
        (1 - X ^ 2 * A) * (1 + Y ^ 2) * (1 + V ^ 2)) 33 := by
    have h := gapDegree_mul
      (gapDegree_mul (gapDegree_mul (gapDegree_mul hF hZ) hT) hYsq) hVsq
    norm_num at h ⊢
    exact h
  have hSecond : GapDegree
      (4 * Z * (1 - X ^ 2 * A) * A * (1 + V ^ 2)) 20 := by
    have h := gapDegree_mul
      (gapDegree_mul
        (gapDegree_mul (gapDegree_mul (gapDegree_nat 4) hZ) hT) hA) hVsq
    norm_num at h ⊢
    exact h
  have hThird : GapDegree
      (4 * E * (1 - V * W) * A * (1 - X ^ 2) * (1 + Y ^ 2)) 25 := by
    have hVW : GapDegree (1 - V * W) 9 := by
      have h := gapDegree_sub (gapDegree_nat 1) (gapDegree_mul hV hW)
      norm_num at h ⊢
      exact h
    have hOne : GapDegree (1 - X ^ 2) 2 := by
      have h := gapDegree_sub (gapDegree_nat 1) (gapDegree_pow gapDegree_X 2)
      norm_num at h ⊢
      exact h
    have h := gapDegree_mul
      (gapDegree_mul
        (gapDegree_mul
          (gapDegree_mul (gapDegree_mul (gapDegree_nat 4) hE) hVW) hA)
          hOne)
      hYsq
    norm_num at h ⊢
    exact h
  have hAll := gapDegree_sub (gapDegree_add hFirst hSecond) hThird
  dsimp only [GapDegree] at hAll
  change (let Z := rescaledZPathPolynomial q
    let Aphys := rescaledAPathPolynomial q
    let Bphys := rescaledBPathPolynomial q
    let A := 1 + X * Z
    let R := 2 + X * Aphys
    let E := 6 * Aphys - 2 * Z + X * Bphys
    let Y := X * A
    let W := X * R
    let V := X * (R + X * E)
    ((2 - R ^ 2 + X ^ 2 * R ^ 2) * Z * (1 - X ^ 2 * A) *
      (1 + Y ^ 2) * (1 + V ^ 2) +
      4 * Z * (1 - X ^ 2 * A) * A * (1 + V ^ 2) -
      4 * E * (1 - V * W) * A * (1 - X ^ 2) *
        (1 + Y ^ 2)).natDegree < 34)
  dsimp only
  exact hAll.trans_lt (by norm_num)

/-- The pole-free reduced-gap rescaling is jointly continuous in the scale and
all endpoint-box coordinates. -/
theorem continuous_poleFreeReducedGap_joint :
    Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
      poleFreeReducedGap p.1 p.2) := by
  have hcoeff : GapCC (fun q =>
      (reducedGapBarPathPolynomial q).divX.divX) :=
    gapCC_divX (gapCC_divX reducedGapBarPathPolynomial_gapCC)
  rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
      poleFreeReducedGap p.1 p.2) =
      fun p => ∑ n ∈ Finset.range 34,
        ((reducedGapBarPathPolynomial p.2).divX.divX).coeff n *
          p.1 ^ n by
    funext p
    unfold poleFreeReducedGap
    have hd : (reducedGapBarPathPolynomial p.2).divX.divX.natDegree < 34 := calc
      _ ≤ (reducedGapBarPathPolynomial p.2).divX.natDegree :=
        natDegree_divX_le
      _ ≤ (reducedGapBarPathPolynomial p.2).natDegree :=
        natDegree_divX_le
      _ < 34 := reducedGapBarPathPolynomial_degree p.2
    rw [eval_eq_sum_range' hd]]
  exact continuous_finsetSum _ fun n _ =>
    ((hcoeff n).comp continuous_snd).mul (continuous_fst.pow n)

/-- The endpoint coefficient is strictly negative on the complete rational
box. -/
theorem poleFreeReducedGap_zero_neg (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : poleFreeReducedGap 0 q < 0 := by
  rw [poleFreeReducedGap_zero]
  have hq1 := hq (1 : Fin 3)
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
  have hpihi := Real.pi_lt_d20
  norm_num at hp3lo hpihi ⊢
  nlinarith

private lemma endpointBox_isCompact_gap :
    IsCompact {q : Fin 3 → ℝ | InEndpointBox q} := by
  rw [show {q : Fin 3 → ℝ | InEndpointBox q} =
      Set.pi Set.univ
        (fun i => Set.Icc (endpointBoxLower i) (endpointBoxUpper i)) by
    ext q
    simp only [InEndpointBox, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, true_implies]]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

private lemma compact_eventually_gap_neg
    {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    {f : ℝ × (Fin 3 → ℝ) → ℝ} (hf : Continuous f)
    (h0 : ∀ q ∈ K, f (0, q) < 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q ∈ K, f (s, q) < 0 := by
  let U : Set ((Fin 3 → ℝ) × ℝ) := {p | f (p.2, p.1) < 0}
  have hUlocal : ∀ q ∈ K, U ∈ 𝓝 q ×ˢ 𝓝 (0 : ℝ) := by
    intro q hq
    rw [← nhds_prod_eq]
    exact ((hf.comp (by fun_prop :
        Continuous (fun p : (Fin 3 → ℝ) × ℝ => (p.2, p.1)))).continuousAt
      |>.eventually_lt_const (h0 q hq))
  have hU : U ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ) :=
    hK.mem_nhdsSet_prod_of_forall hUlocal
  rcases mem_prod_iff.mp hU with ⟨V, hV, W, hW, hVW⟩
  filter_upwards [hW] with s hs
  intro q hq
  have hqs : (q, s) ∈ V ×ˢ W :=
    ⟨subset_of_mem_nhdsSet hV hq, hs⟩
  exact hVW hqs

/-- The negative reduced-gap sign persists uniformly on the complete endpoint
box near the cusp. -/
theorem eventually_poleFreeReducedGap_neg :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q, InEndpointBox q →
      poleFreeReducedGap s q < 0 :=
  compact_eventually_gap_neg endpointBox_isCompact_gap
    continuous_poleFreeReducedGap_joint
    (fun q hq => poleFreeReducedGap_zero_neg q hq)

/-- One reciprocal-natural slice simultaneously carries all six root-map face
signs and the strict reduced-gap sign on the entire endpoint box. -/
theorem exists_positive_rational_all_face_cell_gap :
    ∃ n : ℕ,
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ HasEndpointBoxFaceSigns s ∧
        ∀ q, InEndpointBox q → poleFreeReducedGap s q < 0 := by
  have hboth : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasEndpointBoxFaceSigns s ∧
        ∀ q, InEndpointBox q → poleFreeReducedGap s q < 0 :=
    eventually_all_face_cell.and eventually_poleFreeReducedGap_neg
  have hseq : ∀ᶠ n : ℕ in atTop,
      (HasEndpointBoxFaceSigns (1 / (n + 1 : ℝ)) ∧
        ∀ q, InEndpointBox q →
          poleFreeReducedGap (1 / (n + 1 : ℝ)) q < 0) ∧
        1 / (n + 1 : ℝ) < 1 / 100 :=
    tendsto_one_div_add_atTop_nhds_zero_nat
      (hboth.and
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100)))
  rcases Filter.Eventually.exists hseq with ⟨n, hn⟩
  exact ⟨n, by positivity, hn.2, hn.1.1, hn.1.2⟩

/-- Poincare--Miranda on the strengthened slice gives a simultaneous root at
which the pole-free reduced gap is negative. -/
theorem positive_rational_rescaled_all_rows_root_gap :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        poleFreeReducedGap s q < 0 := by
  rcases exists_positive_rational_all_face_cell_gap with
    ⟨n, hs0, hs, hfaces, hgap⟩
  obtain ⟨q, hq, hroot⟩ :=
    rescaled_all_rows_root_of_face_signs hs0 hs hfaces
  exact ⟨n, q, hs0, hs, hq, hroot, hgap q hq⟩

/-- Negativity of the pole-free rescaling is equivalent to negativity of the
source reduced gap on a positive endpoint-box slice. -/
theorem sourceReducedGap_neg_of_poleFree {s : ℝ} {q : Fin 3 → ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (hq : InEndpointBox q)
    (hgap : poleFreeReducedGap s q < 0) :
    sourceReducedGap s (endpointPhysicalPoint s q 0)
        (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) < 0 := by
  let z := endpointPhysicalPoint s q 0
  let a := endpointPhysicalPoint s q 1
  let b := endpointPhysicalPoint s q 2
  rcases endpointBox_coordinate_bounds hs0 hs q hq with
    ⟨⟨_, hsy, hy1⟩, ⟨hw0, hwv, hv1⟩, _⟩
  have hy0 : 0 < yCoord s z := lt_trans hs0 hsy
  have hApos : 0 < aCoord s z := by
    by_contra h
    have hnonpos : aCoord s z ≤ 0 := le_of_not_gt h
    have : yCoord s z ≤ 0 := by
      rw [yCoord]
      exact mul_nonpos_of_nonneg_of_nonpos hs0.le hnonpos
    linarith
  have hsSq : s ^ 2 < 1 := by nlinarith
  have hdenPos : 0 < reducedGapDenominator s z a b := by
    unfold reducedGapDenominator
    positivity
  have hbarNeg :
      s ^ 2 * reducedGapNumeratorBar s z a b < 0 := by
    rw [show reducedGapNumeratorBar s z a b =
        s ^ 2 * poleFreeReducedGap s q by
      simpa only [z, a, b] using
        reducedGapNumeratorBar_rescaled_factorization s q]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hs0)
      (mul_neg_of_pos_of_neg (sq_pos_of_pos hs0) hgap)
  have hprod :
      reducedGapDenominator s z a b * sourceReducedGap s z a b < 0 := by
    rw [reducedGap_clearing_identity (ne_of_gt hs0) (ne_of_gt hApos)
      (ne_of_gt (sub_pos.mpr hsSq))]
    exact hbarNeg
  by_contra h
  have hnonneg : 0 ≤ sourceReducedGap s z a b := le_of_not_gt h
  have := mul_nonneg hdenPos.le hnonneg
  linarith


private theorem endpointPhysicalPoint_one_pos {s : ℝ}
    (hs0 : 0 < s) (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    0 < endpointPhysicalPoint s q 1 := by
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  have hqA : 0 < 5 * q 0 / 12 + q 1 := by
    nlinarith [hq0.1, hq1.1]
  rw [show endpointPhysicalPoint s q 1 = 5 * π / 12 +
      s * ((43 * π ^ 2 + 1056) / 144) +
      s ^ 2 * (5 * q 0 / 12 + q 1) by
    simp [endpointPhysicalPoint, tangentCenteredPoint, exactCuspPoint,
      exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
    ring]
  positivity

/-- Throughout the first endpoint box, the type-(iii) curvature is strictly
below the stationary type-(iv) curvature. -/
theorem endpointBox_height_order {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (1 + halfCos (wCoord s (endpointPhysicalPoint s q 1))) / 2 <
      halfCos s := by
  let a := endpointPhysicalPoint s q 1
  let w := wCoord s a
  have ha0 : 0 < a := by
    simpa only [a] using endpointPhysicalPoint_one_pos hs0 q hq
  have hw : 2 * s < w := by
    dsimp only [w]
    unfold wCoord rCoord
    nlinarith [mul_pos hs0 ha0]
  have hw0 : 0 < w := lt_trans (mul_pos (by norm_num) hs0) hw
  have hsq : 4 * s ^ 2 < w ^ 2 := by nlinarith
  have hsSqHalf : s ^ 2 < (1 / 2 : ℝ) := by nlinarith
  have hfactor : (1 / 2 : ℝ) < 1 - s ^ 2 := by linarith
  have hprod : w ^ 2 / 2 < w ^ 2 * (1 - s ^ 2) := by
    have := mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hw0)
    nlinarith
  have hmain : 2 * s ^ 2 < w ^ 2 * (1 - s ^ 2) := by
    nlinarith
  change (1 + halfCos w) / 2 < halfCos s
  rw [show (1 + halfCos w) / 2 = 1 / (1 + w ^ 2) by
    unfold halfCos
    field_simp
    ring]
  unfold halfCos
  rw [div_lt_div_iff₀ (by positivity : 0 < 1 + w ^ 2)
    (by positivity : 0 < 1 + s ^ 2)]
  nlinarith
/-- A simultaneous rescaled root with negative pole-free gap at any sufficiently
small positive scale produces a stationary equal-area pair on the negative
type-(iii) fold branch with strict perimeter improvement. -/
theorem stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
    {s : ℝ} {q : Fin 3 → ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (hq : InEndpointBox q)
    (hrootRescaled : rescaledOrientedNearOneMap s q = 0)
    (hgapPoleFree : poleFreeReducedGap s q < 0) :
    let x := endpointPhysicalPoint s q
    ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (density s (x 0)),
      pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
      pair.h₄ = halfCos s ∧
      1 < density s (x 0) ∧ density s (x 0) < (51 / 50 : ℝ) ∧
      LeanSuffixAnalytic.typeThreeFold
          (density s (x 0)) pair.h₃ < 0 ∧
      LeanSuffixAnalytic.reducedFoldGap
          (density s (x 0)) pair.h₃ pair.h₄ < 0 ∧
      LeanSuffixAnalytic.typeThreePerimeter
          (density s (x 0)) pair.h₃ <
        LeanSuffixAnalytic.typeFourPerimeter
          (density s (x 0)) pair.h₄ := by
  let x := endpointPhysicalPoint s q
  have hroot : nearOneRootMap s π x = 0 := by
    apply (rescaledOrientedNearOneMap_eq_zero_iff (ne_of_gt hs0) q).mp
    simpa only [x, endpointPhysicalPoint] using hrootRescaled
  have hfold : foldRow s (x 0) π = 0 := by
    have h := congrFun hroot (0 : Fin 3)
    simpa [nearOneRootMap] using h
  have hcosine : (NearOneNormalizedFlow.H2 (x 0) (x 1) (x 2)).eval s = 0 := by
    have h := congrFun hroot (1 : Fin 3)
    simpa [nearOneRootMap] using h
  have harea : regularizedThirdRow s (x 0) (x 1) (x 2) π = 0 := by
    have h := congrFun hroot (2 : Fin 3)
    simpa [nearOneRootMap] using h
  rcases endpointBox_principalChart hs0 hs q hq with
    ⟨hySq, hdenFour, haddFour, hdenThree, haddThree⟩
  rcases endpointBox_coordinate_bounds hs0 hs q hq with
    ⟨⟨_, hsy, hy1⟩, ⟨hw0, hwv, hv1⟩, hlam, hlam51⟩
  have hfoldSource : sourceFoldResidual s (x 0) π = 0 := by
    apply (sourceFoldResidual_eq_zero_iff_complete s (x 0) π
      (ne_of_gt hs0) (ne_of_gt (sub_pos.mpr hySq)) hdenFour haddFour).mpr
    exact (foldRow_eq_zero_iff s (x 0) π).mp hfold
  have hcosineSource : sourceCosineResidual s (x 0) (x 1) (x 2) = 0 :=
    (sourceCosineResidual_eq_zero_iff_H2 s (x 0) (x 1) (x 2)
      (ne_of_gt hs0) hySq).mpr hcosine
  have hareaSource : sourceAreaResidual s (x 0) (x 1) (x 2) π = 0 :=
    (sourceAreaResidual_eq_zero_iff_regularizedThirdRow
      s (x 0) (x 1) (x 2) π (ne_of_gt hs0) hySq hdenFour haddFour
        hdenThree haddThree hfoldSource hcosineSource).mpr harea
  have hy0 : 0 < yCoord s (x 0) := lt_trans hs0 hsy
  have hw1 : wCoord s (x 1) < 1 := lt_trans hwv hv1
  have hv0 : 0 < vCoord s (x 0) (x 1) (x 2) := lt_trans hw0 hwv
  let pair :=
    sourceResiduals_stationaryEqualAreaPair
      hs0 (lt_trans hs (by norm_num)) hy0 hy1 hw0 hw1 hv0 hlam
        hfoldSource hcosineSource hareaSource
  have hsourceGap :
      sourceReducedGap s (x 0) (x 1) (x 2) < 0 := by
    simpa only [x] using
      sourceReducedGap_neg_of_poleFree hs0 hs hq hgapPoleFree
  have hgap :
      LeanSuffixAnalytic.reducedFoldGap
          (density s (x 0)) pair.h₃ pair.h₄ < 0 := by
    change LeanSuffixAnalytic.reducedFoldGap (density s (x 0))
      ((1 + halfCos (wCoord s (x 1))) / 2) (halfCos s) < 0
    rw [reducedFoldGap_eq_sourceReducedGap hs0
      hy0 hy1 hw0 hv0 hlam hcosineSource]
    exact hsourceGap
  have hheight : pair.h₃ < pair.h₄ := by
    rw [show pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 from rfl,
      show pair.h₄ = halfCos s from rfl]
    simpa only [x] using endpointBox_height_order hs0 hs q hq
  have hfoldThree :
      LeanSuffixAnalytic.typeThreeFold
          (density s (x 0)) pair.h₃ < 0 :=
    LeanSuffixAnalytic.typeThreeFold_neg_of_equalArea_of_lt
      hlam ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
        ⟨pair.h₄_pos, pair.h₄_lt_one⟩ hheight pair.equalArea
  have hperimeter :
      LeanSuffixAnalytic.typeThreePerimeter
          (density s (x 0)) pair.h₃ <
        LeanSuffixAnalytic.typeFourPerimeter
          (density s (x 0)) pair.h₄ :=
    (LeanSuffixAnalytic.stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).2 hgap
  exact ⟨pair, rfl, rfl, hlam, hlam51,
    hfoldThree, hgap, hperimeter⟩

/-- The first validated positive cell contains an actual stationary equal-area
pair on the negative type-(iii) fold branch with a strict perimeter
improvement. -/
theorem positive_rational_stationaryEqualAreaPair_strictImprovement :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      let x := endpointPhysicalPoint s q
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (density s (x 0)),
          pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
          pair.h₄ = halfCos s ∧
          1 < density s (x 0) ∧ density s (x 0) < (51 / 50 : ℝ) ∧
          LeanSuffixAnalytic.typeThreeFold
              (density s (x 0)) pair.h₃ < 0 ∧
          LeanSuffixAnalytic.reducedFoldGap
              (density s (x 0)) pair.h₃ pair.h₄ < 0 ∧
          LeanSuffixAnalytic.typeThreePerimeter
              (density s (x 0)) pair.h₃ <
            LeanSuffixAnalytic.typeFourPerimeter
              (density s (x 0)) pair.h₄ := by
  rcases positive_rational_rescaled_all_rows_root_gap with
    ⟨n, q, hs0, hs, hq, hrootRescaled, hgapPoleFree⟩
  refine ⟨n, q, hs0, hs, hq, ?_⟩
  exact stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
    hs0 hs hq hrootRescaled hgapPoleFree

/-- Every sufficiently small positive scale has a simultaneous first-cell root
whose stationary equal-area pair lies on the negative type-(iii) fold branch
and strictly improves the type-(iv) perimeter. -/
theorem exists_epsilon_stationaryEqualAreaPair_strictImprovement :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε →
      ∃ q : Fin 3 → ℝ,
        let x := endpointPhysicalPoint s q
        InEndpointBox q ∧ rescaledOrientedNearOneMap s q = 0 ∧
          ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair
              (density s (x 0)),
            pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
            pair.h₄ = halfCos s ∧
            1 < density s (x 0) ∧
            density s (x 0) < (51 / 50 : ℝ) ∧
            LeanSuffixAnalytic.typeThreeFold
                (density s (x 0)) pair.h₃ < 0 ∧
            LeanSuffixAnalytic.reducedFoldGap
                (density s (x 0)) pair.h₃ pair.h₄ < 0 ∧
            LeanSuffixAnalytic.typeThreePerimeter
                (density s (x 0)) pair.h₃ <
              LeanSuffixAnalytic.typeFourPerimeter
                (density s (x 0)) pair.h₄ := by
  have hgood : ∀ᶠ s in 𝓝 (0 : ℝ),
      s < (1 / 100 : ℝ) ∧ HasEndpointBoxFaceSigns s ∧
        (∀ q, InEndpointBox q → poleFreeReducedGap s q < 0) :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100)).and
      (eventually_all_face_cell.and eventually_poleFreeReducedGap_neg)
  rcases Metric.mem_nhds_iff.mp hgood with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro s hs0 hsε
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hs0] using hsε
  rcases hball hsball with ⟨hs, hfaces, hgap⟩
  obtain ⟨q, hq, hroot⟩ :=
    rescaled_all_rows_root_of_face_signs hs0 hs hfaces
  refine ⟨q, hq, hroot, ?_⟩
  exact stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
    hs0 hs hq hroot (hgap q hq)

end NearOneRescaledFirstCell

end

end NearOneRegularizedThirdRow
