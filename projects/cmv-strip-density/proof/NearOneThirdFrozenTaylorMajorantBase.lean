/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenMajorantCore
import NearOneCertifiedCubicTaylorBound

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell
section FrozenPolynomial
namespace FrozenTaylorMajorant

abbrev CT (p : ℝ[X]) := CertifiedCubicTaylorBound p

private theorem eval_eq_cubic_add_tail (p : ℝ[X]) (s : ℝ) :
    p.eval s = p.coeff 0 + p.coeff 1 * s + p.coeff 2 * s ^ 2 +
      p.coeff 3 * s ^ 3 + s ^ 4 * p.divX.divX.divX.divX.eval s := by
  have h0 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p)
  have h1 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p.divX)
  have h2 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p.divX.divX)
  have h3 := congrArg (Polynomial.eval s)
    (Polynomial.X_mul_divX_add p.divX.divX.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX] at h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, ← h3]
  ring

/-- Exact Taylor certificate for a nonnegative-coefficient polynomial. -/
def ofNonnegative (p : ℝ[X]) (hp : ∀ k, 0 ≤ p.coeff k) : CT p where
  toCubicTaylorBound := {
    c0 := p.coeff 0
    c1 := p.coeff 1
    c2 := p.coeff 2
    c3 := p.coeff 3
    b0 := p.coeff 0
    b1 := p.coeff 1
    b2 := p.coeff 2
    b3 := p.coeff 3
    remainder := p.divX.divX.divX.divX.eval cubicTaylorRadius
    b0_nonneg := hp 0
    b1_nonneg := hp 1
    b2_nonneg := hp 2
    b3_nonneg := hp 3
    remainder_nonneg := by
      let P : PolynomialMajorant p := {
        majorant := p
        coeff_nonneg := hp
        coeff_abs_le := fun k => by rw [abs_of_nonneg (hp k)] }
      have h := P.divX.divX.divX.divX.abs_eval_le_eval_abs cubicTaylorRadius
      have ha : 0 ≤ |p.divX.divX.divX.divX.eval cubicTaylorRadius| := abs_nonneg _
      rw [abs_of_nonneg cubicTaylorRadius_nonneg] at h
      exact ha.trans h
    abs_c0_le := by rw [abs_of_nonneg (hp 0)]
    abs_c1_le := by rw [abs_of_nonneg (hp 1)]
    abs_c2_le := by rw [abs_of_nonneg (hp 2)]
    abs_c3_le := by rw [abs_of_nonneg (hp 3)]
    remainder_bound := by
      intro s hs
      let P : PolynomialMajorant p := {
        majorant := p
        coeff_nonneg := hp
        coeff_abs_le := fun k => by rw [abs_of_nonneg (hp k)] }
      have htail := P.divX.divX.divX.divX.abs_eval_le_eval_of_abs_le hs
      have htail' :
          |p.divX.divX.divX.divX.eval s| ≤
            p.divX.divX.divX.divX.eval cubicTaylorRadius := by
        simpa [P, PolynomialMajorant.divX] using htail
      rw [eval_eq_cubic_add_tail]
      rw [show p.coeff 0 + p.coeff 1 * s + p.coeff 2 * s ^ 2 +
          p.coeff 3 * s ^ 3 + s ^ 4 * p.divX.divX.divX.divX.eval s -
          (p.coeff 0 + p.coeff 1 * s + p.coeff 2 * s ^ 2 +
            p.coeff 3 * s ^ 3) = s ^ 4 * p.divX.divX.divX.divX.eval s by ring]
      rw [abs_mul, abs_pow]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left htail' (pow_nonneg (abs_nonneg s) 4) }
  c0_eq_coeff := rfl
  c1_eq_coeff := rfl

  c2_eq_coeff := rfl
  c3_eq_coeff := rfl
@[simp] theorem cast_certified_b0 {p q : ℝ[X]} (h : p = q) (P : CT p) :
    (cast (congrArg CT h) P).b0 = P.b0 := by subst q; rfl
@[simp] theorem cast_certified_b1 {p q : ℝ[X]} (h : p = q) (P : CT p) :
    (cast (congrArg CT h) P).b1 = P.b1 := by subst q; rfl
@[simp] theorem cast_certified_b2 {p q : ℝ[X]} (h : p = q) (P : CT p) :
    (cast (congrArg CT h) P).b2 = P.b2 := by subst q; rfl
@[simp] theorem cast_certified_b3 {p q : ℝ[X]} (h : p = q) (P : CT p) :
    (cast (congrArg CT h) P).b3 = P.b3 := by subst q; rfl
@[simp] theorem cast_certified_remainder {p q : ℝ[X]} (h : p = q) (P : CT p) :
    (cast (congrArg CT h) P).remainder = P.remainder := by subst q; rfl

@[simp] theorem certified_pow_b0_zero {p : ℝ[X]} (P : CT p) :
    (P.pow 0).b0 = 1 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.const,
    CubicTaylorBound.const]

@[simp] theorem certified_pow_b1_zero {p : ℝ[X]} (P : CT p) :
    (P.pow 0).b1 = 0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.const,
    CubicTaylorBound.const]

@[simp] theorem certified_pow_b2_zero {p : ℝ[X]} (P : CT p) :
    (P.pow 0).b2 = 0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.const,
    CubicTaylorBound.const]

@[simp] theorem certified_pow_b3_zero {p : ℝ[X]} (P : CT p) :
    (P.pow 0).b3 = 0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.const,
    CubicTaylorBound.const]

@[simp] theorem certified_pow_remainder_zero {p : ℝ[X]} (P : CT p) :
    (P.pow 0).remainder = 0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.const,
    CubicTaylorBound.const]

@[simp] theorem certified_pow_b0_succ {p : ℝ[X]} (P : CT p) (k : ℕ) :
    (P.pow (k + 1)).b0 = (P.pow k).b0 * P.b0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.mul,
    CubicTaylorBound.mul]

@[simp] theorem certified_pow_b1_succ {p : ℝ[X]} (P : CT p) (k : ℕ) :
    (P.pow (k + 1)).b1 =
      (P.pow k).b0 * P.b1 + (P.pow k).b1 * P.b0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.mul,
    CubicTaylorBound.mul]

@[simp] theorem certified_pow_b2_succ {p : ℝ[X]} (P : CT p) (k : ℕ) :
    (P.pow (k + 1)).b2 =
      (P.pow k).b0 * P.b2 + (P.pow k).b1 * P.b1 +
        (P.pow k).b2 * P.b0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.mul,
    CubicTaylorBound.mul]

@[simp] theorem certified_pow_b3_succ {p : ℝ[X]} (P : CT p) (k : ℕ) :
    (P.pow (k + 1)).b3 =
      (P.pow k).b0 * P.b3 + (P.pow k).b1 * P.b2 +
        (P.pow k).b2 * P.b1 + (P.pow k).b3 * P.b0 := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.mul,
    CubicTaylorBound.mul]

@[simp] theorem certified_pow_remainder_succ {p : ℝ[X]} (P : CT p) (k : ℕ) :
    (P.pow (k + 1)).remainder =
      (P.pow k).bound.productRemainder P.bound := by
  simp [CertifiedCubicTaylorBound.pow, CertifiedCubicTaylorBound.mul,
    CubicTaylorBound.mul]

/-- A coefficient majorant bundled with a compositional Taylor certificate for
its majorant polynomial. -/
structure TaylorMajorant (p : ℝ[X]) where
  pm : PolynomialMajorant p
  taylor : CT pm.majorant

@[simp] theorem cast_taylorMajorant_pm_majorant {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).pm.majorant = P.pm.majorant := by
  subst q
  rfl

@[simp] theorem cast_taylorMajorant_b0 {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).taylor.b0 = P.taylor.b0 := by
  subst q
  rfl

@[simp] theorem cast_taylorMajorant_b1 {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).taylor.b1 = P.taylor.b1 := by
  subst q
  rfl

@[simp] theorem cast_taylorMajorant_b2 {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).taylor.b2 = P.taylor.b2 := by
  subst q
  rfl

@[simp] theorem cast_taylorMajorant_b3 {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).taylor.b3 = P.taylor.b3 := by
  subst q
  rfl

@[simp] theorem cast_taylorMajorant_remainder {p q : ℝ[X]} (h : p = q)
    (P : TaylorMajorant p) :
    (cast (congrArg TaylorMajorant h) P).taylor.remainder =
      P.taylor.remainder := by
  subst q
  rfl


namespace TaylorMajorant

/-- Reindex a bundled majorant along a polynomial identity without changing
its majorant polynomial or Taylor data. -/
def reindex {p q : ℝ[X]} (P : TaylorMajorant p) (h : p = q) :
    TaylorMajorant q where
  pm := {
    majorant := P.pm.majorant
    coeff_nonneg := P.pm.coeff_nonneg
    coeff_abs_le := by
      intro n
      rw [← h]
      exact P.pm.coeff_abs_le n }
  taylor := P.taylor

@[simp] theorem reindex_pm_majorant {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).pm.majorant = P.pm.majorant := by
  subst q
  rfl

@[simp] theorem reindex_b0 {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).taylor.b0 = P.taylor.b0 := by
  subst q
  rfl

@[simp] theorem reindex_b1 {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).taylor.b1 = P.taylor.b1 := by
  subst q
  rfl

@[simp] theorem reindex_b2 {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).taylor.b2 = P.taylor.b2 := by
  subst q
  rfl

@[simp] theorem reindex_b3 {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).taylor.b3 = P.taylor.b3 := by
  subst q
  rfl

@[simp] theorem reindex_remainder {p q : ℝ[X]} (P : TaylorMajorant p)
    (h : p = q) : (P.reindex h).taylor.remainder =
      P.taylor.remainder := by
  subst q
  rfl

def boundedC (a M : ℝ) (hM : 0 ≤ M) (h : |a| ≤ M) : TaylorMajorant (C a) :=
  ⟨NearOneRescaledFirstCell.boundedC a M hM h,
    CertifiedCubicTaylorBound.const M⟩

def C (a : ℝ) : TaylorMajorant (Polynomial.C a) :=
  ⟨PolynomialMajorant.C a, CertifiedCubicTaylorBound.const |a|⟩

def X : TaylorMajorant (Polynomial.X : ℝ[X]) :=
  ⟨PolynomialMajorant.X, CertifiedCubicTaylorBound.X⟩

def add {p q : ℝ[X]} (P : TaylorMajorant p) (Q : TaylorMajorant q) :
    TaylorMajorant (p + q) :=
  ⟨P.pm.add Q.pm, P.taylor.add Q.taylor⟩

def neg {p : ℝ[X]} (P : TaylorMajorant p) : TaylorMajorant (-p) :=
  ⟨P.pm.neg, P.taylor⟩

def sub {p q : ℝ[X]} (P : TaylorMajorant p) (Q : TaylorMajorant q) :
    TaylorMajorant (p - q) :=
  P.add Q.neg

def mul {p q : ℝ[X]} (P : TaylorMajorant p) (Q : TaylorMajorant q) :
    TaylorMajorant (p * q) :=
  ⟨P.pm.mul Q.pm, P.taylor.mul Q.taylor⟩

@[simp] private theorem cast_pm_majorant {p q : ℝ[X]} (h : p = q)
    (P : PolynomialMajorant p) :
    (cast (congrArg PolynomialMajorant h) P).majorant = P.majorant := by
  subst q
  rfl

private theorem pm_pow_majorant {p : ℝ[X]} (P : PolynomialMajorant p) (k : ℕ) :
    (P.pow k).majorant = P.majorant ^ k := by
  induction k with
  | zero => simp [PolynomialMajorant.pow, PolynomialMajorant.C,
      cast_pm_majorant]
  | succ k ih =>
      simp [PolynomialMajorant.pow, PolynomialMajorant.mul, ih, pow_succ,
        cast_pm_majorant]

def pow {p : ℝ[X]} (P : TaylorMajorant p) (k : ℕ) :
    TaylorMajorant (p ^ k) where
  pm := {
    majorant := P.pm.majorant ^ k
    coeff_nonneg := by
      intro n
      simpa only [pm_pow_majorant] using (P.pm.pow k).coeff_nonneg n
    coeff_abs_le := by
      intro n
      simpa only [pm_pow_majorant] using (P.pm.pow k).coeff_abs_le n }
  taylor := P.taylor.pow k

/-- Dividing twice is used only at the normalized H3 node; exact certification
there avoids propagating a high-order numerator remainder through a shift. -/
def divXTwo {p : ℝ[X]} (P : TaylorMajorant p) :
    TaylorMajorant p.divX.divX :=
  ⟨P.pm.divX.divX,
    ofNonnegative P.pm.majorant.divX.divX (fun k => by
      simpa only [Polynomial.coeff_divX, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using P.pm.coeff_nonneg (k + 2))⟩

def widen {p : ℝ[X]} (P : TaylorMajorant p)
    (b0 b1 b2 b3 remainder : ℝ)
    (hb0_nonneg : 0 ≤ b0) (hb1_nonneg : 0 ≤ b1)
    (hb2_nonneg : 0 ≤ b2) (hb3_nonneg : 0 ≤ b3)
    (hremainder_nonneg : 0 ≤ remainder)
    (hb0 : P.taylor.b0 ≤ b0) (hb1 : P.taylor.b1 ≤ b1)
    (hb2 : P.taylor.b2 ≤ b2) (hb3 : P.taylor.b3 ≤ b3)
    (hremainder : P.taylor.remainder ≤ remainder) : TaylorMajorant p :=
  ⟨P.pm, P.taylor.widen b0 b1 b2 b3 remainder hb0_nonneg hb1_nonneg
    hb2_nonneg hb3_nonneg hremainder_nonneg hb0 hb1 hb2 hb3 hremainder⟩

@[simp] theorem boundedC_pm_majorant (a M : ℝ) (hM : 0 ≤ M)
    (h : |a| ≤ M) :
    (boundedC a M hM h).pm.majorant = Polynomial.C M := rfl

@[simp] theorem C_pm_majorant (a : ℝ) :
    (C a).pm.majorant = Polynomial.C |a| := rfl

@[simp] theorem X_pm_majorant :
    TaylorMajorant.X.pm.majorant = (Polynomial.X : ℝ[X]) := rfl

@[simp] theorem add_pm_majorant {p q : ℝ[X]} (P : TaylorMajorant p)
    (Q : TaylorMajorant q) :
    (P.add Q).pm.majorant = P.pm.majorant + Q.pm.majorant := rfl

@[simp] theorem neg_pm_majorant {p : ℝ[X]} (P : TaylorMajorant p) :
    P.neg.pm.majorant = P.pm.majorant := rfl

@[simp] theorem sub_pm_majorant {p q : ℝ[X]} (P : TaylorMajorant p)
    (Q : TaylorMajorant q) :
    (P.sub Q).pm.majorant = P.pm.majorant + Q.pm.majorant := rfl

@[simp] theorem mul_pm_majorant {p q : ℝ[X]} (P : TaylorMajorant p)
    (Q : TaylorMajorant q) :
    (P.mul Q).pm.majorant = P.pm.majorant * Q.pm.majorant := rfl

@[simp] theorem pow_pm_majorant {p : ℝ[X]} (P : TaylorMajorant p) (k : ℕ) :
    (P.pow k).pm.majorant = P.pm.majorant ^ k := rfl

@[simp] theorem divXTwo_pm_majorant {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.pm.majorant = P.pm.majorant.divX.divX := rfl

@[simp] theorem divXTwo_b0 {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.taylor.b0 = P.divXTwo.pm.majorant.coeff 0 := rfl

@[simp] theorem divXTwo_b1 {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.taylor.b1 = P.divXTwo.pm.majorant.coeff 1 := rfl

@[simp] theorem divXTwo_b2 {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.taylor.b2 = P.divXTwo.pm.majorant.coeff 2 := rfl

@[simp] theorem divXTwo_b3 {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.taylor.b3 = P.divXTwo.pm.majorant.coeff 3 := rfl

@[simp] theorem divXTwo_remainder {p : ℝ[X]} (P : TaylorMajorant p) :
    P.divXTwo.taylor.remainder =
      P.divXTwo.pm.majorant.divX.divX.divX.divX.eval cubicTaylorRadius := rfl

end TaylorMajorant

open TaylorMajorant

def one : TaylorMajorant (1 : ℝ[X]) :=
  (TaylorMajorant.C 1).reindex (by norm_num)
def nat (k : ℕ) : TaylorMajorant (k : ℝ[X]) :=
  (TaylorMajorant.C (k : ℝ)).reindex (by simp)
def rational (r : ℝ) : TaylorMajorant (Polynomial.C r) :=
  TaylorMajorant.C r
def oneSubX2 : TaylorMajorant ((1 : ℝ[X]) - Polynomial.X ^ 2) :=
  one.sub (TaylorMajorant.X.pow 2)
def oneAddX2 : TaylorMajorant ((1 : ℝ[X]) + Polynomial.X ^ 2) :=
  one.add (TaylorMajorant.X.pow 2)

/-- The scalar `π` is deliberately widened to `4`, keeping all later data
rational. -/
def piC : TaylorMajorant (Polynomial.C π) :=
  TaylorMajorant.boundedC π 4 (by norm_num) (by
    rw [abs_of_pos Real.pi_pos]
    exact Real.pi_lt_four.le)

/-- Fixed `[4,16,54]` majorant for the endpoint `Z` path. -/
def z (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TaylorMajorant (rescaledZPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0 := hbounds.2.1
  have hpi : |π| ≤ (4 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]; exact Real.pi_lt_four.le
  have hpi2 : |π ^ 2| ≤ (16 : ℝ) := by
    rw [abs_of_nonneg (sq_nonneg π)]
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hq0' : |q 0| ≤ (54 : ℝ) := by
    rw [abs_of_nonneg (by linarith)]
    exact hq0
  exact
    ((TaylorMajorant.boundedC π 4 (by norm_num) hpi).add
      ((TaylorMajorant.boundedC (π ^ 2) 16 (by norm_num) hpi2).mul
        TaylorMajorant.X)).add
      ((TaylorMajorant.boundedC (q 0) 54 (by norm_num) hq0').mul
        (TaylorMajorant.X.pow 2))

/-- Fixed `[2,13,51]` majorant for the endpoint `A` path. -/
def a (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TaylorMajorant (rescaledAPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0lo := hbounds.1
  have hq0hi := hbounds.2.1
  have hq1lo := hbounds.2.2.1
  have hq1hi := hbounds.2.2.2.1
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  have ha0 : |5 * π / 12| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have ha1nonneg : 0 ≤ (43 * π ^ 2 + 1056) / 144 := by positivity
  have ha1 : |(43 * π ^ 2 + 1056) / 144| ≤ (13 : ℝ) := by
    rw [abs_of_nonneg ha1nonneg]; nlinarith [sq_nonneg (π - 4)]
  have ha2nonneg : 0 ≤ 5 * q 0 / 12 + q 1 := by linarith
  have ha2 : |5 * q 0 / 12 + q 1| ≤ (51 : ℝ) := by
    rw [abs_of_nonneg ha2nonneg]
    linarith
  exact
    ((TaylorMajorant.boundedC (5 * π / 12) 2 (by norm_num) ha0).add
      ((TaylorMajorant.boundedC ((43 * π ^ 2 + 1056) / 144) 13
        (by norm_num) ha1).mul TaylorMajorant.X)).add
      ((TaylorMajorant.boundedC (5 * q 0 / 12 + q 1) 51
        (by norm_num) ha2).mul (TaylorMajorant.X.pow 2))

/-- Fixed `[44,270,5200]` majorant for the endpoint `B` path. -/
def b (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TaylorMajorant (rescaledBPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0lo := hbounds.1
  have hq0hi := hbounds.2.1
  have hq1lo := hbounds.2.2.1
  have hq1hi := hbounds.2.2.2.1
  have hq2lo := hbounds.2.2.2.2.1
  have hq2hi := hbounds.2.2.2.2.2
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi3 : 3 ≤ π := Real.pi_gt_three.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  have hbbaseLo : -44 ≤ -44 + 19 * π ^ 2 / 24 := by nlinarith
  have hbbaseHi : -44 + 19 * π ^ 2 / 24 ≤ -31 := by
    norm_num
    nlinarith
  have hblinLo : -270 ≤ π * (295 * π ^ 2 - 14256) / 216 := by
    have hinnerLo : -14256 ≤ 295 * π ^ 2 - 14256 := by nlinarith
    have hinnerHi : 295 * π ^ 2 - 14256 ≤ 0 := by nlinarith
    have hprodLo : -57024 ≤ π * (295 * π ^ 2 - 14256) := by
      calc
        (-57024 : ℝ) = 4 * (-14256) := by norm_num
        _ ≤ π * (-14256) := mul_le_mul_of_nonpos_right hpi4 (by norm_num)
        _ ≤ π * (295 * π ^ 2 - 14256) :=
          mul_le_mul_of_nonneg_left hinnerLo hpi0
    linarith
  have hblinHi : π * (295 * π ^ 2 - 14256) / 216 ≤ 0 := by
    have hi : 295 * π ^ 2 - 14256 ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hpi0 hi) (by norm_num)
  have hcoef0lo : -5376 ≤ 109 * π ^ 2 - 5376 := by nlinarith
  have hcoef0hi : 109 * π ^ 2 - 5376 ≤ 0 := by nlinarith
  have hcoef1lo : 0 ≤ 2880 - 7 * π ^ 2 := by nlinarith
  have hcoef1hi : 2880 - 7 * π ^ 2 ≤ 2880 := by nlinarith
  have hden72 : 0 < 72 * π := by positivity
  have hden6 : 0 < 6 * π := by positivity
  have ht0lo : -1300 ≤ (109 * π ^ 2 - 5376) / (72 * π) * q 0 := by
    have hfrac : -24 ≤ (109 * π ^ 2 - 5376) / (72 * π) := by
      rw [le_div_iff₀ hden72]
      nlinarith
    have hq0nonneg : 0 ≤ q 0 := by linarith
    calc
      (-1300 : ℝ) ≤ -24 * q 0 := by nlinarith
      _ ≤ (109 * π ^ 2 - 5376) / (72 * π) * q 0 :=
        mul_le_mul_of_nonneg_right hfrac hq0nonneg
  have ht0hi : (109 * π ^ 2 - 5376) / (72 * π) * q 0 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hcoef0hi hden72.le) (by linarith)
  have ht1lo : 0 ≤ (2880 - 7 * π ^ 2) / (6 * π) * q 1 :=
    mul_nonneg (div_nonneg hcoef1lo hden6.le) (by linarith)
  have ht1hi : (2880 - 7 * π ^ 2) / (6 * π) * q 1 ≤ 4480 := by
    have hfrac : (2880 - 7 * π ^ 2) / (6 * π) ≤ 160 := by
      rw [div_le_iff₀ hden6]
      nlinarith
    exact (mul_le_mul hfrac hq1hi (by linarith) (by linarith)).trans_eq (by norm_num)
  have hbquadLo : -5200 ≤
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 := by linarith
  have hbquadHi :
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 ≤ 700 := by linarith
  have hb0 : |-44 + 19 * π ^ 2 / 24| ≤ (44 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hb1 : |π * (295 * π ^ 2 - 14256) / 216| ≤ (270 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hb2 : |(109 * π ^ 2 - 5376) / (72 * π) * q 0 +
      (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2| ≤ (5200 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  exact
    ((TaylorMajorant.boundedC (-44 + 19 * π ^ 2 / 24) 44
      (by norm_num) hb0).add
      ((TaylorMajorant.boundedC (π * (295 * π ^ 2 - 14256) / 216) 270
        (by norm_num) hb1).mul TaylorMajorant.X)).add
      ((TaylorMajorant.boundedC ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
          (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) 5200
        (by norm_num) hb2).mul (TaylorMajorant.X.pow 2))

end FrozenTaylorMajorant
end FrozenPolynomial
end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
