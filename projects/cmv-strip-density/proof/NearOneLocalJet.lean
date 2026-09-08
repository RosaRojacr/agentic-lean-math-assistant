/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalTranscription

/-!
# Exact fourth-order jets for the scale-local atlas

`Jet4 s` is an exact value decomposition, not an asymptotic expansion.  Its
`tail` retains every term of order four and above.  The operations below mirror
the cancellation engine used by the atlas producer, including the inverse-tail
identity.  `Jet2` is the exact truncation used after the two forced source-row
cancellations.
-/

namespace NearOneLocalJet

noncomputable section

/-- An exact fourth-order decomposition at the fixed real scale `s`. -/
structure Jet4 (s : ℝ) where
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  tail : ℝ
  value : ℝ
  value_eq : value = c0 + s * c1 + s ^ 2 * c2 + s ^ 3 * c3 + s ^ 4 * tail

namespace Jet4

variable {s : ℝ}

/-- A constant exact jet. -/
def const (s x : ℝ) : Jet4 s :=
  ⟨x, 0, 0, 0, 0, x, by ring⟩

/-- The exact jet of the scale coordinate. -/
def id (s : ℝ) : Jet4 s :=
  ⟨0, 1, 0, 0, 0, s, by ring⟩

/-- Exact addition. -/
def add (a b : Jet4 s) : Jet4 s :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3,
    a.tail + b.tail, a.value + b.value, by
      rw [a.value_eq, b.value_eq]
      ring⟩

/-- Exact negation. -/
def neg (a : Jet4 s) : Jet4 s :=
  ⟨-a.c0, -a.c1, -a.c2, -a.c3, -a.tail, -a.value, by
      rw [a.value_eq]
      ring⟩

/-- Exact subtraction. -/
def sub (a b : Jet4 s) : Jet4 s := a.add b.neg

/-- Exact multiplication.  The displayed high polynomial and all three tail
terms are the complete product remainder; no order is discarded. -/
def mul (a b : Jet4 s) : Jet4 s :=
  ⟨a.c0 * b.c0,
    a.c0 * b.c1 + a.c1 * b.c0,
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0,
    a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0,
    (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) +
      s * (a.c2 * b.c3 + a.c3 * b.c2) + s ^ 2 * (a.c3 * b.c3) +
      a.tail * (b.c0 + s * b.c1 + s ^ 2 * b.c2 + s ^ 3 * b.c3) +
      b.tail * (a.c0 + s * a.c1 + s ^ 2 * a.c2 + s ^ 3 * a.c3) +
      s ^ 4 * a.tail * b.tail,
    a.value * b.value, by
      rw [a.value_eq, b.value_eq]
      ring⟩

/-- Exact natural powers. -/
def pow (a : Jet4 s) : ℕ → Jet4 s
  | 0 => const s 1
  | n + 1 => (pow a n).mul a

/-- Exact square without a recursive power elaboration. -/
def sq (a : Jet4 s) : Jet4 s := a.mul a

/-- Exact fourth power. -/
def fourth (a : Jet4 s) : Jet4 s := a.sq.sq

/-- Exact reciprocal for a jet with constant coefficient one.  If `a*q` is the
truncated inverse product, then `1/a = q - s^4*(a*q).tail/a`; this is the same
inverse-tail identity used by the atlas producer. -/
def invOne (a : Jet4 s) (h0 : a.c0 = 1) (hv : a.value ≠ 0) : Jet4 s := by
  let q1 := -a.c1
  let q2 := a.c1 ^ 2 - a.c2
  let q3 := -(a.c1 * q2 + a.c2 * q1 + a.c3)
  let q : Jet4 s :=
    ⟨1, q1, q2, q3, 0,
      1 + s * q1 + s ^ 2 * q2 + s ^ 3 * q3, by ring⟩
  let product := a.mul q
  refine ⟨1, q1, q2, q3, -product.tail / a.value, 1 / a.value, ?_⟩
  have hp := product.value_eq
  have hpValue : product.value = a.value * q.value := rfl
  rw [hpValue, q.value_eq] at hp
  dsimp [product, mul, q, q1, q2, q3] at hp ⊢
  rw [h0] at hp ⊢
  field_simp [hv] at hp ⊢
  nlinarith [hp]

/-- Exact division by a denominator whose constant coefficient is one. -/
def divOne (a b : Jet4 s) (h0 : b.c0 = 1) (hv : b.value ≠ 0) : Jet4 s :=
  a.mul (b.invOne h0 hv)

/-- The exact identity underlying the generated `R₁` atom.  Its analytic tail
is `R₃`, exactly as in the fixed atlas DAG. -/
def atanRemainderOne (x : Jet4 s) : Jet4 s :=
  (const s (-(1 / 3 : ℝ))).add
    ((const s (1 / 5 : ℝ)).mul x.sq |>.add
      (x.fourth.mul
        (const s (NearOneAtanRemainder.atanRemainder 3 x.value))))

/-- The exact generated arctangent quotient node. -/
def atanQuotient (x : Jet4 s) : Jet4 s :=
  (const s 1).add (x.sq.mul x.atanRemainderOne)

@[simp] theorem value_const (x : ℝ) : (const s x).value = x := rfl
@[simp] theorem value_id : (id s).value = s := rfl
@[simp] theorem value_add (a b : Jet4 s) : (a.add b).value = a.value + b.value := rfl
@[simp] theorem value_neg (a : Jet4 s) : a.neg.value = -a.value := rfl
@[simp] theorem value_sub (a b : Jet4 s) : (a.sub b).value = a.value - b.value := rfl
@[simp] theorem value_mul (a b : Jet4 s) : (a.mul b).value = a.value * b.value := rfl
@[simp] theorem value_sq (a : Jet4 s) : a.sq.value = a.value ^ 2 := by
  simp [sq, pow_two]
@[simp] theorem value_fourth (a : Jet4 s) : a.fourth.value = a.value ^ 4 := by
  simp [fourth]
  ring

@[simp] theorem value_pow (a : Jet4 s) (n : ℕ) :
    (a.pow n).value = a.value ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow, value_mul, ih, pow_succ]
@[simp] theorem value_invOne (a : Jet4 s) (h0 hv) :
    (a.invOne h0 hv).value = 1 / a.value := rfl
@[simp] theorem value_divOne (a b : Jet4 s) (h0 hv) :
    (a.divOne b h0 hv).value = a.value / b.value := by
  change a.value * (1 / b.value) = a.value / b.value
  simp only [one_mul, div_eq_mul_inv]

@[simp] theorem value_atanRemainderOne (x : Jet4 s) :
    x.atanRemainderOne.value = NearOneAtanRemainder.atanRemainder 1 x.value := by
  rw [NearOneAtanRemainder.atanRemainder_finite_expansion 1 2]
  simp [atanRemainderOne, Finset.sum_range_succ]
  ring

@[simp] theorem value_atanQuotient (x : Jet4 s) :
    x.atanQuotient.value = NearOneAnalyticSystem.atanQuotient x.value := by
  rw [NearOneRegularizedThirdRow.atanQuotient_eq_one_add_sq_mul,
    ← NearOneAtanRemainder.atanRemainder_one]
  simp [atanQuotient]

end Jet4

/-- An exact second-order decomposition at the fixed scale. -/
structure Jet2 (s : ℝ) where
  c0 : ℝ
  c1 : ℝ
  tail : ℝ
  value : ℝ
  value_eq : value = c0 + s * c1 + s ^ 2 * tail

namespace Jet2

variable {s : ℝ}

/-- Exact addition of second-order decompositions. -/
def add (a b : Jet2 s) : Jet2 s :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.tail + b.tail, a.value + b.value, by
    rw [a.value_eq, b.value_eq]
    ring⟩

/-- Move the quadratic and cubic coefficients of a fourth-order jet into its
exact second-order tail. -/
def truncate (a : Jet4 s) : Jet2 s :=
  ⟨a.c0, a.c1, a.c2 + s * a.c3 + s ^ 2 * a.tail, a.value, by
    rw [a.value_eq]
    ring⟩

/-- Divide a fourth-order decomposition by the two checked zero coefficients.
The nonzero-scale hypothesis is explicit because the resulting value is the
actual quotient, not a totalized endpoint convention. -/
def divideSq (a : Jet4 s) (h0 : a.c0 = 0) (h1 : a.c1 = 0) (hs : s ≠ 0) :
    Jet2 s :=
  ⟨a.c2, a.c3, a.tail, a.value / s ^ 2, by
    rw [a.value_eq, h0, h1]
    field_simp [hs]
    ring⟩

@[simp] theorem value_add (a b : Jet2 s) : (a.add b).value = a.value + b.value := rfl
@[simp] theorem value_truncate (a : Jet4 s) : (truncate a).value = a.value := rfl
@[simp] theorem value_divideSq (a : Jet4 s) h0 h1 hs :
    (divideSq a h0 h1 hs).value = a.value / s ^ 2 := rfl

/-- The retained tail is exactly the second divided value once both low
coefficients vanish. -/
theorem tail_eq_div_sq (a : Jet2 s) (h0 : a.c0 = 0) (h1 : a.c1 = 0)
    (hs : s ≠ 0) : a.tail = a.value / s ^ 2 := by
  rw [a.value_eq, h0, h1]
  field_simp [hs]
  ring

end Jet2

end

end NearOneLocalJet
