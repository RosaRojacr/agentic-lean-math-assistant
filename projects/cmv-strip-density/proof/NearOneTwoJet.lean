/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
Exact two-jets of real-valued germs at zero.
-/

namespace NearOneTwoJet

open Filter Polynomial
open scoped Topology

noncomputable section

/-- `HasTwoJet f c₀ c₁ c₂` records an exact second-order decomposition of the
 germ of `f` at zero, with a continuous tail whose endpoint is `c₂`. -/
structure HasTwoJet (f : ℝ → ℝ) (c₀ c₁ c₂ : ℝ) where
  tail : ℝ → ℝ
  continuousAt_tail : ContinuousAt tail 0
  tail_zero : tail 0 = c₂
  eventually_eq : f =ᶠ[𝓝 0] fun s => c₀ + s * c₁ + s ^ 2 * tail s

namespace HasTwoJet

variable {f g : ℝ → ℝ} {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}

@[simp] theorem value (h : HasTwoJet f a₀ a₁ a₂) : f 0 = a₀ := by
  have heq := h.eventually_eq.eq_of_nhds
  simpa using heq

theorem continuousAt (h : HasTwoJet f a₀ a₁ a₂) : ContinuousAt f 0 := by
  apply (continuousAt_const.add
    (continuousAt_id.mul continuousAt_const)).add
      ((continuousAt_id.pow 2).mul h.continuousAt_tail) |>.congr_of_eventuallyEq
  exact h.eventually_eq

/-- The continuous second-order tail supplied by a two-jet. -/
def remainder (h : HasTwoJet f a₀ a₁ a₂) : ℝ → ℝ := h.tail

@[fun_prop] theorem continuousAt_remainder (h : HasTwoJet f a₀ a₁ a₂) :
    ContinuousAt h.remainder 0 := h.continuousAt_tail

@[simp] theorem remainder_zero (h : HasTwoJet f a₀ a₁ a₂) :
    h.remainder 0 = a₂ := h.tail_zero

theorem eventually_eq_remainder (h : HasTwoJet f a₀ a₁ a₂) :
    f =ᶠ[𝓝 0] fun s => a₀ + s * a₁ + s ^ 2 * h.remainder s :=
  h.eventually_eq

/-- Dividing an order-two germ by `s²` away from zero and filling in its
second coefficient at zero gives a continuous germ. -/
protected theorem continuousAt_div_sq
    (hf : HasTwoJet f 0 0 a₂) :
    ContinuousAt (fun s => if s = 0 then a₂ else f s / s ^ 2) 0 := by
  apply hf.continuousAt_remainder.congr_of_eventuallyEq
  filter_upwards [hf.eventually_eq_remainder] with s hs
  by_cases h0 : s = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rw [hs]
    field_simp
    ring

/-- Transport a two-jet across equality of germs. -/
protected def congr (hf : HasTwoJet f a₀ a₁ a₂)
    (hfg : g =ᶠ[𝓝 0] f) : HasTwoJet g a₀ a₁ a₂ :=
  ⟨hf.tail, hf.continuousAt_tail, hf.tail_zero,
    hfg.trans hf.eventually_eq⟩

protected def const (c : ℝ) :
    HasTwoJet (fun _ : ℝ => c) c 0 0 := by
  refine ⟨fun _ => 0, continuousAt_const, rfl, ?_⟩
  filter_upwards
  intro s
  ring

protected def id : HasTwoJet (fun s : ℝ => s) 0 1 0 := by
  refine ⟨fun _ => 0, continuousAt_const, rfl, ?_⟩
  filter_upwards
  intro s
  ring

protected def add
    (hf : HasTwoJet f a₀ a₁ a₂) (hg : HasTwoJet g b₀ b₁ b₂) :
    HasTwoJet (fun s => f s + g s)
      (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  refine ⟨fun s => hf.remainder s + hg.remainder s,
    hf.continuousAt_remainder.add hg.continuousAt_remainder, ?_, ?_⟩
  · simp
  · filter_upwards [hf.eventually_eq_remainder, hg.eventually_eq_remainder]
      with s hfs hgs
    rw [hfs, hgs]
    ring

protected def neg (hf : HasTwoJet f a₀ a₁ a₂) :
    HasTwoJet (fun s => -f s) (-a₀) (-a₁) (-a₂) := by
  refine ⟨fun s => -hf.remainder s,
    hf.continuousAt_remainder.neg, by simp, ?_⟩
  filter_upwards [hf.eventually_eq_remainder] with s hfs
  rw [hfs]
  ring

protected def sub
    (hf : HasTwoJet f a₀ a₁ a₂) (hg : HasTwoJet g b₀ b₁ b₂) :
    HasTwoJet (fun s => f s - g s)
      (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

protected def mul
    (hf : HasTwoJet f a₀ a₁ a₂) (hg : HasTwoJet g b₀ b₁ b₂) :
    HasTwoJet (fun s => f s * g s)
      (a₀ * b₀) (a₀ * b₁ + a₁ * b₀)
      (a₀ * b₂ + a₁ * b₁ + a₂ * b₀) := by
  let F := hf.remainder
  let G := hg.remainder
  refine ⟨fun s => a₀ * G s + a₁ * b₁ + s * a₁ * G s +
      b₀ * F s + s * b₁ * F s + s ^ 2 * F s * G s, ?_, ?_, ?_⟩
  · dsimp only [F, G]
    fun_prop
  · dsimp only [F, G]
    simp
    ring
  · filter_upwards [hf.eventually_eq_remainder, hg.eventually_eq_remainder]
      with s hfs hgs
    dsimp only [F, G]
    rw [hfs, hgs]
    ring

protected def smul (c : ℝ) (hf : HasTwoJet f a₀ a₁ a₂) :
    HasTwoJet (fun s => c * f s) (c * a₀) (c * a₁) (c * a₂) := by
  simpa using (HasTwoJet.const c).mul hf

protected def inv (hf : HasTwoJet f a₀ a₁ a₂) (ha₀ : a₀ ≠ 0) :
    HasTwoJet (fun s => (f s)⁻¹) (a₀⁻¹) (-a₁ / a₀ ^ 2)
      (a₁ ^ 2 / a₀ ^ 3 - a₂ / a₀ ^ 2) := by
  let F := hf.remainder
  let T : ℝ → ℝ := fun s =>
    (a₁ ^ 2 / a₀ ^ 2 - F s / a₀ + s * a₁ * F s / a₀ ^ 2) / f s
  have hfn : f 0 ≠ 0 := by
    rw [hf.value]
    exact ha₀
  refine ⟨T, ?_, ?_, ?_⟩
  · exact (((continuousAt_const.div_const _).sub
        (hf.continuousAt_remainder.div_const _)).add
      (((continuousAt_id.mul continuousAt_const).mul
        hf.continuousAt_remainder).div_const _)).div hf.continuousAt hfn
  · dsimp only [T, F]
    rw [hf.value, hf.remainder_zero]
    field_simp
    ring
  · have hevne : ∀ᶠ s in 𝓝 0, f s ≠ 0 := hf.continuousAt.eventually_ne hfn
    filter_upwards [hf.eventually_eq_remainder, hevne] with s hfs hsn
    dsimp only [T, F]
    rw [hfs] at hsn ⊢
    field_simp [hsn, ha₀]
    ring

protected def div
    (hf : HasTwoJet f a₀ a₁ a₂) (hg : HasTwoJet g b₀ b₁ b₂)
    (hb₀ : b₀ ≠ 0) :
    HasTwoJet (fun s => f s / g s)
      (a₀ / b₀)
      (a₁ / b₀ - a₀ * b₁ / b₀ ^ 2)
      (a₂ / b₀ - a₁ * b₁ / b₀ ^ 2 +
        a₀ * (b₁ ^ 2 / b₀ ^ 3 - b₂ / b₀ ^ 2)) := by
  have h := hf.mul (hg.inv hb₀)
  convert h using 1 <;> field_simp <;> ring

/-- Squaring a two-jet. -/
protected def sq (hf : HasTwoJet f a₀ a₁ a₂) :
    HasTwoJet (fun s => f s ^ 2)
      (a₀ ^ 2) (2 * a₀ * a₁) (2 * a₀ * a₂ + a₁ ^ 2) := by
  have h := hf.mul hf
  convert h using 1 <;> ring

/-- Multiplication by `s²` promotes a continuous germ to a two-jet. -/
protected def sq_mul_continuous {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasTwoJet (fun s => s ^ 2 * g s) 0 0 (g 0) := by
  refine ⟨g, hg, rfl, ?_⟩
  filter_upwards
  intro s
  ring

/-- An order-two germ may be multiplied by a merely continuous germ. -/
protected def mul_continuous_of_orderTwo
    (hf : HasTwoJet f 0 0 a₂) {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) :
    HasTwoJet (fun s => f s * g s) 0 0 (a₂ * g 0) := by
  refine ⟨fun s => hf.remainder s * g s,
    hf.continuousAt_remainder.mul hg, by simp, ?_⟩
  filter_upwards [hf.eventually_eq_remainder] with s hs
  rw [hs]
  ring

/-- If `f(0)=0`, the germ `1 + f² g(f)` has no linear term.  This
constructor deliberately asks only for continuity of `g`. -/
protected def one_add_sq_mul_continuous
    (hf : HasTwoJet f 0 a₁ a₂)
    {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasTwoJet (fun s => 1 + f s ^ 2 * g (f s))
      1 0 (a₁ ^ 2 * g 0) := by
  let F := hf.remainder
  refine ⟨fun s => (a₁ + s * F s) ^ 2 * g (f s), ?_, ?_, ?_⟩
  · dsimp only [F]
    have hcomp : ContinuousAt (fun s => g (f s)) 0 := by
      simpa only [Function.comp_def] using
        hg.comp_of_eq hf.continuousAt hf.value
    exact (((continuousAt_const.add
      (continuousAt_id.mul hf.continuousAt_remainder)).pow 2).mul hcomp)
  · dsimp only [F]
    rw [hf.value]
    simp
  · filter_upwards [hf.eventually_eq_remainder] with s hfs
    dsimp only [F]
    rw [hfs]
    ring


end HasTwoJet

/-- A scalar two-jet with bundled coefficients, convenient for compositional
construction when the intermediate coefficients are inferred. -/
structure SomeHasTwoJet (f : ℝ → ℝ) where
  c₀ : ℝ
  c₁ : ℝ
  c₂ : ℝ
  jet : HasTwoJet f c₀ c₁ c₂

namespace SomeHasTwoJet

variable {f g : ℝ → ℝ}

protected def const (c : ℝ) : SomeHasTwoJet (fun _ : ℝ => c) :=
  ⟨c, 0, 0, HasTwoJet.const c⟩

protected def id : SomeHasTwoJet (fun s : ℝ => s) :=
  ⟨0, 1, 0, HasTwoJet.id⟩

protected def add (hf : SomeHasTwoJet f) (hg : SomeHasTwoJet g) :
    SomeHasTwoJet (fun s => f s + g s) :=
  ⟨hf.c₀ + hg.c₀, hf.c₁ + hg.c₁, hf.c₂ + hg.c₂,
    hf.jet.add hg.jet⟩

protected def neg (hf : SomeHasTwoJet f) :
    SomeHasTwoJet (fun s => -f s) :=
  ⟨-hf.c₀, -hf.c₁, -hf.c₂, hf.jet.neg⟩

protected def sub (hf : SomeHasTwoJet f) (hg : SomeHasTwoJet g) :
    SomeHasTwoJet (fun s => f s - g s) :=
  ⟨hf.c₀ - hg.c₀, hf.c₁ - hg.c₁, hf.c₂ - hg.c₂,
    hf.jet.sub hg.jet⟩

protected def mul (hf : SomeHasTwoJet f) (hg : SomeHasTwoJet g) :
    SomeHasTwoJet (fun s => f s * g s) :=
  ⟨hf.c₀ * hg.c₀, hf.c₀ * hg.c₁ + hf.c₁ * hg.c₀,
    hf.c₀ * hg.c₂ + hf.c₁ * hg.c₁ + hf.c₂ * hg.c₀,
    hf.jet.mul hg.jet⟩

/-- Multiplication by a scalar without routing through generic jet
multiplication. -/
protected def smul (c : ℝ) (hf : SomeHasTwoJet f) :
    SomeHasTwoJet (fun s => c * f s) :=
  ⟨c * hf.c₀, c * hf.c₁, c * hf.c₂, HasTwoJet.smul c hf.jet⟩

/-- Squaring without duplicating the bundled jet through recursive `pow`. -/
protected def sq (hf : SomeHasTwoJet f) :
    SomeHasTwoJet (fun s => f s ^ 2) :=
  ⟨hf.c₀ ^ 2, 2 * hf.c₀ * hf.c₁,
    2 * hf.c₀ * hf.c₂ + hf.c₁ ^ 2, hf.jet.sq⟩

/-- Cubing with explicit bundled coefficients, avoiding casts introduced by
recursive `pow`. -/
protected def cube (hf : SomeHasTwoJet f) :
    SomeHasTwoJet (fun s => f s ^ 3) :=
  ⟨hf.c₀ ^ 3, 3 * hf.c₀ ^ 2 * hf.c₁,
    3 * hf.c₀ ^ 2 * hf.c₂ + 3 * hf.c₀ * hf.c₁ ^ 2, by
      convert hf.jet.mul hf.jet.sq using 1 <;> ring⟩

protected def inv (hf : SomeHasTwoJet f) (h₀ : hf.c₀ ≠ 0) :
    SomeHasTwoJet (fun s => (f s)⁻¹) :=
  ⟨hf.c₀⁻¹, -hf.c₁ / hf.c₀ ^ 2,
    hf.c₁ ^ 2 / hf.c₀ ^ 3 - hf.c₂ / hf.c₀ ^ 2,
    hf.jet.inv h₀⟩

protected def div (hf : SomeHasTwoJet f) (hg : SomeHasTwoJet g)
    (h₀ : hg.c₀ ≠ 0) :
    SomeHasTwoJet (fun s => f s / g s) :=
  ⟨hf.c₀ / hg.c₀,
    hf.c₁ / hg.c₀ - hf.c₀ * hg.c₁ / hg.c₀ ^ 2,
    hf.c₂ / hg.c₀ - hf.c₁ * hg.c₁ / hg.c₀ ^ 2 +
      hf.c₀ * (hg.c₁ ^ 2 / hg.c₀ ^ 3 - hg.c₂ / hg.c₀ ^ 2),
    hf.jet.div hg.jet h₀⟩

protected def pow (hf : SomeHasTwoJet f) :
    ∀ n : ℕ, SomeHasTwoJet (fun s => f s ^ n)
  | 0 => by simpa using SomeHasTwoJet.const 1
  | n + 1 => by simpa [pow_succ] using (hf.pow n).mul hf

end SomeHasTwoJet

/-! ## Continuous polynomial families -/

/-- A polynomial-valued family with coefficientwise continuity at zero and a
uniform support bound.  The bound makes diagonal evaluation continuous without
putting an artificial topology on `Polynomial ℝ`. -/
structure ContinuousPolynomialAt (p : ℝ → ℝ[X]) where
  bound : ℕ
  continuousAt_coeff : ∀ n, ContinuousAt (fun s => (p s).coeff n) 0
  coeff_eq_zero_of_bound_lt : ∀ s n, bound < n → (p s).coeff n = 0

namespace ContinuousPolynomialAt

variable {p r : ℝ → ℝ[X]}
private theorem continuousAt_finset_sum'
    {ι : Type*} {S : Finset ι} {F : ℝ → ι → ℝ}
    (hF : ∀ i ∈ S, ContinuousAt (fun s => F s i) 0) :
    ContinuousAt (fun s => ∑ i ∈ S, F s i) 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact continuousAt_const
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i S)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

protected def const (P : ℝ[X]) :
    ContinuousPolynomialAt (fun _ : ℝ => P) where
  bound := P.natDegree
  continuousAt_coeff := fun _ => continuousAt_const
  coeff_eq_zero_of_bound_lt := fun _ _ hn =>
    P.coeff_eq_zero_of_natDegree_lt hn

protected def C {f : ℝ → ℝ} (hf : ContinuousAt f 0) :
    ContinuousPolynomialAt (fun s => Polynomial.C (f s)) where
  bound := 0
  continuousAt_coeff := fun n => by
    simp only [coeff_C]
    split <;> fun_prop
  coeff_eq_zero_of_bound_lt := fun _ n hn => by
    simp only [coeff_C]
    split
    · omega
    · rfl

protected def add (hp : ContinuousPolynomialAt p)
    (hr : ContinuousPolynomialAt r) :
    ContinuousPolynomialAt (fun s => p s + r s) where
  bound := max hp.bound hr.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_add]
    exact (hp.continuousAt_coeff n).add (hr.continuousAt_coeff n)
  coeff_eq_zero_of_bound_lt := fun s n hn => by
    rw [coeff_add, hp.coeff_eq_zero_of_bound_lt s n (lt_of_le_of_lt
      (le_max_left _ _) hn), hr.coeff_eq_zero_of_bound_lt s n
      (lt_of_le_of_lt (le_max_right _ _) hn), add_zero]

protected def neg (hp : ContinuousPolynomialAt p) :
    ContinuousPolynomialAt (fun s => -p s) where
  bound := hp.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_neg]
    exact (hp.continuousAt_coeff n).neg
  coeff_eq_zero_of_bound_lt := fun s n hn => by
    rw [coeff_neg, hp.coeff_eq_zero_of_bound_lt s n hn, neg_zero]

protected def sub (hp : ContinuousPolynomialAt p)
    (hr : ContinuousPolynomialAt r) :
    ContinuousPolynomialAt (fun s => p s - r s) :=
  hp.add hr.neg

protected def mul (hp : ContinuousPolynomialAt p)
    (hr : ContinuousPolynomialAt r) :
    ContinuousPolynomialAt (fun s => p s * r s) where
  bound := hp.bound + hr.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_mul]
    apply continuousAt_finset_sum'
    intro ij hij
    exact (hp.continuousAt_coeff ij.1).mul
      (hr.continuousAt_coeff ij.2)
  coeff_eq_zero_of_bound_lt := fun s n hn => by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum : ij.1 + ij.2 = n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hi : hp.bound < ij.1
    · rw [hp.coeff_eq_zero_of_bound_lt s ij.1 hi, zero_mul]
    · have hj : hr.bound < ij.2 := by omega
      rw [hr.coeff_eq_zero_of_bound_lt s ij.2 hj, mul_zero]

protected def pow (hp : ContinuousPolynomialAt p) :
    ∀ n : ℕ, ContinuousPolynomialAt (fun s => p s ^ n)
  | 0 => by simpa using ContinuousPolynomialAt.const 1
  | n + 1 => by
      simpa [pow_succ] using (hp.pow n).mul hp

protected def divX (hp : ContinuousPolynomialAt p) :
    ContinuousPolynomialAt (fun s => (p s).divX) where
  bound := hp.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_divX]
    exact hp.continuousAt_coeff (n + 1)
  coeff_eq_zero_of_bound_lt := fun s n hn => by
    rw [coeff_divX]
    exact hp.coeff_eq_zero_of_bound_lt s (n + 1) (by omega)


/-- Simultaneous evaluation of a uniformly bounded continuous polynomial
family at a continuous scalar path is continuous. -/
theorem continuousAt_eval (hp : ContinuousPolynomialAt p)
    {x : ℝ → ℝ} (hx : ContinuousAt x 0) :
    ContinuousAt (fun s => (p s).eval (x s)) 0 := by
  let S := Finset.range (hp.bound + 1)
  have hsum : ContinuousAt
      (fun s => ∑ n ∈ S, (p s).coeff n * x s ^ n) 0 := by
    apply continuousAt_finset_sum'
    intro n hn
    exact (hp.continuousAt_coeff n).mul (hx.pow n)
  apply hsum.congr_of_eventuallyEq
  filter_upwards
  intro s
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset (s₁ := (p s).support) (s₂ := S) ?_ ?_
  · intro n hn
    rw [Finset.mem_range]
    by_contra hnot
    have hgt : hp.bound < n := by omega
    exact (Polynomial.mem_support_iff.mp hn)
      (hp.coeff_eq_zero_of_bound_lt s n hgt)
  · intro n hnS hnSupp
    have hz : (p s).coeff n = 0 := by
      simpa only [Polynomial.mem_support_iff, not_ne_iff] using hnSupp
    rw [hz, zero_mul]

/-- The diagonal evaluation jet is determined by the jets of the first two
coefficient functions.  All higher coefficients enter through a continuous
tail. -/
protected def diagonalEval
    (hp : ContinuousPolynomialAt p)
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (h₀ : HasTwoJet (fun s => (p s).coeff 0) a₀ a₁ a₂)
    (h₁ : HasTwoJet (fun s => (p s).coeff 1) b₀ b₁ b₂) :
    HasTwoJet (fun s => (p s).eval s)
      a₀ (a₁ + b₀) (a₂ + b₁ + (p 0).coeff 2) := by
  let tail : ℝ → ℝ := fun s => ((p s).divX.divX).eval s
  have htail : ContinuousAt tail 0 := by
    dsimp only [tail]
    exact hp.divX.divX.continuousAt_eval continuousAt_id
  have hsq := HasTwoJet.sq_mul_continuous htail
  have h := (h₀.add (HasTwoJet.id.mul h₁)).add hsq
  have htail0 : tail 0 = (p 0).coeff 2 := by
    change (p 0).divX.divX.eval 0 = (p 0).coeff 2
    rw [← coeff_zero_eq_eval_zero]
    simp only [coeff_divX]
  rw [htail0] at h
  have heval : (fun s => (p s).eval s) =ᶠ[𝓝 0]
      fun s => (p s).coeff 0 + s * (p s).coeff 1 + s ^ 2 * tail s := by
    filter_upwards
    intro s
    have hfirst := congrArg (Polynomial.eval s)
      (Polynomial.X_mul_divX_add (p s))
    have hsecond := congrArg (Polynomial.eval s)
      (Polynomial.X_mul_divX_add (p s).divX)
    simp only [eval_add, eval_mul, eval_X, eval_C] at hfirst hsecond
    simp only [coeff_divX] at hsecond
    dsimp only [tail]
    rw [← hfirst, ← hsecond]
    ring
  have hc := h.congr heval
  convert hc using 1 <;> ring

end ContinuousPolynomialAt

/-! ## Polynomial-valued two-jets -/

/-- A coefficientwise exact two-jet for a uniformly bounded polynomial
family. -/
structure PolynomialTwoJet (p : ℝ → ℝ[X]) (P₀ P₁ P₂ : ℝ[X]) where
  continuousPolynomialAt : ContinuousPolynomialAt p
  tail : ℝ → ℝ[X]
  continuousPolynomialAt_tail : ContinuousPolynomialAt tail
  tail_zero : tail 0 = P₂
  eventually_eq : p =ᶠ[𝓝 0] fun s =>
    P₀ + Polynomial.C s * P₁ + Polynomial.C (s ^ 2) * tail s

namespace PolynomialTwoJet

variable {p r : ℝ → ℝ[X]}
  {P₀ P₁ P₂ Q₀ Q₁ Q₂ : ℝ[X]}

/-- Taking a coefficient of a polynomial two-jet gives a scalar two-jet. -/
def coeff (hp : PolynomialTwoJet p P₀ P₁ P₂) (n : ℕ) :
    HasTwoJet (fun s => (p s).coeff n)
      (P₀.coeff n) (P₁.coeff n) (P₂.coeff n) := by
  refine ⟨fun s => (hp.tail s).coeff n,
    hp.continuousPolynomialAt_tail.continuousAt_coeff n, ?_, ?_⟩
  · rw [hp.tail_zero]
  · filter_upwards [hp.eventually_eq] with s hs
    rw [hs]
    simp only [coeff_add, coeff_C_mul]

protected def const (P : ℝ[X]) :
    PolynomialTwoJet (fun _ : ℝ => P) P 0 0 := by
  refine ⟨ContinuousPolynomialAt.const P, fun _ => 0,
    ContinuousPolynomialAt.const 0, rfl, ?_⟩
  filter_upwards
  intro s
  ring

/-- Lift a scalar two-jet through `Polynomial.C`. -/
protected def C {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasTwoJet f a₀ a₁ a₂) :
    PolynomialTwoJet (fun s => Polynomial.C (f s))
      (Polynomial.C a₀) (Polynomial.C a₁) (Polynomial.C a₂) := by
  refine ⟨ContinuousPolynomialAt.C hf.continuousAt,
    fun s => Polynomial.C (hf.remainder s),
    ContinuousPolynomialAt.C hf.continuousAt_remainder, ?_, ?_⟩
  · rw [hf.remainder_zero]
  · filter_upwards [hf.eventually_eq_remainder] with s hs
    rw [hs, map_add, map_add, map_mul, map_mul, map_pow]

protected def add (hp : PolynomialTwoJet p P₀ P₁ P₂)
    (hr : PolynomialTwoJet r Q₀ Q₁ Q₂) :
    PolynomialTwoJet (fun s => p s + r s)
      (P₀ + Q₀) (P₁ + Q₁) (P₂ + Q₂) := by
  refine ⟨hp.continuousPolynomialAt.add hr.continuousPolynomialAt,
    fun s => hp.tail s + hr.tail s,
    hp.continuousPolynomialAt_tail.add
      hr.continuousPolynomialAt_tail, ?_, ?_⟩
  · rw [hp.tail_zero, hr.tail_zero]
  · filter_upwards [hp.eventually_eq, hr.eventually_eq] with s hps hrs
    rw [hps, hrs]
    ring

protected def neg (hp : PolynomialTwoJet p P₀ P₁ P₂) :
    PolynomialTwoJet (fun s => -p s) (-P₀) (-P₁) (-P₂) := by
  refine ⟨hp.continuousPolynomialAt.neg, fun s => -hp.tail s,
    hp.continuousPolynomialAt_tail.neg, ?_, ?_⟩
  · rw [hp.tail_zero]
  · filter_upwards [hp.eventually_eq] with s hs
    rw [hs]
    ring

protected def sub (hp : PolynomialTwoJet p P₀ P₁ P₂)
    (hr : PolynomialTwoJet r Q₀ Q₁ Q₂) :
    PolynomialTwoJet (fun s => p s - r s)
      (P₀ - Q₀) (P₁ - Q₁) (P₂ - Q₂) :=
  hp.add hr.neg

protected def mul (hp : PolynomialTwoJet p P₀ P₁ P₂)
    (hr : PolynomialTwoJet r Q₀ Q₁ Q₂) :
    PolynomialTwoJet (fun s => p s * r s)
      (P₀ * Q₀) (P₀ * Q₁ + P₁ * Q₀)
      (P₀ * Q₂ + P₁ * Q₁ + P₂ * Q₀) := by
  let T : ℝ → ℝ[X] := fun s =>
    P₀ * hr.tail s + P₁ * Q₁ + Polynomial.C s * P₁ * hr.tail s +
      Q₀ * hp.tail s + Polynomial.C s * Q₁ * hp.tail s +
      Polynomial.C (s ^ 2) * hp.tail s * hr.tail s
  have hT : ContinuousPolynomialAt T := by
    dsimp only [T]
    have h₁ := (ContinuousPolynomialAt.const P₀).mul
      hr.continuousPolynomialAt_tail
    have h₂ := ContinuousPolynomialAt.const (P₁ * Q₁)
    have h₃ := ((ContinuousPolynomialAt.C continuousAt_id).mul
      (ContinuousPolynomialAt.const P₁)).mul
        hr.continuousPolynomialAt_tail
    have h₄ := (ContinuousPolynomialAt.const Q₀).mul
      hp.continuousPolynomialAt_tail
    have h₅ := ((ContinuousPolynomialAt.C continuousAt_id).mul
      (ContinuousPolynomialAt.const Q₁)).mul
        hp.continuousPolynomialAt_tail
    have h₆ := ((ContinuousPolynomialAt.C
      (continuousAt_id.pow 2)).mul
        hp.continuousPolynomialAt_tail).mul
          hr.continuousPolynomialAt_tail
    exact ((((h₁.add h₂).add h₃).add h₄).add h₅).add h₆
  refine ⟨hp.continuousPolynomialAt.mul hr.continuousPolynomialAt,
    T, hT, ?_, ?_⟩
  · dsimp only [T]
    rw [hp.tail_zero, hr.tail_zero]
    simp
    ring
  · filter_upwards [hp.eventually_eq, hr.eventually_eq] with s hps hrs
    dsimp only [T]
    rw [hps, hrs]
    simp only [map_pow]
    ring

private def pow₀ (P₀ : ℝ[X]) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => pow₀ P₀ n * P₀

private def pow₁ (P₀ P₁ : ℝ[X]) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => pow₀ P₀ n * P₁ + pow₁ P₀ P₁ n * P₀

private def pow₂ (P₀ P₁ P₂ : ℝ[X]) : ℕ → ℝ[X]
  | 0 => 0
  | n + 1 => pow₀ P₀ n * P₂ + pow₁ P₀ P₁ n * P₁ +
      pow₂ P₀ P₁ P₂ n * P₀

protected def pow (hp : PolynomialTwoJet p P₀ P₁ P₂) :
    ∀ n : ℕ, PolynomialTwoJet (fun s => p s ^ n)
      (pow₀ P₀ n) (pow₁ P₀ P₁ n) (pow₂ P₀ P₁ P₂ n)
  | 0 => by simpa [pow₀, pow₁, pow₂] using PolynomialTwoJet.const 1
  | n + 1 => by
      simpa [pow_succ, pow₀, pow₁, pow₂] using (hp.pow n).mul hp

protected def divX (hp : PolynomialTwoJet p P₀ P₁ P₂) :
    PolynomialTwoJet (fun s => (p s).divX)
      P₀.divX P₁.divX P₂.divX := by
  refine ⟨hp.continuousPolynomialAt.divX,
    fun s => (hp.tail s).divX,
    hp.continuousPolynomialAt_tail.divX, ?_, ?_⟩
  · rw [hp.tail_zero]
  · filter_upwards [hp.eventually_eq] with s hs
    rw [hs]
    simp only [divX_add, divX_C_mul]

/-- Diagonal evaluation of a polynomial two-jet. -/
def diagonalEval (hp : PolynomialTwoJet p P₀ P₁ P₂) :
    HasTwoJet (fun s => (p s).eval s)
      (P₀.coeff 0)
      (P₀.coeff 1 + P₁.coeff 0)
      (P₀.coeff 2 + P₁.coeff 1 + P₂.coeff 0) := by
  have h := hp.continuousPolynomialAt.diagonalEval (hp.coeff 0) (hp.coeff 1)
  have hv : p 0 = P₀ := by
    have heq := hp.eventually_eq.eq_of_nhds
    simpa using heq
  rw [hv] at h
  convert h using 1 <;> ring

end PolynomialTwoJet

/-- A polynomial two-jet with its three coefficient polynomials bundled. -/
structure SomePolynomialTwoJet (p : ℝ → ℝ[X]) where
  P₀ : ℝ[X]
  P₁ : ℝ[X]
  P₂ : ℝ[X]
  jet : PolynomialTwoJet p P₀ P₁ P₂

namespace SomePolynomialTwoJet

variable {p r : ℝ → ℝ[X]}

protected def const (P : ℝ[X]) :
    SomePolynomialTwoJet (fun _ : ℝ => P) :=
  ⟨P, 0, 0, PolynomialTwoJet.const P⟩

protected def C {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasTwoJet f a₀ a₁ a₂) :
    SomePolynomialTwoJet (fun s => Polynomial.C (f s)) :=
  ⟨Polynomial.C a₀, Polynomial.C a₁, Polynomial.C a₂,
    PolynomialTwoJet.C hf⟩

protected def add (hp : SomePolynomialTwoJet p)
    (hr : SomePolynomialTwoJet r) :
    SomePolynomialTwoJet (fun s => p s + r s) :=
  ⟨hp.P₀ + hr.P₀, hp.P₁ + hr.P₁, hp.P₂ + hr.P₂,
    hp.jet.add hr.jet⟩

protected def neg (hp : SomePolynomialTwoJet p) :
    SomePolynomialTwoJet (fun s => -p s) :=
  ⟨-hp.P₀, -hp.P₁, -hp.P₂, hp.jet.neg⟩

protected def sub (hp : SomePolynomialTwoJet p)
    (hr : SomePolynomialTwoJet r) :
    SomePolynomialTwoJet (fun s => p s - r s) :=
  ⟨hp.P₀ - hr.P₀, hp.P₁ - hr.P₁, hp.P₂ - hr.P₂,
    hp.jet.sub hr.jet⟩

protected def mul (hp : SomePolynomialTwoJet p)
    (hr : SomePolynomialTwoJet r) :
    SomePolynomialTwoJet (fun s => p s * r s) :=
  ⟨hp.P₀ * hr.P₀, hp.P₀ * hr.P₁ + hp.P₁ * hr.P₀,
    hp.P₀ * hr.P₂ + hp.P₁ * hr.P₁ + hp.P₂ * hr.P₀,
    hp.jet.mul hr.jet⟩

/-- Squaring with explicit coefficient polynomials, avoiding recursive-power
casts in downstream normalization. -/
protected def sq (hp : SomePolynomialTwoJet p) :
    SomePolynomialTwoJet (fun s => p s ^ 2) :=
  ⟨hp.P₀ ^ 2, 2 * hp.P₀ * hp.P₁,
    2 * hp.P₀ * hp.P₂ + hp.P₁ ^ 2, by
      convert hp.jet.mul hp.jet using 1 <;> ring⟩

protected def pow (hp : SomePolynomialTwoJet p) (n : ℕ) :
    SomePolynomialTwoJet (fun s => p s ^ n) :=
  ⟨PolynomialTwoJet.pow₀ hp.P₀ n,
    PolynomialTwoJet.pow₁ hp.P₀ hp.P₁ n,
    PolynomialTwoJet.pow₂ hp.P₀ hp.P₁ hp.P₂ n,
    hp.jet.pow n⟩

protected def divX (hp : SomePolynomialTwoJet p) :
    SomePolynomialTwoJet (fun s => (p s).divX) :=
  ⟨hp.P₀.divX, hp.P₁.divX, hp.P₂.divX, hp.jet.divX⟩

/-- Diagonal evaluation, retaining the exact coefficients in the bundle
projections. -/
def diagonalEval (hp : SomePolynomialTwoJet p) :
    HasTwoJet (fun s => (p s).eval s)
      (hp.P₀.coeff 0)
      (hp.P₀.coeff 1 + hp.P₁.coeff 0)
      (hp.P₀.coeff 2 + hp.P₁.coeff 1 + hp.P₂.coeff 0) :=
  hp.jet.diagonalEval

end SomePolynomialTwoJet

end

end NearOneTwoJet
