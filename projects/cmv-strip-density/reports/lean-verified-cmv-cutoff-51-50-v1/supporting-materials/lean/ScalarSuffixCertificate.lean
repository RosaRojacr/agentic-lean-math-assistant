/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import EqualAreaEnvelope
import CMVSuffixModel
import LeanSuffixReflective
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue

/-!
# A sound scalar suffix certificate kernel

Numerical leaves are exact rationals. `QInterval.RealContains` is the only
interpretation of an interval as a statement about a real number. The concrete
cell is the first brick of `face_bridge_pilot`.
-/

open Real Set
open scoped BigOperators
noncomputable section
namespace ScalarSuffixCertificate

abbrev QInterval := LeanSuffixReflective.QInterval

namespace QInterval

/-- The tight interval product: its endpoints are the extrema of the four
corner products. -/
def mul (i j : QInterval) : QInterval where
  lo := min (min (i.lo * j.lo) (i.lo * j.hi))
    (min (i.hi * j.lo) (i.hi * j.hi))
  hi := max (max (i.lo * j.lo) (i.lo * j.hi))
    (max (i.hi * j.lo) (i.hi * j.hi))
  ordered := by
    calc
      min (min (i.lo * j.lo) (i.lo * j.hi))
          (min (i.hi * j.lo) (i.hi * j.hi))
          ≤ i.lo * j.lo := (min_le_left _ _).trans (min_le_left _ _)
      _ ≤ max (max (i.lo * j.lo) (i.lo * j.hi))
          (max (i.hi * j.lo) (i.hi * j.hi)) :=
        (le_max_left _ _).trans (le_max_left _ _)

/-- Positive reciprocal; positivity is checked in exact rational arithmetic. -/
def recipPos (i : QInterval) (hi : 0 < i.lo) : QInterval where
  lo := 1 / i.hi
  hi := 1 / i.lo
  ordered := one_div_le_one_div_of_le hi i.ordered

def divPos (i j : QInterval) (hj : 0 < j.lo) : QInterval :=
  i.mul (j.recipPos hj)

/-- Real soundness of tight exact-rational multiplication. -/
theorem realContains_mul {i j : QInterval} {x y : ℝ}
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (i.mul j).RealContains (x * y) := by
  have corner_lower (q : ℚ) :
      min ((q : ℝ) * (j.lo : ℝ)) ((q : ℝ) * (j.hi : ℝ)) ≤ (q : ℝ) * y := by
    by_cases hq : 0 ≤ q
    · have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hqR)
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
      exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hq')
  have corner_upper (q : ℚ) :
      (q : ℝ) * y ≤ max ((q : ℝ) * (j.lo : ℝ)) ((q : ℝ) * (j.hi : ℝ)) := by
    by_cases hq : 0 ≤ q
    · have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      exact (mul_le_mul_of_nonneg_left hy.2 hqR).trans (le_max_right _ _)
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
      exact (mul_le_mul_of_nonpos_left hy.1 hq').trans (le_max_left _ _)
  have hlo :
      min
          (min ((i.lo : ℝ) * (j.lo : ℝ)) ((i.lo : ℝ) * (j.hi : ℝ)))
          (min ((i.hi : ℝ) * (j.lo : ℝ)) ((i.hi : ℝ) * (j.hi : ℝ)))
        ≤ x * y := by
    by_cases hy0 : 0 ≤ y
    · exact ((min_le_left _ _).trans (corner_lower i.lo)).trans
        (mul_le_mul_of_nonneg_right hx.1 hy0)
    · have hy0' : y ≤ 0 := le_of_not_ge hy0
      exact ((min_le_right _ _).trans (corner_lower i.hi)).trans
        (mul_le_mul_of_nonpos_right hx.2 hy0')
  have hhi :
      x * y ≤
        max
          (max ((i.lo : ℝ) * (j.lo : ℝ)) ((i.lo : ℝ) * (j.hi : ℝ)))
          (max ((i.hi : ℝ) * (j.lo : ℝ)) ((i.hi : ℝ) * (j.hi : ℝ))) := by
    by_cases hy0 : 0 ≤ y
    · exact (mul_le_mul_of_nonneg_right hx.2 hy0).trans
        ((corner_upper i.hi).trans (le_max_right _ _))
    · have hy0' : y ≤ 0 := le_of_not_ge hy0
      exact (mul_le_mul_of_nonpos_right hx.1 hy0').trans
        ((corner_upper i.lo).trans (le_max_left _ _))
  constructor
  · simpa [mul, LeanSuffixReflective.QInterval.RealContains] using hlo
  · simpa [mul, LeanSuffixReflective.QInterval.RealContains] using hhi

/-- Real soundness of nonnegative rational scaling. -/
theorem realContains_nsmul {i : QInterval} {x : ℝ} {q : ℚ} (hq : 0 ≤ q)
    (hx : i.RealContains x) : (i.nsmul q hq).RealContains ((q : ℝ) * x) := by
  constructor
  · simpa [LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.RealContains] using
      mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hq)
  · simpa [LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.RealContains] using
      mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hq)

/-- Real soundness of a positive reciprocal certificate. -/
theorem realContains_recipPos {i : QInterval} {x : ℝ} (hi : 0 < i.lo)
    (hx : i.RealContains x) : (i.recipPos hi).RealContains (1 / x) := by
  have hiR : 0 < (i.lo : ℝ) := by exact_mod_cast hi
  have hxpos : 0 < x := hiR.trans_le hx.1
  constructor
  · simpa [recipPos, LeanSuffixReflective.QInterval.RealContains] using
      one_div_le_one_div_of_le hxpos hx.2
  · simpa [recipPos, LeanSuffixReflective.QInterval.RealContains] using
      one_div_le_one_div_of_le hiR hx.1

/-- Real soundness of division by a positive interval. -/
theorem realContains_divPos {i j : QInterval} {x y : ℝ} (hj : 0 < j.lo)
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (i.divPos j hj).RealContains (x / y) := by
  unfold divPos
  rw [div_eq_mul_one_div]
  exact realContains_mul hx (realContains_recipPos hj hy)

/-- Soundness kernel for centered mean-value interval evaluation.  The output
enclosure is derived, not assumed: the mean value theorem supplies one shared
intermediate point, `slope` encloses the derivative expression at that point,
and ordinary interval addition and multiplication finish the check. -/
theorem realContains_centered_meanValue
    (f f' : ℝ → ℝ) {c h : ℝ}
    (base slope displacement : QInterval)
    (hderiv : ∀ x ∈ Set.uIcc c h, HasDerivAt f (f' x) x)
    (hbase : base.RealContains (f c))
    (hslope : ∀ x ∈ Set.uIcc c h, slope.RealContains (f' x))
    (hdisplacement : displacement.RealContains (h - c)) :
    (base.add (slope.mul displacement)).RealContains (f h) := by
  rcases LeanSuffixAnalytic.centered_meanValue_exists f f' hderiv with
    ⟨ξ, hξ, hmean⟩
  rw [hmean]
  exact LeanSuffixReflective.QInterval.realContains_add hbase
    (realContains_mul (hslope ξ hξ) hdisplacement)

/-- Rational square bounds imply a real square-root enclosure. -/
theorem realContains_sqrt {i : QInterval} {x : ℝ}
    (hlo : 0 ≤ i.lo) (hloSq : (i.lo : ℝ) ^ 2 ≤ x)
    (hhiSq : x ≤ (i.hi : ℝ) ^ 2) : i.RealContains (sqrt x) := by
  have hhi : 0 ≤ (i.hi : ℝ) := by exact_mod_cast (hlo.trans i.ordered)
  exact ⟨Real.le_sqrt_of_sq_le hloSq, Real.sqrt_le_iff.2 ⟨hhi, hhiSq⟩⟩

/-- Strict sign transfer from an exact rational upper endpoint. -/
theorem negative_of_realContains {i : QInterval} {x : ℝ}
    (hx : i.RealContains x) (hi : i.hi < 0) : x < 0 := by
  have hiR : (i.hi : ℝ) < 0 := by exact_mod_cast hi
  exact hx.2.trans_lt hiR

/-- Strict sign transfer from an exact rational lower endpoint. -/
theorem positive_of_realContains {i : QInterval} {x : ℝ}
    (hx : i.RealContains x) (hi : 0 < i.lo) : 0 < x := by
  have hiR : 0 < (i.lo : ℝ) := by exact_mod_cast hi
  exact hiR.trans_le hx.1

end QInterval

/-- Expression language whose analytic atoms carry proved real enclosures. -/
inductive CertificateExpr where
  | rational (q : ℚ)
  | atom (x : ℝ) (i : QInterval) (sound : i.RealContains x)
  | add (a b : CertificateExpr)
  | neg (a : CertificateExpr)
  | mul (a b : CertificateExpr)

namespace CertificateExpr

def value : CertificateExpr → ℝ
  | rational q => q
  | atom x _ _ => x
  | add a b => a.value + b.value
  | neg a => -a.value
  | mul a b => a.value * b.value

def enclosure : CertificateExpr → QInterval
  | rational q => LeanSuffixReflective.QInterval.point q
  | atom _ i _ => i
  | add a b => a.enclosure.add b.enclosure
  | neg a => a.enclosure.neg
  | mul a b => a.enclosure.mul b.enclosure

/-- Generic kernel soundness for every certificate expression. -/
theorem sound (e : CertificateExpr) : e.enclosure.RealContains e.value := by
  induction e with
  | rational q => exact
      (LeanSuffixReflective.QInterval.realContains_point q (q : ℝ)).2 rfl
  | atom x i h => exact h
  | add a b ha hb => exact LeanSuffixReflective.QInterval.realContains_add ha hb
  | neg a ha => exact LeanSuffixReflective.QInterval.realContains_neg ha
  | mul a b ha hb => exact QInterval.realContains_mul ha hb

/-- Checked negativity proves a proposition about the represented real value. -/
theorem value_neg_of_hi_neg (e : CertificateExpr) (h : e.enclosure.hi < 0) :
    e.value < 0 := QInterval.negative_of_realContains e.sound h

end CertificateExpr

def piInterval : QInterval :=
  ⟨3.141592, 3.141593, by norm_num⟩

theorem piInterval_sound : piInterval.RealContains π := by
  simpa [piInterval, LeanSuffixReflective.QInterval.RealContains] using
    And.intro Real.pi_gt_d6.le Real.pi_lt_d6.le

/-- Degree-27 sine polynomial used by the face-certificate checker. -/
def sinTaylor27 (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 14, (-1 : ℚ) ^ k * x ^ (2 * k + 1) /
    (2 * k + 1).factorial

/-- Degree-26 cosine polynomial used by the face-certificate checker. -/
def cosTaylor26 (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 14, (-1 : ℚ) ^ k * x ^ (2 * k) /
    (2 * k).factorial

/-- Degree-27 sine enclosure with the exact Lagrange radius `|x|^28 / 28!`. -/
def sinTaylor27Interval (x : ℚ) : QInterval :=
  let p := sinTaylor27 x
  let r := |x| ^ 28 / (Nat.factorial 28 : ℚ)
  ⟨p - r, p + r, by linarith [show 0 ≤ r by positivity]⟩

/-- Degree-26 cosine enclosure with the exact Lagrange radius `|x|^27 / 27!`. -/
def cosTaylor26Interval (x : ℚ) : QInterval :=
  let p := cosTaylor26 x
  let r := |x| ^ 27 / (Nat.factorial 27 : ℚ)
  ⟨p - r, p + r, by linarith [show 0 ≤ r by positivity]⟩

private theorem sin_bound27 (x : ℝ) :
    |sin x - ∑ k ∈ Finset.range 14,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
      |x| ^ 28 / Nat.factorial 28 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0x : (0 : ℝ) ≠ x := Ne.symm hx
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := uniqueDiffOn_uIcc h0x
  obtain ⟨y, -, hry⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := sin) (x₀ := 0) (x := x) (n := 27)
    h0x Real.contDiff_sin.contDiffOn
  have ht : taylorWithinEval sin 27 (uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
        (2 * k + 1).factorial := by
    rw [taylor_within_apply]
    simp_rw [iteratedDerivWithin_eq_iteratedDeriv hu
      Real.contDiff_sin.contDiffAt left_mem_uIcc]
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [ht] at hry
  rw [hry]
  have hderiv : iteratedDeriv 28 sin y = sin y := by
    simpa using congrFun (Real.iteratedDeriv_even_sin 14) y
  rw [hderiv, abs_div, abs_mul, abs_pow]
  simp only [sub_zero]
  norm_num [Nat.factorial]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one y))
    (by positivity)

private theorem cos_bound26 (x : ℝ) :
    |cos x - ∑ k ∈ Finset.range 14,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      |x| ^ 27 / Nat.factorial 27 := by
  by_cases hx : x = 0
  · norm_num [hx, Finset.sum_range_succ, Nat.factorial]
  have h0x : (0 : ℝ) ≠ x := Ne.symm hx
  have hu : UniqueDiffOn ℝ (uIcc 0 x) := uniqueDiffOn_uIcc h0x
  obtain ⟨y, -, hry⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := cos) (x₀ := 0) (x := x) (n := 26)
    h0x Real.contDiff_cos.contDiffOn
  have ht : taylorWithinEval cos 26 (uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * x ^ (2 * k) /
        (2 * k).factorial := by
    rw [taylor_within_apply]
    simp_rw [iteratedDerivWithin_eq_iteratedDeriv hu
      Real.contDiff_cos.contDiffAt left_mem_uIcc]
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [ht] at hry
  rw [hry]
  have hderiv : iteratedDeriv 27 cos y = sin y := by
    simpa using congrFun (Real.iteratedDeriv_odd_cos 13) y
  rw [hderiv, abs_div, abs_mul, abs_pow]
  simp only [sub_zero]
  norm_num [Nat.factorial]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one y))
    (by positivity)

/-- Kernel proof of the exact degree-27 rational sine enclosure. -/
theorem sinTaylor27Interval_sound (x : ℚ) :
    (sinTaylor27Interval x).RealContains (sin (x : ℝ)) := by
  have h := abs_le.1 (sin_bound27 (x : ℝ))
  simpa [sinTaylor27Interval, sinTaylor27,
      LeanSuffixReflective.QInterval.RealContains] using
    (show
      ((∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
          (2 * k + 1).factorial) - |(x : ℝ)| ^ 28 / Nat.factorial 28 ≤
          sin (x : ℝ)) ∧
       (sin (x : ℝ) ≤
          (∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) /
            (2 * k + 1).factorial) + |(x : ℝ)| ^ 28 / Nat.factorial 28) by
      constructor <;> linarith [h.1, h.2])

/-- Kernel proof of the exact degree-26 rational cosine enclosure. -/
theorem cosTaylor26Interval_sound (x : ℚ) :
    (cosTaylor26Interval x).RealContains (cos (x : ℝ)) := by
  have h := abs_le.1 (cos_bound26 (x : ℝ))
  simpa [cosTaylor26Interval, cosTaylor26,
      LeanSuffixReflective.QInterval.RealContains] using
    (show
      ((∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) /
          (2 * k).factorial) - |(x : ℝ)| ^ 27 / Nat.factorial 27 ≤
          cos (x : ℝ)) ∧
       (cos (x : ℝ) ≤
          (∑ k ∈ Finset.range 14, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) /
            (2 * k).factorial) + |(x : ℝ)| ^ 27 / Nat.factorial 27) by
      constructor <;> linarith [h.1, h.2])

/-- Sine endpoint certificates extend to a principal-branch interval. -/
theorem realContains_sin_interval {input output : QInterval} {x : ℝ}
    (hx : input.RealContains x)
    (hbranch : -(π / 2) ≤ (input.lo : ℝ) ∧ (input.hi : ℝ) ≤ π / 2)
    (hlo : (output.lo : ℝ) ≤ sin (input.lo : ℝ))
    (hhi : sin (input.hi : ℝ) ≤ (output.hi : ℝ)) :
    output.RealContains (sin x) := by
  constructor
  · exact hlo.trans (Real.sin_le_sin_of_le_of_le_pi_div_two hbranch.1
      (hx.2.trans hbranch.2) hx.1)
  · exact (Real.sin_le_sin_of_le_of_le_pi_div_two
      (hbranch.1.trans hx.1) hbranch.2 hx.2).trans hhi

/-- Cosine endpoint certificates extend to a principal-branch interval. -/
theorem realContains_cos_interval {input output : QInterval} {x : ℝ}
    (hx : input.RealContains x)
    (hbranch : 0 ≤ (input.lo : ℝ) ∧ (input.hi : ℝ) ≤ π)
    (hlo : (output.lo : ℝ) ≤ cos (input.hi : ℝ))
    (hhi : cos (input.lo : ℝ) ≤ (output.hi : ℝ)) :
    output.RealContains (cos x) := by
  constructor
  · exact hlo.trans (Real.cos_le_cos_of_nonneg_of_le_pi
      (hbranch.1.trans hx.1) hbranch.2 hx.2)
  · exact (Real.cos_le_cos_of_nonneg_of_le_pi hbranch.1
      (hx.2.trans hbranch.2) hx.1).trans hhi

/-- Lift the degree-27 point certificates over a monotone sine interval.
`hordered` is an exact-rational check on the resulting endpoints. -/
def sinTaylor27On (input : QInterval)
    (hordered :
      (sinTaylor27Interval input.lo).lo ≤
        (sinTaylor27Interval input.hi).hi) : QInterval :=
  ⟨(sinTaylor27Interval input.lo).lo,
    (sinTaylor27Interval input.hi).hi, hordered⟩

theorem sinTaylor27On_sound {input : QInterval} {x : ℝ}
    (hordered :
      (sinTaylor27Interval input.lo).lo ≤
        (sinTaylor27Interval input.hi).hi)
    (hx : input.RealContains x)
    (hbranch : -(π / 2) ≤ (input.lo : ℝ) ∧
      (input.hi : ℝ) ≤ π / 2) :
    (sinTaylor27On input hordered).RealContains (sin x) := by
  apply realContains_sin_interval hx hbranch
  · simpa [sinTaylor27On] using (sinTaylor27Interval_sound input.lo).1
  · simpa [sinTaylor27On] using (sinTaylor27Interval_sound input.hi).2

/-- Lift the degree-26 point certificates over a nonnegative monotone cosine
interval. `hordered` is an exact-rational check on the resulting endpoints. -/
def cosTaylor26On (input : QInterval)
    (hordered :
      (cosTaylor26Interval input.hi).lo ≤
        (cosTaylor26Interval input.lo).hi) : QInterval :=
  ⟨(cosTaylor26Interval input.hi).lo,
    (cosTaylor26Interval input.lo).hi, hordered⟩

theorem cosTaylor26On_sound {input : QInterval} {x : ℝ}
    (hordered :
      (cosTaylor26Interval input.hi).lo ≤
        (cosTaylor26Interval input.lo).hi)
    (hx : input.RealContains x)
    (hbranch : 0 ≤ (input.lo : ℝ) ∧ (input.hi : ℝ) ≤ π) :
    (cosTaylor26On input hordered).RealContains (cos x) := by
  apply realContains_cos_interval hx hbranch
  · simpa [cosTaylor26On] using (cosTaylor26Interval_sound input.hi).1
  · simpa [cosTaylor26On] using (cosTaylor26Interval_sound input.lo).2

/-- Inverse-sine enclosure through principal-branch sine bounds. -/
theorem realContains_arcsin_of_sin_bounds {i : QInterval} {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1)
    (hbranch : (i.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (i.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2))
    (hlo : sin (i.lo : ℝ) ≤ x) (hhi : x ≤ sin (i.hi : ℝ)) :
    i.RealContains (arcsin x) := by
  exact ⟨(Real.le_arcsin_iff_sin_le hbranch.1 hx).2 hlo,
    (Real.arcsin_le_iff_le_sin hx hbranch.2).2 hhi⟩

/-- `arccos x = π/2-arcsin x` transports primitive enclosures. -/
theorem realContains_arccos_of_arcsin {p a : QInterval} {x : ℝ}
    (hp : p.RealContains π) (ha : a.RealContains (arcsin x)) :
    ((p.nsmul (1 / 2) (by norm_num)).sub a).RealContains (arccos x) := by
  have hp2 := QInterval.realContains_nsmul (q := (1 / 2 : ℚ)) (by norm_num) hp
  have h := LeanSuffixReflective.QInterval.realContains_sub hp2 ha
  simpa [Real.arccos, div_eq_mul_inv, mul_comm] using h

/-- One-dimensional opposite-face lemma for scalar IVT seams. -/
theorem oppositeFace_zero {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ x ∈ Icc a b, f x = 0 := by
  rcases intermediate_value_Icc hab hf
      (show (0 : ℝ) ∈ Icc (f a) (f b) from ⟨ha, hb⟩) with ⟨x, hx, hzero⟩
  exact ⟨x, hx, hzero⟩

abbrev Vec4 := Fin 4 → ℝ

def InSymmetricBox (r z : Vec4) : Prop := ∀ j, -r j ≤ z j ∧ z j ≤ r j


namespace FirstPrototypeCell

structure Brick where
  lamLo : ℚ
  lamHi : ℚ
  centers : Fin 4 → ℚ
  slopes : Fin 4 → ℚ
  yXiSlope : ℚ
  vRhoSlope : ℚ
  radii : Fin 4 → ℚ
  lamOrdered : lamLo < lamHi
  radiiPos : ∀ j, 0 < radii j

/-- Representative `[51/50, 102001/100000]` exact-data brick. -/
def brick : Brick where
  lamLo := 51 / 50
  lamHi := 102001 / 100000
  centers := ![925629104183851933 / 5000000000000000000,
    2705068892345424047 / 10000000000000000000,
    1046818865074353649 / 2500000000000000000,
    4608185511215091997 / 10000000000000000000]
  slopes := ![439944824343995293 / 200000000000000000,
    2510476247114540243 / 500000000000000000,
    6186129361874951931 / 1000000000000000000,
    3760062975752449919 / 500000000000000000]
  yXiSlope := 67 / 100
  vRhoSlope := 112 / 125
  radii := ![1 / 10000000, 1 / 100000000, 1 / 10000000, 1 / 100000000]
  lamOrdered := by norm_num
  radiiPos := by intro j; fin_cases j <;> norm_num

abbrev lamMid : ℚ := (brick.lamLo + brick.lamHi) / 2
abbrev tRadius : ℚ := (brick.lamHi - brick.lamLo) / 2

def tInterval : QInterval := ⟨-tRadius, tRadius, by norm_num [tRadius, brick]⟩
def lamInterval : QInterval := ⟨brick.lamLo, brick.lamHi, brick.lamOrdered.le⟩

theorem lambda_iff_centered {lam : ℝ} :
    lamInterval.RealContains lam ↔ tInterval.RealContains (lam - (lamMid : ℝ)) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;>
      norm_num [lamInterval, tInterval, lamMid, tRadius, brick,
        LeanSuffixReflective.QInterval.RealContains] at h₁ h₂ ⊢ <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;>
      norm_num [lamInterval, tInterval, lamMid, tRadius, brick,
        LeanSuffixReflective.QInterval.RealContains] at h₁ h₂ ⊢ <;> linarith

/-- Unconditional real-range conclusion for the representative cell. -/
theorem lambda_in_retainedSuffix {lam : ℝ} (h : lamInterval.RealContains lam) :
    LeanSuffixAnalytic.InRetainedSuffix lam := by
  unfold LeanSuffixAnalytic.InRetainedSuffix
  norm_num [lamInterval, LeanSuffixReflective.QInterval.RealContains, brick] at h ⊢
  exact ⟨h.1, h.2.trans (by norm_num)⟩

/-- The whole exact-data cell lies in the retained real suffix. -/
theorem representative_real_range :
    ∀ lam : ℝ, (51 / 50 : ℝ) ≤ lam → lam ≤ 102001 / 100000 →
      LeanSuffixAnalytic.InRetainedSuffix lam := by
  intro lam hlo hhi
  apply lambda_in_retainedSuffix
  simpa [lamInterval, LeanSuffixReflective.QInterval.RealContains, brick] using
    And.intro hlo hhi

structure Point where
  t : ℝ
  xi : ℝ
  eta : ℝ
  rho : ℝ
  sigma : ℝ

def lam (p : Point) : ℝ := (lamMid : ℝ) + p.t
def x (p : Point) : ℝ := brick.centers 0 + brick.slopes 0 * p.t + p.xi
def y (p : Point) : ℝ := brick.centers 1 + brick.slopes 1 * p.t +
  brick.yXiSlope * p.xi + p.eta
def w (p : Point) : ℝ := brick.centers 2 + brick.slopes 2 * p.t + p.rho
def v (p : Point) : ℝ := brick.centers 3 + brick.slopes 3 * p.t +
  brick.vRhoSlope * p.rho + p.sigma

def B4 (p : Point) : ℝ := lam p * y p + π / 2 - x p
def D4 (p : Point) : ℝ := sin (y p) - sin (x p)
def N4 (p : Point) : ℝ := B4 p + cos (x p) * D4 p
def B3 (p : Point) : ℝ := lam p * v p + π - w p
def D3 (p : Point) : ℝ := sin (v p) - sin (w p)
def N3 (p : Point) : ℝ := B3 p + (cos (w p) + 2) * D3 p

def C4 (p : Point) : ℝ := cos (x p) - lam p * cos (y p)
def F (p : Point) : ℝ := cos (x p) * D4 p - sin (x p) * sin (y p) * B4 p
def C3 (p : Point) : ℝ := cos (w p) - lam p * cos (v p)
def E (p : Point) : ℝ :=
  2 * cos (x p) ^ 2 * N3 p - (1 + cos (w p)) ^ 2 * N4 p
def G (p : Point) : ℝ :=
  cos (x p) * (B3 p + D3 p) - (1 + cos (w p)) * B4 p

/-- The shared analytic interpretation of the checker coordinates at a point
on the recorded angle branch.  The equation and sign fields deliberately take
their checker hypotheses as arguments, so the expensive trigonometric
translation is proved only once. -/
structure PointEquationSemantics (p : Point) : Prop where
  typeThreeHeight_gt_half : 1 / 2 < (1 + cos (w p)) / 2
  typeThreeHeight_lt_one : (1 + cos (w p)) / 2 < 1
  typeFourHeight_pos : 0 < cos (x p)
  typeFourHeight_lt_one : cos (x p) < 1
  equalArea_of_E_zero : E p = 0 →
    LeanSuffixAnalytic.typeThreeArea (lam p) ((1 + cos (w p)) / 2) =
      LeanSuffixAnalytic.typeFourArea (lam p) (cos (x p))
  stationary_of_F_zero : F p = 0 →
    LeanSuffixAnalytic.typeFourFold (lam p) (cos (x p)) = 0
  perimeter_lt_of_G_neg : G p < 0 →
    LeanSuffixAnalytic.typeThreePerimeter (lam p) ((1 + cos (w p)) / 2) <
      LeanSuffixAnalytic.typeFourPerimeter (lam p) (cos (x p))

/-- The checker coordinates have their intended analytic semantics on the
recorded angle branch. -/
theorem pointEquationSemantics
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4)
    (hC4 : C4 p = 0) (hC3 : C3 p = 0) :
    PointEquationSemantics p := by
  rcases hbranches with ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  have hpi4_lt_pi : π / 4 < π := by linarith [Real.pi_pos]
  have hpi4_lt_pi_div_two : π / 4 < π / 2 := by linarith [Real.pi_pos]
  have hxpi : x p < π := hxq.trans hpi4_lt_pi
  have hypi : y p < π := hyq.trans hpi4_lt_pi
  have hwpi : w p < π := hwq.trans hpi4_lt_pi
  have hvpi : v p < π := hvq.trans hpi4_lt_pi
  have hlam_pos : 0 < lam p := lt_trans (by norm_num) hlam
  have hxcos_pos : 0 < cos (x p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hxq.trans hpi4_lt_pi_div_two⟩
  have hwcos_pos : 0 < cos (w p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hwq.trans hpi4_lt_pi_div_two⟩
  have hzero_mem : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hx_mem : x p ∈ Icc 0 π := ⟨hx0.le, hxpi.le⟩
  have hw_mem : w p ∈ Icc 0 π := ⟨hw0.le, hwpi.le⟩
  have hxcos_lt_one : cos (x p) < 1 := by
    have h := Real.strictAntiOn_cos hzero_mem hx_mem hx0
    simpa using h
  have hwcos_lt_one : cos (w p) < 1 := by
    have h := Real.strictAntiOn_cos hzero_mem hw_mem hw0
    simpa using h
  have hxsin_pos : 0 < sin (x p) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hysin_pos : 0 < sin (y p) :=
    Real.sin_pos_of_pos_of_lt_pi hy0 hypi
  have hwsin_pos : 0 < sin (w p) :=
    Real.sin_pos_of_pos_of_lt_pi hw0 hwpi
  have hvsin_pos : 0 < sin (v p) :=
    Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
  have hcos_xy : cos (x p) = lam p * cos (y p) := by
    unfold C4 at hC4
    linarith
  have hcos_wv : cos (w p) = lam p * cos (v p) := by
    unfold C3 at hC3
    linarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape ((1 + cos (w p)) / 2) = cos (w p) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hcos_xy_div : cos (x p) / lam p = cos (y p) := by
    rw [hcos_xy]
    field_simp [ne_of_gt hlam_pos]
  have hcos_wv_div : cos (w p) / lam p = cos (v p) := by
    rw [hcos_wv]
    field_simp [ne_of_gt hlam_pos]
  have hB4 :
      LeanSuffixAnalytic.typeFourAngle (lam p) (cos (x p)) = B4 p := by
    rw [LeanSuffixAnalytic.typeFourAngle_eq_checker, hcos_xy_div,
      Real.arccos_cos hy0.le hypi.le, Real.arccos_cos hx0.le hxpi.le]
    rfl
  have hB3 :
      LeanSuffixAnalytic.typeThreeAngle (lam p)
          ((1 + cos (w p)) / 2) + π / 2 = B3 p := by
    rw [LeanSuffixAnalytic.typeThreeAngle_add_halfPi, hshape, hcos_wv_div,
      Real.arccos_cos hv0.le hvpi.le, Real.arccos_cos hw0.le hwpi.le]
    rfl
  have hsqrt_x : sqrt (1 - cos (x p) ^ 2) = sin (x p) := by
    have htrig := Real.sin_sq_add_cos_sq (x p)
    rw [show 1 - cos (x p) ^ 2 = sin (x p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hxsin_pos]
  have hsqrt_w : sqrt (1 - cos (w p) ^ 2) = sin (w p) := by
    have htrig := Real.sin_sq_add_cos_sq (w p)
    rw [show 1 - cos (w p) ^ 2 = sin (w p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hwsin_pos]
  have hsqrt_lam_x :
      sqrt (lam p ^ 2 - cos (x p) ^ 2) = lam p * sin (y p) := by
    have htrig := Real.sin_sq_add_cos_sq (y p)
    rw [show lam p ^ 2 - cos (x p) ^ 2 = (lam p * sin (y p)) ^ 2 by
      rw [hcos_xy]
      linear_combination -(lam p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hysin_pos)]
  have hsqrt_lam_w :
      sqrt (lam p ^ 2 - cos (w p) ^ 2) = lam p * sin (v p) := by
    have htrig := Real.sin_sq_add_cos_sq (v p)
    rw [show lam p ^ 2 - cos (w p) ^ 2 = (lam p * sin (v p)) ^ 2 by
      rw [hcos_wv]
      linear_combination -(lam p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hvsin_pos)]
  have hD4 :
      LeanSuffixAnalytic.typeFourDelta (lam p) (cos (x p)) = D4 p := by
    rw [LeanSuffixAnalytic.typeFourDelta, hsqrt_lam_x, hsqrt_x]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hD3 :
      LeanSuffixAnalytic.typeThreeDelta (lam p)
          ((1 + cos (w p)) / 2) = D3 p := by
    rw [LeanSuffixAnalytic.typeThreeDelta, hshape, hsqrt_lam_w, hsqrt_w]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hh3_pos : 0 < (1 + cos (w p)) / 2 := by linarith
  have hh4_pos : 0 < cos (x p) := hxcos_pos
  have equalArea_of_E_zero (hE : E p = 0) :
      LeanSuffixAnalytic.typeThreeArea (lam p) ((1 + cos (w p)) / 2) =
        LeanSuffixAnalytic.typeFourArea (lam p) (cos (x p)) := by
    rw [LeanSuffixAnalytic.typeThreeArea, LeanSuffixAnalytic.typeFourArea,
      hshape, hB3, hD3, hB4, hD4]
    apply (div_eq_div_iff (pow_ne_zero 2 (ne_of_gt hh3_pos))
      (pow_ne_zero 2 (ne_of_gt hh4_pos))).2
    unfold E N3 N4 at hE
    linear_combination (1 / 2 : ℝ) * hE
  have stationary_of_F_zero (hF : F p = 0) :
      LeanSuffixAnalytic.typeFourFold (lam p) (cos (x p)) = 0 := by
    have hden_ne : sin (x p) * sin (y p) ≠ 0 :=
      mul_ne_zero (ne_of_gt hxsin_pos) (ne_of_gt hysin_pos)
    have hnumerator :
        cos (x p) * (sin (y p) - sin (x p)) =
          sin (x p) * sin (y p) * B4 p := by
      unfold F D4 at hF
      linarith
    have hcore :
        cos (x p) * (1 / sin (x p) - 1 / sin (y p)) = B4 p := by
      calc
        cos (x p) * (1 / sin (x p) - 1 / sin (y p)) =
            (cos (x p) * (sin (y p) - sin (x p))) /
              (sin (x p) * sin (y p)) := by
                field_simp [ne_of_gt hxsin_pos, ne_of_gt hysin_pos]
        _ = B4 p := (div_eq_iff hden_ne).2 (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hnumerator)
    have hcancel : lam p / (lam p * sin (y p)) = 1 / sin (y p) := by
      field_simp [ne_of_gt hlam_pos, ne_of_gt hysin_pos]
    rw [LeanSuffixAnalytic.typeFourFold, hsqrt_x, hsqrt_lam_x, hB4,
      hcancel, hcore]
    ring
  have perimeter_lt_of_G_neg (hG : G p < 0) :
      LeanSuffixAnalytic.typeThreePerimeter (lam p)
          ((1 + cos (w p)) / 2) <
        LeanSuffixAnalytic.typeFourPerimeter (lam p) (cos (x p)) := by
    rw [LeanSuffixAnalytic.typeThreePerimeter,
      LeanSuffixAnalytic.typeFourPerimeter, hB3, hD3, hB4]
    apply (div_lt_div_iff₀ hh3_pos hh4_pos).2
    unfold G at hG
    nlinarith
  exact ⟨by linarith, by linarith, hxcos_pos, hxcos_lt_one,
    equalArea_of_E_zero, stationary_of_F_zero, perimeter_lt_of_G_neg⟩

/-- The primitive checker equations have their intended analytic meaning on
the recorded angle branch.  In particular, `E = 0` is equal weighted area,
`F = 0` is the type-(iv) stationary fold, and `G < 0` is strict type-(iii)
perimeter improvement. -/
theorem point_equations_to_scalar_improvement
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4)
    (hC4 : C4 p = 0) (hF : F p = 0)
    (hC3 : C3 p = 0) (hE : E p = 0) (hG : G p < 0) :
    let h₃ := (1 + cos (w p)) / 2
    let h₄ := cos (x p)
    1 / 2 < h₃ ∧ h₃ < 1 ∧
      0 < h₄ ∧ h₄ < 1 ∧
      LeanSuffixAnalytic.typeThreeArea (lam p) h₃ =
        LeanSuffixAnalytic.typeFourArea (lam p) h₄ ∧
      LeanSuffixAnalytic.typeFourFold (lam p) h₄ = 0 ∧
      LeanSuffixAnalytic.typeThreePerimeter (lam p) h₃ <
        LeanSuffixAnalytic.typeFourPerimeter (lam p) h₄ ∧
      LeanSuffixAnalytic.reducedFoldGap (lam p) h₃ h₄ < 0 := by
  dsimp only
  have hs := pointEquationSemantics p hlam hbranches hC4 hC3
  have harea := hs.equalArea_of_E_zero hE
  have hfold := hs.stationary_of_F_zero hF
  have hperimeter := hs.perimeter_lt_of_G_neg hG
  have hgap :=
    (LeanSuffixAnalytic.stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) hs.typeThreeHeight_gt_half))
      (ne_of_gt hs.typeFourHeight_pos) harea hfold).mp hperimeter
  exact ⟨hs.typeThreeHeight_gt_half, hs.typeThreeHeight_lt_one,
    hs.typeFourHeight_pos, hs.typeFourHeight_lt_one, harea, hfold,
    hperimeter, hgap⟩

def K3 (p : Point) : ℝ :=
  let h3 := (1 + cos (w p)) / 2
  4 * h3 * ((1 + cos (w p)) / sin (w p) -
    (lam p ^ 2 + cos (w p)) / (lam p * (lam p * sin (v p)))) -
    2 * (B3 p + D3 p)

/-- On the certified angle branch, the checker quantity `K3` is exactly the
numerator of the type-(iii) area derivative. -/
theorem typeThreeArea_deriv_eq_K3
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < w p ∧ w p < π / 4 ∧ 0 < v p ∧ v p < π / 4)
    (hC3 : C3 p = 0) :
    deriv (LeanSuffixAnalytic.typeThreeArea (lam p))
        ((1 + cos (w p)) / 2) =
      K3 p / ((1 + cos (w p)) / 2) ^ 3 := by
  rcases hbranches with ⟨hw0, hwq, hv0, hvq⟩
  have hpi4_lt_pi : π / 4 < π := by linarith [Real.pi_pos]
  have hpi4_lt_pi_div_two : π / 4 < π / 2 := by
    linarith [Real.pi_pos]
  have hwpi : w p < π := hwq.trans hpi4_lt_pi
  have hvpi : v p < π := hvq.trans hpi4_lt_pi
  have hlam_pos : 0 < lam p := lt_trans (by norm_num) hlam
  have hwcos_pos : 0 < cos (w p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hwq.trans hpi4_lt_pi_div_two⟩
  have hzero_mem : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hw_mem : w p ∈ Icc 0 π := ⟨hw0.le, hwpi.le⟩
  have hwcos_lt_one : cos (w p) < 1 := by
    have h := Real.strictAntiOn_cos hzero_mem hw_mem hw0
    simpa using h
  have hwsin_pos : 0 < sin (w p) :=
    Real.sin_pos_of_pos_of_lt_pi hw0 hwpi
  have hvsin_pos : 0 < sin (v p) :=
    Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
  have hcos_wv : cos (w p) = lam p * cos (v p) := by
    unfold C3 at hC3
    linarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape ((1 + cos (w p)) / 2) =
        cos (w p) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hcos_wv_div : cos (w p) / lam p = cos (v p) := by
    rw [hcos_wv]
    field_simp [ne_of_gt hlam_pos]
  have hB3 :
      LeanSuffixAnalytic.typeThreeAngle (lam p)
          ((1 + cos (w p)) / 2) + π / 2 = B3 p := by
    rw [LeanSuffixAnalytic.typeThreeAngle_add_halfPi, hshape, hcos_wv_div,
      Real.arccos_cos hv0.le hvpi.le, Real.arccos_cos hw0.le hwpi.le]
    rfl
  have hsqrt_w : sqrt (1 - cos (w p) ^ 2) = sin (w p) := by
    have htrig := Real.sin_sq_add_cos_sq (w p)
    rw [show 1 - cos (w p) ^ 2 = sin (w p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hwsin_pos]
  have hsqrt_lam_w :
      sqrt (lam p ^ 2 - cos (w p) ^ 2) = lam p * sin (v p) := by
    have htrig := Real.sin_sq_add_cos_sq (v p)
    rw [show lam p ^ 2 - cos (w p) ^ 2 =
        (lam p * sin (v p)) ^ 2 by
      rw [hcos_wv]
      linear_combination -(lam p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hvsin_pos)]
  have hD3 :
      LeanSuffixAnalytic.typeThreeDelta (lam p)
          ((1 + cos (w p)) / 2) = D3 p := by
    rw [LeanSuffixAnalytic.typeThreeDelta, hshape, hsqrt_lam_w, hsqrt_w]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hh3_pos : 0 < (1 + cos (w p)) / 2 := by linarith
  have hh3_one : (1 + cos (w p)) / 2 < 1 := by linarith
  rw [LeanSuffixAnalytic.typeThreeArea_deriv_eq_explicit
    hlam hh3_pos hh3_one, hshape, hsqrt_w, hsqrt_lam_w, hB3, hD3]
  unfold K3
  dsimp only
  field_simp [ne_of_gt hlam_pos, ne_of_gt hwsin_pos, ne_of_gt hvsin_pos]
  ring

def vars (p : Point) : Vec4 := ![p.xi, p.eta, p.rho, p.sigma]
def radiiReal : Vec4 := fun j => (brick.radii j : ℝ)
def pointOf (t : ℝ) (z : Vec4) : Point := ⟨t, z 0, z 1, z 2, z 3⟩

def rootMap (t : ℝ) (z : Vec4) : Vec4 :=
  let p := pointOf t z
  ![-F p, C4 p, E p, C3 p]

theorem rootMap_continuous (t : ℝ) : Continuous (rootMap t) := by
  apply continuous_pi
  intro j
  fin_cases j <;>
    simp [rootMap, F, C4, E, C3, N3, N4, B3, B4, D3, D4, pointOf,
      lam, x, y, w, v] <;> fun_prop

/-- Scalar form of `C4`, exposing the three correlated variables used by the
face certificate. -/
private def c4Reduced (t xi eta : ℝ) : ℝ :=
  cos ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi) -
    ((lamMid : ℝ) + t) *
      cos ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi + eta)

private theorem C4_pointOf_eq_c4Reduced (t : ℝ) (z : Vec4) :
    C4 (pointOf t z) = c4Reduced t (z 0) (z 1) := by
  rfl

/-- Scalar form of `F`, retaining the common `x`, `y`, and `B₄` arguments
throughout the face estimates. -/
private def fReduced (t xi eta : ℝ) : ℝ :=
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ll := (lamMid : ℝ) + t
  cos xx * (sin yy - sin xx) -
    sin xx * sin yy * (ll * yy + π / 2 - xx)

private theorem F_pointOf_eq_fReduced (t : ℝ) (z : Vec4) :
    F (pointOf t z) = fReduced t (z 0) (z 1) := by
  rfl

/-- Scalar form of `C3`, exposing the three correlated variables used by the
opposite-face certificate. -/
private def c3Reduced (t rho sigma : ℝ) : ℝ :=
  cos ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho) -
    ((lamMid : ℝ) + t) *
      cos ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
        brick.vRhoSlope * rho + sigma)

private theorem C3_pointOf_eq_c3Reduced (t : ℝ) (z : Vec4) :
    C3 (pointOf t z) = c3Reduced t (z 2) (z 3) := by
  rfl

/-- Scalar form of the equal-area residual, retaining all correlations between
the five affine variables. -/
private def eReduced (t xi eta rho sigma : ℝ) : ℝ :=
  let ll := (lamMid : ℝ) + t
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ww := (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho
  let vv := (brick.centers 3 : ℝ) + brick.slopes 3 * t +
    brick.vRhoSlope * rho + sigma
  let nn4 := ll * yy + π / 2 - xx + cos xx * (sin yy - sin xx)
  let nn3 := ll * vv + π - ww + (cos ww + 2) * (sin vv - sin ww)
  2 * cos xx ^ 2 * nn3 - (1 + cos ww) ^ 2 * nn4

private theorem E_pointOf_eq_eReduced (t : ℝ) (z : Vec4) :
    E (pointOf t z) = eReduced t (z 0) (z 1) (z 2) (z 3) := by
  rfl

/-- Directional derivative of the five-variable equal-area formula. -/
private def eFormulaDeriv (ll xx yy ww vv dl dx dy dw dv : ℝ) : ℝ :=
  let nn4 := ll * yy + π / 2 - xx + cos xx * (sin yy - sin xx)
  let nn3 := ll * vv + π - ww + (cos ww + 2) * (sin vv - sin ww)
  let dn4 := dl * yy + ll * dy - dx +
    (-sin xx * dx) * (sin yy - sin xx) +
    cos xx * (cos yy * dy - cos xx * dx)
  let dn3 := dl * vv + ll * dv - dw +
    (-sin ww * dw) * (sin vv - sin ww) +
    (cos ww + 2) * (cos vv * dv - cos ww * dw)
  (-4 : ℝ) * cos xx * sin xx * dx * nn3 + 2 * cos xx ^ 2 * dn3 +
    2 * (1 + cos ww) * sin ww * dw * nn4 - (1 + cos ww) ^ 2 * dn4
/-- A reusable certificate expression for `eFormulaDeriv`.  Its arguments
carry the enclosures of the five affine variables, their eight trigonometric
values, and `π`; the directional coefficients are exact rationals. -/
private def eFormulaDerivExpr
    (ell ex ey ew ev esx ecx esy ecy esw ecw esv ecv ep :
      CertificateExpr) (dl dx dy dw dv : ℚ) : CertificateExpr :=
  let nn4 :=
    .add
      (.add
        (.add (.mul ell ey) (.mul (.rational (1 / 2)) ep))
        (.neg ex))
      (.mul ecx (.add esy (.neg esx)))
  let nn3 :=
    .add
      (.add (.add (.mul ell ev) ep) (.neg ew))
      (.mul (.add ecw (.rational 2)) (.add esv (.neg esw)))
  let dn4 :=
    .add
      (.add
        (.add
          (.add (.mul (.rational dl) ey) (.mul ell (.rational dy)))
          (.neg (.rational dx)))
        (.mul
          (.mul (.neg esx) (.rational dx))
          (.add esy (.neg esx))))
      (.mul ecx
        (.add
          (.mul ecy (.rational dy))
          (.neg (.mul ecx (.rational dx)))))
  let dn3 :=
    .add
      (.add
        (.add
          (.add (.mul (.rational dl) ev) (.mul ell (.rational dv)))
          (.neg (.rational dw)))
        (.mul
          (.mul (.neg esw) (.rational dw))
          (.add esv (.neg esw))))
      (.mul (.add ecw (.rational 2))
        (.add
          (.mul ecv (.rational dv))
          (.neg (.mul ecw (.rational dw)))))
  .add
    (.add
      (.mul
        (.mul
          (.mul (.mul (.rational (-4)) ecx) esx)
          (.rational dx))
        nn3)
      (.mul (.mul (.rational 2) (.mul ecx ecx)) dn3))
    (.add
      (.mul
        (.mul
          (.mul (.mul (.rational 2) (.add (.rational 1) ecw)) esw)
          (.rational dw))
        nn4)
      (.neg
        (.mul
          (.mul (.add (.rational 1) ecw) (.add (.rational 1) ecw))
          dn4)))

private def eReducedDerivT (t xi eta rho sigma : ℝ) : ℝ :=
  eFormulaDeriv ((lamMid : ℝ) + t)
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
    1 (brick.slopes 0) (brick.slopes 1) (brick.slopes 2) (brick.slopes 3)

private def eReducedDerivXi (t xi eta rho sigma : ℝ) : ℝ :=
  eFormulaDeriv ((lamMid : ℝ) + t)
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
    0 1 brick.yXiSlope 0 0

private def eReducedDerivEta (t xi eta rho sigma : ℝ) : ℝ :=
  eFormulaDeriv ((lamMid : ℝ) + t)
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
    0 0 1 0 0
private def eReducedDerivRho (t xi eta rho sigma : ℝ) : ℝ :=
  eFormulaDeriv ((lamMid : ℝ) + t)
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
    0 0 0 1 brick.vRhoSlope

private def eReducedDerivSigma (t xi eta rho sigma : ℝ) : ℝ :=
  eFormulaDeriv ((lamMid : ℝ) + t)
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
    0 0 0 0 1

private theorem eFormula_hasDerivAt
    {lf xf yf wf vf : ℝ → ℝ} {q ll xx yy ww vv dl dx dy dw dv : ℝ}
    (hl : HasDerivAt lf dl q) (hx : HasDerivAt xf dx q)
    (hy : HasDerivAt yf dy q) (hw : HasDerivAt wf dw q)
    (hv : HasDerivAt vf dv q)
    (hll : lf q = ll) (hxx : xf q = xx) (hyy : yf q = yy)
    (hww : wf q = ww) (hvv : vf q = vv) :
    HasDerivAt
      (fun u =>
        let nn4 := lf u * yf u + π / 2 - xf u +
          cos (xf u) * (sin (yf u) - sin (xf u))
        let nn3 := lf u * vf u + π - wf u +
          (cos (wf u) + 2) * (sin (vf u) - sin (wf u))
        2 * cos (xf u) ^ 2 * nn3 - (1 + cos (wf u)) ^ 2 * nn4)
      (eFormulaDeriv ll xx yy ww vv dl dx dy dw dv) q := by
  subst ll
  subst xx
  subst yy
  subst ww
  subst vv
  have hsx := (Real.hasDerivAt_sin (xf q)).comp q hx
  have hcx := (Real.hasDerivAt_cos (xf q)).comp q hx
  have hsy := (Real.hasDerivAt_sin (yf q)).comp q hy
  have hcy := (Real.hasDerivAt_cos (yf q)).comp q hy
  have hsw := (Real.hasDerivAt_sin (wf q)).comp q hw
  have hcw := (Real.hasDerivAt_cos (wf q)).comp q hw
  have hsv := (Real.hasDerivAt_sin (vf q)).comp q hv
  have hcv := (Real.hasDerivAt_cos (vf q)).comp q hv
  have hn4 :=
    (((hl.mul hy).add (hasDerivAt_const q (π / 2))).sub hx).add
      (hcx.mul (hsy.sub hsx))
  have hn3 :=
    (((hl.mul hv).add (hasDerivAt_const q π)).sub hw).add
      ((hcw.add_const 2).mul (hsv.sub hsw))
  have he :=
    (((hasDerivAt_const q 2).mul (hcx.pow 2)).mul hn3).sub
      (((hasDerivAt_const q 1).add hcw).pow 2 |>.mul hn4)
  convert he using 1 <;> try rfl
  simp [Function.comp_apply, eFormulaDeriv]
  ring

private theorem hasDerivAt_affine (a b c q : ℝ) :
    HasDerivAt (fun u => a + b * u + c) b q := by
  convert ((hasDerivAt_const q a).add
    ((hasDerivAt_const q b).mul (hasDerivAt_id q))).add
      (hasDerivAt_const q c) using 1 <;>
    first | rfl | ring_nf

private theorem eReduced_hasDerivAt_t (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => eReduced u xi eta rho sigma)
      (eReducedDerivT t xi eta rho sigma) t := by
  have hl : HasDerivAt (fun u : ℝ => (lamMid : ℝ) + u) 1 t := by
    convert hasDerivAt_affine (lamMid : ℝ) 1 0 t using 1 <;>
      first | rfl | ring_nf
  have hx : HasDerivAt
      (fun u : ℝ => (brick.centers 0 : ℝ) + brick.slopes 0 * u + xi)
      (brick.slopes 0 : ℝ) t :=
    hasDerivAt_affine _ _ _ _
  have hy : HasDerivAt
      (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * u +
        brick.yXiSlope * xi + eta) (brick.slopes 1 : ℝ) t := by
    convert hasDerivAt_affine (brick.centers 1 : ℝ) (brick.slopes 1 : ℝ)
      ((brick.yXiSlope : ℝ) * xi + eta) t using 1 <;>
        first | rfl | ring_nf
  have hw : HasDerivAt
      (fun u : ℝ => (brick.centers 2 : ℝ) + brick.slopes 2 * u + rho)
      (brick.slopes 2 : ℝ) t :=
    hasDerivAt_affine _ _ _ _
  have hv : HasDerivAt
      (fun u : ℝ => (brick.centers 3 : ℝ) + brick.slopes 3 * u +
        brick.vRhoSlope * rho + sigma) (brick.slopes 3 : ℝ) t := by
    convert hasDerivAt_affine (brick.centers 3 : ℝ) (brick.slopes 3 : ℝ)
      ((brick.vRhoSlope : ℝ) * rho + sigma) t using 1 <;>
        first | rfl | ring_nf
  exact eFormula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

private theorem eReduced_hasDerivAt_xi (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => eReduced t u eta rho sigma)
      (eReducedDerivXi t xi eta rho sigma) xi := by
  have hl := hasDerivAt_const xi ((lamMid : ℝ) + t)
  have hx : HasDerivAt
      (fun u : ℝ => (brick.centers 0 : ℝ) + brick.slopes 0 * t + u) 1 xi := by
    convert hasDerivAt_affine
      ((brick.centers 0 : ℝ) + brick.slopes 0 * t) 1 0 xi using 1 <;>
        first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * u + eta) (brick.yXiSlope : ℝ) xi := by
    convert hasDerivAt_affine
      ((brick.centers 1 : ℝ) + brick.slopes 1 * t) (brick.yXiSlope : ℝ)
        eta xi using 1 <;> first | rfl | ring_nf
  have hw := hasDerivAt_const xi
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
  have hv := hasDerivAt_const xi
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
  exact eFormula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

private theorem eReduced_hasDerivAt_eta (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => eReduced t xi u rho sigma)
      (eReducedDerivEta t xi eta rho sigma) eta := by
  have hl := hasDerivAt_const eta ((lamMid : ℝ) + t)
  have hx := hasDerivAt_const eta
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
  have hy : HasDerivAt
      (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi + u) 1 eta := by
    convert hasDerivAt_affine
      ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi) 1 0 eta using 1 <;>
          first | rfl | ring_nf
  have hw := hasDerivAt_const eta
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
  have hv := hasDerivAt_const eta
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho + sigma)
  exact eFormula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl
private theorem eReduced_hasDerivAt_rho (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => eReduced t xi eta u sigma)
      (eReducedDerivRho t xi eta rho sigma) rho := by
  have hl := hasDerivAt_const rho ((lamMid : ℝ) + t)
  have hx := hasDerivAt_const rho
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
  have hy := hasDerivAt_const rho
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
  have hw : HasDerivAt
      (fun u : ℝ => (brick.centers 2 : ℝ) + brick.slopes 2 * t + u) 1 rho := by
    convert hasDerivAt_affine
      ((brick.centers 2 : ℝ) + brick.slopes 2 * t) 1 0 rho using 1 <;>
        first | rfl | ring_nf
  have hv : HasDerivAt
      (fun u : ℝ => (brick.centers 3 : ℝ) + brick.slopes 3 * t +
        brick.vRhoSlope * u + sigma) (brick.vRhoSlope : ℝ) rho := by
    convert hasDerivAt_affine
      ((brick.centers 3 : ℝ) + brick.slopes 3 * t)
        (brick.vRhoSlope : ℝ) sigma rho using 1 <;>
          first | rfl | ring_nf
  exact eFormula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

private theorem eReduced_hasDerivAt_sigma (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => eReduced t xi eta rho u)
      (eReducedDerivSigma t xi eta rho sigma) sigma := by
  have hl := hasDerivAt_const sigma ((lamMid : ℝ) + t)
  have hx := hasDerivAt_const sigma
    ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)
  have hy := hasDerivAt_const sigma
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi + eta)
  have hw := hasDerivAt_const sigma
    ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)
  have hv : HasDerivAt
      (fun u : ℝ => (brick.centers 3 : ℝ) + brick.slopes 3 * t +
        brick.vRhoSlope * rho + u) 1 sigma := by
    convert hasDerivAt_affine
      ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
        brick.vRhoSlope * rho) 1 0 sigma using 1 <;>
          first | rfl | ring_nf
  exact eFormula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

/-- A one-dimensional mean-value estimate which retains the shared argument
of every occurrence in the derivative. -/
private theorem abs_image_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {R M u : ℝ}
    (hR : 0 ≤ R) (hu : u ∈ Icc (-R) R)
    (hderiv : ∀ q ∈ Icc (-R) R, HasDerivAt f (f' q) q)
    (hbound : ∀ q ∈ Icc (-R) R, |f' q| ≤ M) :
    |f u - f 0| ≤ M * |u| := by
  have hzero : (0 : ℝ) ∈ Icc (-R) R := by
    constructor <;> linarith
  have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (C := M)
    (fun q hq => (hderiv q hq).hasFDerivAt.hasFDerivWithinAt)
    (fun q hq => by
      simpa [Real.norm_eq_abs] using hbound q hq)
    hzero hu
  simpa [Real.norm_eq_abs] using h

/-- Exact Taylor enclosure for every type-(iv) `x` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c4_sin_x_range {q : ℝ}
    (hq : (18511 / 100000 : ℝ) ≤ q ∧ q ≤ 18514 / 100000) :
    (184054 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (184085 / 1000000 : ℝ) := by
  have hmonoLo : sin (18511 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (18514 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (18511 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (18514 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iv) `cos x` occurring in the
`F` face estimates. -/
private theorem c4_cos_x_range {q : ℝ}
    (hq : (18511 / 100000 : ℝ) ≤ q ∧ q ≤ 18514 / 100000) :
    (982910 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (982917 / 1000000 : ℝ) := by
  have hmonoLo : cos (18514 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (18511 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (18514 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (18511 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iv) `y` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c4_sin_y_range {q : ℝ}
    (hq : (27048 / 100000 : ℝ) ≤ q ∧ q ≤ 27054 / 100000) :
    (267194 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (267252 / 1000000 : ℝ) := by
  have hmonoLo : sin (27048 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (27054 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (27048 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (27054 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for the correlated `cos y` term in the `t`
derivative of `C4`. -/
private theorem c4_cos_y_range {q : ℝ}
    (hq : (27048 / 100000 : ℝ) ≤ q ∧ q ≤ 27054 / 100000) :
    (963626 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (963643 / 1000000 : ℝ) := by
  have hmonoLo : cos (27054 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (27048 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (27054 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (27048 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iii) `w` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c3_sin_w_range {q : ℝ}
    (hq : (41869 / 100000 : ℝ) ≤ q ∧ q ≤ 41877 / 100000) :
    (406563 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (406638 / 1000000 : ℝ) := by
  have hmonoLo : sin (41869 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (41877 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (41869 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (41877 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iii) `v` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c3_sin_v_range {q : ℝ}
    (hq : (46078 / 100000 : ℝ) ≤ q ∧ q ≤ 46086 / 100000) :
    (444646 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (444719 / 1000000 : ℝ) := by
  have hmonoLo : sin (46078 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (46086 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (46078 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (46086 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for the correlated `cos v` term in the `t`
derivative of `C3`. -/
private theorem c3_cos_v_range {q : ℝ}
    (hq : (46078 / 100000 : ℝ) ≤ q ∧ q ≤ 46086 / 100000) :
    (895670 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (895706 / 1000000 : ℝ) := by
  have hmonoLo : cos (46086 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (46078 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (46086 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (46078 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith


/- Tighter trigonometric enclosures used only for the cancellation-sensitive
`E` derivative.  The decimal endpoints are exact rationals. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_x_trig_range {q : ℝ}
    (hq : (18511472 / 100000000 : ℝ) ≤ q ∧
      q ≤ 18513692 / 100000000) :
    (18405929 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (18408112 / 100000000 : ℝ) ∧
      (98291105 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (98291515 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (18511472 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (18513692 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (18513692 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (18511472 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_y_trig_range {q : ℝ}
    (hq : (27048170 / 100000000 : ℝ) ≤ q ∧
      q ≤ 27053208 / 100000000) :
    (26719565 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (26724421 / 100000000 : ℝ) ∧
      (96362883 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (96364231 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (27048170 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (27053208 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (27053208 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (27048170 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_w_trig_range {q : ℝ}
    (hq : (41869651 / 100000000 : ℝ) ≤ q ∧
      q ≤ 41875858 / 100000000) :
    (40656990 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (40662662 / 100000000 : ℝ) ∧
      (91359443 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (91361968 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (41869651 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (41875858 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (41875858 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (41869651 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_v_trig_range {q : ℝ}
    (hq : (46078085 / 100000000 : ℝ) ≤ q ∧
      q ≤ 46085626 / 100000000) :
    (44464765 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (44471520 / 100000000 : ℝ) ∧
      (89567203 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (89570557 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (46078085 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (46085626 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (46085626 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (46078085 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith
/- A single correlation-preserving interval certificate bounds all five
directional derivatives of the equal-area residual on the representative
brick. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem eReduced_deriv_bounds {t xi eta rho sigma : ℝ}
    (ht : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta : -(1 / 100000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 100000000)
    (hrho : -(1 / 10000000 : ℝ) ≤ rho ∧ rho ≤ 1 / 10000000)
    (hsigma : -(1 / 100000000 : ℝ) ≤ sigma ∧
      sigma ≤ 1 / 100000000) :
    |eReducedDerivT t xi eta rho sigma| ≤ (51 / 10000 : ℝ) ∧
      |eReducedDerivXi t xi eta rho sigma| ≤ (39 / 1000 : ℝ) ∧
      |eReducedDerivEta t xi eta rho sigma| ≤ (721 / 100 : ℝ) ∧
      (189 / 100 : ℝ) ≤ eReducedDerivRho t xi eta rho sigma ∧
      |eReducedDerivSigma t xi eta rho sigma| ≤ (351 / 50 : ℝ) := by
  let ll := (lamMid : ℝ) + t
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ww := (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho
  let vv := (brick.centers 3 : ℝ) + brick.slopes 3 * t +
    brick.vRhoSlope * rho + sigma
  have hll : (51 / 50 : ℝ) ≤ ll ∧ ll ≤ 102001 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hxx : (18511472 / 100000000 : ℝ) ≤ xx ∧
      xx ≤ 18513692 / 100000000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (27048170 / 100000000 : ℝ) ≤ yy ∧
      yy ≤ 27053208 / 100000000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hww : (41869651 / 100000000 : ℝ) ≤ ww ∧
      ww ≤ 41875858 / 100000000 := by
    dsimp [ww]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    constructor <;> linarith
  have hvv : (46078085 / 100000000 : ℝ) ≤ vv ∧
      vv ≤ 46085626 / 100000000 := by
    dsimp [vv]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    constructor <;> linarith
  have hxtrig := e_x_trig_range hxx
  have hytrig := e_y_trig_range hyy
  have hwtrig := e_w_trig_range hww
  have hvtrig := e_v_trig_range hvv
  let ell : CertificateExpr := .atom ll
    ⟨51 / 50, 102001 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let ex : CertificateExpr := .atom xx
    ⟨18511472 / 100000000, 18513692 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let ey : CertificateExpr := .atom yy
    ⟨27048170 / 100000000, 27053208 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ew : CertificateExpr := .atom ww
    ⟨41869651 / 100000000, 41875858 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hww)
  let ev : CertificateExpr := .atom vv
    ⟨46078085 / 100000000, 46085626 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hvv)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨18405929 / 100000000, 18408112 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hxtrig.1 hxtrig.2.1)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨98291105 / 100000000, 98291515 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hxtrig.2.2.1 hxtrig.2.2.2)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨26719565 / 100000000, 26724421 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hytrig.1 hytrig.2.1)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨96362883 / 100000000, 96364231 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hytrig.2.2.1 hytrig.2.2.2)
  let esw : CertificateExpr := .atom (sin ww)
    ⟨40656990 / 100000000, 40662662 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hwtrig.1 hwtrig.2.1)
  let ecw : CertificateExpr := .atom (cos ww)
    ⟨91359443 / 100000000, 91361968 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hwtrig.2.2.1 hwtrig.2.2.2)
  let esv : CertificateExpr := .atom (sin vv)
    ⟨44464765 / 100000000, 44471520 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hvtrig.1 hvtrig.2.1)
  let ecv : CertificateExpr := .atom (cos vv)
    ⟨89567203 / 100000000, 89570557 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hvtrig.2.2.1 hvtrig.2.2.2)
  let ep : CertificateExpr := .atom π piInterval piInterval_sound
  let ed (dl dx dy dw dv : ℚ) : CertificateExpr :=
    eFormulaDerivExpr ell ex ey ew ev esx ecx esy ecy esw ecw esv ecv ep
      dl dx dy dw dv
  have hvalue (dl dx dy dw dv : ℚ) :
      (ed dl dx dy dw dv).value =
        eFormulaDeriv ll xx yy ww vv
          (dl : ℝ) (dx : ℝ) (dy : ℝ) (dw : ℝ) (dv : ℝ) := by
    simp [ed, eFormulaDerivExpr, ell, ex, ey, ew, ev, esx, ecx, esy, ecy,
      esw, ecw, esv, ecv, ep, CertificateExpr.value, eFormulaDeriv]
    ring
  have hvT :
      (ed 1 (brick.slopes 0) (brick.slopes 1) (brick.slopes 2)
        (brick.slopes 3)).value =
        eReducedDerivT t xi eta rho sigma := by
    rw [hvalue]
    simp [eReducedDerivT, ll, xx, yy, ww, vv]
  have hvXi :
      (ed 0 1 brick.yXiSlope 0 0).value =
        eReducedDerivXi t xi eta rho sigma := by
    rw [hvalue]
    simp [eReducedDerivXi, ll, xx, yy, ww, vv]
  have hvEta :
      (ed 0 0 1 0 0).value =
        eReducedDerivEta t xi eta rho sigma := by
    rw [hvalue]
    simp [eReducedDerivEta, ll, xx, yy, ww, vv]
  have hvRho :
      (ed 0 0 0 1 brick.vRhoSlope).value =
        eReducedDerivRho t xi eta rho sigma := by
    rw [hvalue]
    simp [eReducedDerivRho, ll, xx, yy, ww, vv]
  have hvSigma :
      (ed 0 0 0 0 1).value =
        eReducedDerivSigma t xi eta rho sigma := by
    rw [hvalue]
    simp [eReducedDerivSigma, ll, xx, yy, ww, vv]
  have hT := CertificateExpr.sound
    (ed 1 (brick.slopes 0) (brick.slopes 1) (brick.slopes 2)
      (brick.slopes 3))
  have hXi := CertificateExpr.sound (ed 0 1 brick.yXiSlope 0 0)
  have hEta := CertificateExpr.sound (ed 0 0 1 0 0)
  have hRho := CertificateExpr.sound (ed 0 0 0 1 brick.vRhoSlope)
  have hSigma := CertificateExpr.sound (ed 0 0 0 0 1)
  rw [hvT] at hT
  rw [hvXi] at hXi
  rw [hvEta] at hEta
  rw [hvRho] at hRho
  rw [hvSigma] at hSigma
  norm_num [ed, eFormulaDerivExpr, ell, ex, ey, ew, ev, esx, ecx, esy, ecy,
    esw, ecw, esv, ecv, ep, piInterval, CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    brick, Matrix.cons_val_two, Matrix.cons_val_three] at hT hXi hEta hRho hSigma
  constructor
  · rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  constructor
  · rw [abs_le]
    constructor <;> linarith [hXi.1, hXi.2]
  constructor
  · rw [abs_le]
    constructor <;> linarith [hEta.1, hEta.2]
  constructor
  · linarith [hRho.1]
  · rw [abs_le]
    constructor <;> linarith [hSigma.1, hSigma.2]

/-- Exact affine box arithmetic puts every angle in the analytic branch used by
the first prototype brick. -/
theorem affine_branches :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      let p := pointOf t z
      0 < x p ∧ x p < π / 4 ∧ 0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧ 0 < v p ∧ v p < π / 4 := by
  intro t z ht hz
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  dsimp only
  norm_num [pointOf, x, y, w, v, brick, Matrix.cons_val_two,
    Matrix.cons_val_three]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  · linarith [Real.pi_gt_d6]

/-- Exact affine box arithmetic separates the type-(iv) and type-(iii) angle
pairs throughout the first prototype brick. -/
theorem affine_angleOrder :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      let p := pointOf t z
      x p < y p ∧ w p < v p := by
  intro t z ht hz
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  dsimp only
  norm_num [pointOf, x, y, w, v, brick, Matrix.cons_val_two,
    Matrix.cons_val_three]
  constructor <;> linarith

/-- The type-(iii) equal-area branch is strictly descending throughout the
representative cell.  Coarse rational ranges suffice, but every trigonometric
endpoint is discharged by the degree-27/26 kernel certificates above. -/
theorem descendingK3 :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      K3 (pointOf t z) < 0 := by
  intro t z ht hz
  let p := pointOf t z
  have hz0 := hz 0
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz2 hz3
  have hlamLo : (1 : ℝ) < lam p := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hlamHi : lam p < (103 / 100 : ℝ) := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hwLo : (2 / 5 : ℝ) ≤ w p := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwHi : w p ≤ (21 / 50 : ℝ) := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvLo : (9 / 20 : ℝ) ≤ v p := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvHi : v p ≤ (47 / 100 : ℝ) := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwI :
      (⟨2 / 5, 21 / 50, by norm_num⟩ : QInterval).RealContains (w p) := by
    constructor <;> norm_num <;> assumption
  have hvI :
      (⟨9 / 20, 47 / 100, by norm_num⟩ : QInterval).RealContains (v p) := by
    constructor <;> norm_num <;> assumption
  have hsw :
      (⟨19 / 50, 21 / 50, by norm_num⟩ : QInterval).RealContains
        (sin (w p)) := by
    apply realContains_sin_interval hwI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (sinTaylor27Interval_sound (2 / 5)).1
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (sinTaylor27Interval_sound (21 / 50)).2
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hsv :
      (⟨2 / 5, 47 / 100, by norm_num⟩ : QInterval).RealContains
        (sin (v p)) := by
    apply realContains_sin_interval hvI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (sinTaylor27Interval_sound (9 / 20)).1
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (sinTaylor27Interval_sound (47 / 100)).2
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hsvHi : sin (v p) ≤ (47 / 100 : ℝ) := by
    norm_num
    nlinarith [hsv.2]
  have hcw :
      (⟨9 / 10, 93 / 100, by norm_num⟩ : QInterval).RealContains
        (cos (w p)) := by
    apply realContains_cos_interval hwI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (cosTaylor26Interval_sound (21 / 50)).1
      norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (cosTaylor26Interval_sound (2 / 5)).2
      norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hswPos : 0 < sin (w p) := lt_of_lt_of_le (by norm_num) hsw.1
  have hsvPos : 0 < sin (v p) := lt_of_lt_of_le (by norm_num) hsv.1
  have hlamPos : 0 < lam p := lt_trans (by norm_num) hlamLo
  have hlamSqPos : 0 < lam p ^ 2 := sq_pos_of_pos hlamPos
  have hA : (1 + cos (w p)) / sin (w p) < (51 / 10 : ℝ) := by
    apply (div_lt_iff₀ hswPos).2
    nlinarith [hcw.2, hsw.1]
  have hlamSqHi : lam p ^ 2 < (10609 / 10000 : ℝ) := by
    nlinarith
  have hdenHi :
      lam p * (lam p * sin (v p)) < (498623 / 1000000 : ℝ) := by
    rw [show lam p * (lam p * sin (v p)) =
      lam p ^ 2 * sin (v p) by ring]
    have h₁ :
        lam p ^ 2 * sin (v p) ≤ lam p ^ 2 * (47 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hsvHi hlamSqPos.le
    have h₂ :
        lam p ^ 2 * (47 / 100 : ℝ) <
          (10609 / 10000 : ℝ) * (47 / 100 : ℝ) :=
      mul_lt_mul_of_pos_right hlamSqHi (by norm_num)
    norm_num at h₂ ⊢
    exact h₁.trans_lt h₂
  have hdenPos : 0 < lam p * (lam p * sin (v p)) := by positivity
  have hnumLo : (19 / 10 : ℝ) < lam p ^ 2 + cos (w p) := by
    nlinarith [hcw.1]
  have hB : (19 / 5 : ℝ) <
      (lam p ^ 2 + cos (w p)) /
        (lam p * (lam p * sin (v p))) := by
    apply (lt_div_iff₀ hdenPos).2
    nlinarith [hnumLo, hdenHi]
  have hdiff :
      (1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p))) <
        (13 / 10 : ℝ) := by
    linarith
  have hfactorPos : 0 < 2 * (1 + cos (w p)) := by
    nlinarith [hcw.1]
  have hfactorHi : 2 * (1 + cos (w p)) ≤ (193 / 50 : ℝ) := by
    nlinarith [hcw.2]
  have hproduct :
      2 * (1 + cos (w p)) *
          ((1 + cos (w p)) / sin (w p) -
            (lam p ^ 2 + cos (w p)) /
              (lam p * (lam p * sin (v p)))) <
        (5018 / 1000 : ℝ) := by
    by_cases hd :
        0 ≤ (1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))
    · nlinarith [mul_lt_mul_of_pos_left hdiff hfactorPos,
        mul_le_mul_of_nonneg_right hfactorHi hd]
    · have hd' := lt_of_not_ge hd
      have hnegative := mul_neg_of_pos_of_neg hfactorPos hd'
      norm_num at hnegative ⊢
      linarith
  have hlamv : (9 / 20 : ℝ) < lam p * v p := by
    have hvPos : 0 < v p := lt_of_lt_of_le (by norm_num) hvLo
    nlinarith [mul_lt_mul_of_pos_right hlamLo hvPos]
  have hbase : (31 / 10 : ℝ) < B3 p + D3 p := by
    unfold B3 D3
    nlinarith [hlamv, Real.pi_gt_d6, hwHi, hsv.1, hsw.2]
  change K3 p < 0
  unfold K3
  dsimp only
  rw [show
    4 * ((1 + cos (w p)) / 2) *
        ((1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))) =
      2 * (1 + cos (w p)) *
        ((1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))) by ring]
  linarith

/-- A direct rational interval decomposition proves the scalar perimeter gap
throughout the first prototype brick.  The explicit negative margin keeps this
leaf independent of the root-existence argument. -/
theorem gap_upper :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      G (pointOf t z) < -(437 / 1000000 : ℝ) := by
  intro t z ht hz
  let p := pointOf t z
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  have hlamLo : (51 / 50 : ℝ) ≤ lam p := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hlamHi : lam p ≤ (102001 / 100000 : ℝ) := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hxLo : (1851 / 10000 : ℝ) ≤ x p := by
    dsimp [p, pointOf, x]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hxHi : x p ≤ (1852 / 10000 : ℝ) := by
    dsimp [p, pointOf, x]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hyLo : (2704 / 10000 : ℝ) ≤ y p := by
    dsimp [p, pointOf, y]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwLo : (4186 / 10000 : ℝ) ≤ w p := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwHi : w p ≤ (4188 / 10000 : ℝ) := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvLo : (4607 / 10000 : ℝ) ≤ v p := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvHi : v p ≤ (4609 / 10000 : ℝ) := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hcxHi : cos (x p) ≤ (983 / 1000 : ℝ) := by
    have hmono : cos (x p) ≤ cos (1851 / 10000 : ℝ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_gt_d6]) hxLo
    have h := (cosTaylor26Interval_sound (1851 / 10000)).2
    norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hcwLo : (9135 / 10000 : ℝ) ≤ cos (w p) := by
    have hmono : cos (4188 / 10000 : ℝ) ≤ cos (w p) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_gt_d6]) hwHi
    have h := (cosTaylor26Interval_sound (4188 / 10000)).1
    norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hsvHi : sin (v p) ≤ (4449 / 10000 : ℝ) := by
    have hmono : sin (v p) ≤ sin (4609 / 10000 : ℝ) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_d6]) hvHi
    have h := (sinTaylor27Interval_sound (4609 / 10000)).2
    norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hswLo : (4064 / 10000 : ℝ) ≤ sin (w p) := by
    have hmono : sin (4186 / 10000 : ℝ) ≤ sin (w p) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_d6]) hwLo
    have h := (sinTaylor27Interval_sound (4186 / 10000)).1
    norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hlamvHi : lam p * v p ≤
      (102001 / 100000 : ℝ) * (4609 / 10000 : ℝ) := by
    exact mul_le_mul hlamHi hvHi (by linarith) (by norm_num)
  have hlamyLo : (51 / 50 : ℝ) * (2704 / 10000 : ℝ) ≤
      lam p * y p := by
    exact mul_le_mul hlamLo hyLo (by norm_num) (by linarith)
  have hAHi : B3 p + D3 p < (3232 / 1000 : ℝ) := by
    unfold B3 D3
    linarith [Real.pi_lt_d6]
  have hALo : (0 : ℝ) < B3 p + D3 p := by
    unfold B3 D3
    have hsinv : -(1 : ℝ) ≤ sin (v p) := neg_one_le_sin _
    have hsinw : sin (w p) ≤ 1 := sin_le_one _
    nlinarith [Real.pi_gt_d6]
  have hBLo : (1661 / 1000 : ℝ) < B4 p := by
    unfold B4
    linarith [Real.pi_gt_d6]
  have hfirst : cos (x p) * (B3 p + D3 p) <
      (983 / 1000 : ℝ) * (3232 / 1000 : ℝ) := by
    have hcxPos : 0 < cos (x p) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
        by linarith [Real.pi_gt_d6]⟩
    have hmul := mul_lt_mul hAHi hcxHi hcxPos (by norm_num)
    nlinarith
  have hsecond : (1913 / 1000 : ℝ) * (1661 / 1000 : ℝ) <
      (1 + cos (w p)) * B4 p := by
    have hf : (1913 / 1000 : ℝ) < 1 + cos (w p) := by linarith
    exact mul_lt_mul hf hBLo.le (by norm_num) (by linarith)
  unfold G
  nlinarith [hfirst, hsecond]


/-- At `eta = 0`, the correlated `C4` residual stays within `31/20 · 10⁻⁹`.
The `t` and `xi` variations are bounded by mean value estimates rather than
decorrelating the two cosine arguments. -/
private theorem c4Reduced_eta_zero_abs_lt {t xi : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000) :
    |c4Reduced t xi 0| < (31 / 20000000000 : ℝ) := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hanchor :
      |c4Reduced 0 0 0| < (3 / 10000000000 : ℝ) := by
    have hxlo := (cosTaylor26Interval_sound (brick.centers 0)).1
    have hxhi := (cosTaylor26Interval_sound (brick.centers 0)).2
    have hylo := (cosTaylor26Interval_sound (brick.centers 1)).1
    have hyhi := (cosTaylor26Interval_sound (brick.centers 1)).2
    norm_num [c4Reduced, brick, lamMid, cosTaylor26Interval, cosTaylor26,
      Finset.sum_range_succ, Nat.factorial] at hxlo hxhi hylo hyhi ⊢
    rw [abs_lt]
    constructor <;> nlinarith
  have htChange :
      |c4Reduced t 0 0 - c4Reduced 0 0 0| ≤
        (11 / 50000 : ℝ) * |t| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => c4Reduced u 0 0)
      (f' := fun q =>
        -(brick.slopes 0 : ℝ) *
            sin ((brick.centers 0 : ℝ) + brick.slopes 0 * q) -
          cos ((brick.centers 1 : ℝ) + brick.slopes 1 * q) +
          (brick.slopes 1 : ℝ) * (((lamMid : ℝ) + q) *
            sin ((brick.centers 1 : ℝ) + brick.slopes 1 * q)))
      (R := (1 / 200000 : ℝ)) (M := (11 / 50000 : ℝ))
      (u := t) (by norm_num) ht'
    · intro q hq
      have hx : HasDerivAt
          (fun u : ℝ => (brick.centers 0 : ℝ) + brick.slopes 0 * u)
          (brick.slopes 0 : ℝ) q := by
        convert (hasDerivAt_const q (brick.centers 0 : ℝ)).add
            ((hasDerivAt_const q (brick.slopes 0 : ℝ)).mul
              (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      have hy : HasDerivAt
          (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * u)
          (brick.slopes 1 : ℝ) q := by
        convert (hasDerivAt_const q (brick.centers 1 : ℝ)).add
            ((hasDerivAt_const q (brick.slopes 1 : ℝ)).mul
              (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      have hlam : HasDerivAt (fun u : ℝ => (lamMid : ℝ) + u) 1 q := by
        convert (hasDerivAt_const q (lamMid : ℝ)).add (hasDerivAt_id q) using 1 <;>
          first | rfl | ring_nf
      convert ((Real.hasDerivAt_cos _).comp q hx).sub
          (hlam.mul ((Real.hasDerivAt_cos _).comp q hy)) using 1 <;> try rfl
      · funext u
        simp [c4Reduced, Function.comp_apply]
      · simp only [Function.comp_apply]
        ring
    · intro q hq
      have hq' : -(1 / 200000 : ℝ) ≤ q ∧ q ≤ 1 / 200000 := hq
      have hxArg :
          (18511 / 100000 : ℝ) ≤
              (brick.centers 0 : ℝ) + brick.slopes 0 * q ∧
            (brick.centers 0 : ℝ) + brick.slopes 0 * q ≤
              18514 / 100000 := by
        norm_num [brick]
        constructor <;> linarith
      have hyArg :
          (27048 / 100000 : ℝ) ≤
              (brick.centers 1 : ℝ) + brick.slopes 1 * q ∧
            (brick.centers 1 : ℝ) + brick.slopes 1 * q ≤
              27054 / 100000 := by
        norm_num [brick]
        constructor <;> linarith
      have hsx := c4_sin_x_range hxArg
      have hsy := c4_sin_y_range hyArg
      have hcy := c4_cos_y_range hyArg
      have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + q := by
        norm_num [lamMid, brick]
        linarith
      have hlamHi : (lamMid : ℝ) + q ≤ (102001 / 100000 : ℝ) := by
        norm_num [lamMid, brick]
        linarith
      have hprodLo :
          (51 / 50 : ℝ) * (267194 / 1000000 : ℝ) ≤
            ((lamMid : ℝ) + q) *
              sin ((brick.centers 1 : ℝ) + brick.slopes 1 * q) :=
        mul_le_mul hlamLo hsy.1 (by norm_num) (by linarith)
      have hprodHi :
          ((lamMid : ℝ) + q) *
              sin ((brick.centers 1 : ℝ) + brick.slopes 1 * q) ≤
            (102001 / 100000 : ℝ) * (267252 / 1000000 : ℝ) :=
        mul_le_mul hlamHi hsy.2 (by linarith) (by norm_num)
      rw [abs_le]
      norm_num [brick, lamMid] at hsx hsy hcy hprodLo hprodHi ⊢
      constructor <;> linarith
  have hxiChange :
      |c4Reduced t xi 0 - c4Reduced t 0 0| ≤
        (3 / 2000 : ℝ) * |xi| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => c4Reduced t u 0)
      (f' := fun q =>
        -sin ((brick.centers 0 : ℝ) + brick.slopes 0 * t + q) +
          (brick.yXiSlope : ℝ) * (((lamMid : ℝ) + t) *
            sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
              brick.yXiSlope * q)))
      (R := (1 / 10000000 : ℝ)) (M := (3 / 2000 : ℝ))
      (u := xi) (by norm_num) hxi
    · intro q hq
      have hx : HasDerivAt
          (fun u : ℝ =>
            (brick.centers 0 : ℝ) + brick.slopes 0 * t + u) 1 q := by
        convert (hasDerivAt_const q
            ((brick.centers 0 : ℝ) + brick.slopes 0 * t)).add
              (hasDerivAt_id q) using 1 <;>
          first | rfl | ring_nf
      have hy : HasDerivAt
          (fun u : ℝ =>
            (brick.centers 1 : ℝ) + brick.slopes 1 * t +
              brick.yXiSlope * u) (brick.yXiSlope : ℝ) q := by
        convert (hasDerivAt_const q
            ((brick.centers 1 : ℝ) + brick.slopes 1 * t)).add
              ((hasDerivAt_const q (brick.yXiSlope : ℝ)).mul
                (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      convert ((Real.hasDerivAt_cos _).comp q hx).sub
          ((hasDerivAt_const q ((lamMid : ℝ) + t)).mul
            ((Real.hasDerivAt_cos _).comp q hy)) using 1 <;> try rfl
      · funext u
        simp [c4Reduced, Function.comp_apply]
      · simp only [Function.comp_apply]
        ring
    · intro q hq
      have hq' : -(1 / 10000000 : ℝ) ≤ q ∧
          q ≤ 1 / 10000000 := hq
      have hxArg :
          (18511 / 100000 : ℝ) ≤
              (brick.centers 0 : ℝ) + brick.slopes 0 * t + q ∧
            (brick.centers 0 : ℝ) + brick.slopes 0 * t + q ≤
              18514 / 100000 := by
        norm_num [brick]
        constructor <;> linarith
      have hyArg :
          (27048 / 100000 : ℝ) ≤
              (brick.centers 1 : ℝ) + brick.slopes 1 * t +
                brick.yXiSlope * q ∧
            (brick.centers 1 : ℝ) + brick.slopes 1 * t +
                brick.yXiSlope * q ≤ 27054 / 100000 := by
        norm_num [brick]
        constructor <;> linarith
      have hsx := c4_sin_x_range hxArg
      have hsy := c4_sin_y_range hyArg
      have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
        norm_num [lamMid, brick]
        linarith
      have hlamHi : (lamMid : ℝ) + t ≤ (102001 / 100000 : ℝ) := by
        norm_num [lamMid, brick]
        linarith
      have hprodLo :
          (51 / 50 : ℝ) * (267194 / 1000000 : ℝ) ≤
            ((lamMid : ℝ) + t) *
              sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
                brick.yXiSlope * q) :=
        mul_le_mul hlamLo hsy.1 (by norm_num) (by linarith)
      have hprodHi :
          ((lamMid : ℝ) + t) *
              sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
                brick.yXiSlope * q) ≤
            (102001 / 100000 : ℝ) * (267252 / 1000000 : ℝ) :=
        mul_le_mul hlamHi hsy.2 (by linarith) (by norm_num)
      rw [abs_le]
      norm_num [brick, lamMid] at hsx hsy hprodLo hprodHi ⊢
      constructor <;> linarith
  have htAbs : |t| ≤ (1 / 200000 : ℝ) := (abs_le).2 ht'
  have hxiAbs : |xi| ≤ (1 / 10000000 : ℝ) := (abs_le).2 hxi
  have hsum :
      |c4Reduced t xi 0| ≤
        |c4Reduced t xi 0 - c4Reduced t 0 0| +
          |c4Reduced t 0 0 - c4Reduced 0 0 0| +
            |c4Reduced 0 0 0| := by
    calc
      |c4Reduced t xi 0| =
          |(c4Reduced t xi 0 - c4Reduced t 0 0) +
            (c4Reduced t 0 0 - c4Reduced 0 0 0) +
              c4Reduced 0 0 0| := by ring
      _ ≤ |(c4Reduced t xi 0 - c4Reduced t 0 0) +
              (c4Reduced t 0 0 - c4Reduced 0 0 0)| +
            |c4Reduced 0 0 0| := abs_add_le _ _
      _ ≤ |c4Reduced t xi 0 - c4Reduced t 0 0| +
              |c4Reduced t 0 0 - c4Reduced 0 0 0| +
            |c4Reduced 0 0 0| := by
        have hab := abs_add_le
          (c4Reduced t xi 0 - c4Reduced t 0 0)
          (c4Reduced t 0 0 - c4Reduced 0 0 0)
        linarith
  norm_num at htChange hxiChange htAbs hxiAbs hanchor hsum ⊢
  nlinarith

/-- Quantitative monotonicity in `eta`: on the complete first brick the
`eta` derivative of `C4` is at least the exact rational `109/400`. -/
private theorem c4Reduced_eta_growth {t xi eta₁ eta₂ : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta₁ : eta₁ ∈ Icc (-(1 / 100000000 : ℝ)) (1 / 100000000))
    (heta₂ : eta₂ ∈ Icc (-(1 / 100000000 : ℝ)) (1 / 100000000))
    (heta : eta₁ ≤ eta₂) :
    (109 / 400 : ℝ) * (eta₂ - eta₁) ≤
      c4Reduced t xi eta₂ - c4Reduced t xi eta₁ := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  apply (convex_Icc (-(1 / 100000000 : ℝ))
    (1 / 100000000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold c4Reduced; fun_prop) (by unfold c4Reduced; fun_prop) ?_
        eta₁ heta₁ eta₂ heta₂ heta
  intro q hq
  have hq' : -(1 / 100000000 : ℝ) < q ∧
      q < 1 / 100000000 := by
    simpa only [interior_Icc, mem_Ioo] using hq
  have hyArg :
      (27048 / 100000 : ℝ) ≤
          (brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + q ∧
        (brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + q ≤ 27054 / 100000 := by
    norm_num [brick]
    constructor <;> linarith
  have hsy := c4_sin_y_range hyArg
  have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
    norm_num [lamMid, brick]
    linarith
  have hprodLo :
      (51 / 50 : ℝ) * (267194 / 1000000 : ℝ) ≤
        ((lamMid : ℝ) + t) *
          sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + q) :=
    mul_le_mul hlamLo hsy.1 (by norm_num) (by linarith)
  have hy : HasDerivAt
      (fun u : ℝ =>
        (brick.centers 1 : ℝ) + brick.slopes 1 * t +
          brick.yXiSlope * xi + u) 1 q := by
    convert (hasDerivAt_const q
      ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi)).add (hasDerivAt_id q) using 1 <;>
      first | rfl | ring_nf
  have hC4 : HasDerivAt (fun u => c4Reduced t xi u)
      (((lamMid : ℝ) + t) *
        sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
          brick.yXiSlope * xi + q)) q := by
    convert (hasDerivAt_const q
        (cos ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi))).sub
      ((hasDerivAt_const q ((lamMid : ℝ) + t)).mul
        ((Real.hasDerivAt_cos _).comp q hy)) using 1 <;> try rfl
    simp only [Function.comp_apply]
    ring
  rw [hC4.deriv]
  norm_num [brick, lamMid] at hprodLo ⊢
  linarith

/-- The lower `eta` face has the required `C4` sign with the strict exact
rational margin `11/10 · 10⁻⁹`. -/
theorem C4_eta_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 1 = -radiiReal 1 →
      C4 (pointOf t z) < -(11 / 10000000000 : ℝ) := by
  intro t z ht hz heta
  have hxi := hz 0
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi
  have heta' : z 1 = -(1 / 100000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at heta
    exact heta
  have hzero := c4Reduced_eta_zero_abs_lt ht hxi
  have hgrowth := c4Reduced_eta_growth ht hxi
    (eta₁ := -(1 / 100000000 : ℝ)) (eta₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [C4_pointOf_eq_c4Reduced, heta']
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

/-- The upper `eta` face has the required `C4` sign with the strict exact
rational margin `11/10 · 10⁻⁹`. -/
theorem C4_eta_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 1 = radiiReal 1 →
      (11 / 10000000000 : ℝ) < C4 (pointOf t z) := by
  intro t z ht hz heta
  have hxi := hz 0
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi
  have heta' : z 1 = (1 / 100000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at heta
    exact heta
  have hzero := c4Reduced_eta_zero_abs_lt ht hxi
  have hgrowth := c4Reduced_eta_growth ht hxi
    (eta₁ := 0) (eta₂ := (1 / 100000000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [C4_pointOf_eq_c4Reduced, heta']
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

/-- Derivative of the correlated `F` residual in the brick parameter. -/
private def fReducedDerivT (t xi eta : ℝ) : ℝ :=
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ll := (lamMid : ℝ) + t
  let bb := ll * yy + π / 2 - xx
  let a := (brick.slopes 0 : ℝ)
  let b := (brick.slopes 1 : ℝ)
  (-a) * sin xx * (sin yy - sin xx) +
    cos xx * (b * cos yy - a * cos xx) -
      (a * cos xx * sin yy * bb + sin xx * b * cos yy * bb +
        sin xx * sin yy * (yy + ll * b - a))

/-- Derivative of the correlated `F` residual in `eta`. -/
private def fReducedDerivEta (t xi eta : ℝ) : ℝ :=
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ll := (lamMid : ℝ) + t
  let bb := ll * yy + π / 2 - xx
  cos xx * cos yy - sin xx * cos yy * bb - sin xx * sin yy * ll

private theorem fReduced_hasDerivAt_t (t xi eta : ℝ) :
    HasDerivAt (fun u => fReduced u xi eta) (fReducedDerivT t xi eta) t := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  have hx : HasDerivAt
      (fun u : ℝ => (brick.centers 0 : ℝ) + brick.slopes 0 * u + xi)
      (brick.slopes 0 : ℝ) t := by
    convert ((hasDerivAt_const t (brick.centers 0 : ℝ)).add
      ((hasDerivAt_const t (brick.slopes 0 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t xi) using 1 <;>
      first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * u +
        brick.yXiSlope * xi + eta) (brick.slopes 1 : ℝ) t := by
    convert (((hasDerivAt_const t (brick.centers 1 : ℝ)).add
      ((hasDerivAt_const t (brick.slopes 1 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t ((brick.yXiSlope : ℝ) * xi))).add
          (hasDerivAt_const t eta) using 1 <;>
      first | rfl | ring_nf
  have hl : HasDerivAt (fun u : ℝ => (lamMid : ℝ) + u) 1 t := by
    convert (hasDerivAt_const t (lamMid : ℝ)).add (hasDerivAt_id t) using 1 <;>
      first | rfl | ring_nf
  have hxxs := (Real.hasDerivAt_sin xx).comp t hx
  have hxxc := (Real.hasDerivAt_cos xx).comp t hx
  have hyys := (Real.hasDerivAt_sin yy).comp t hy
  have hb := (((hl.mul hy).add (hasDerivAt_const t (π / 2))).sub hx)
  convert (hxxc.mul (hyys.sub hxxs)).sub ((hxxs.mul hyys).mul hb) using 1 <;> try rfl
  simp [Function.comp_apply, xx, yy, fReducedDerivT]
  ring

private theorem fReduced_hasDerivAt_eta (t xi eta : ℝ) :
    HasDerivAt (fun u => fReduced t xi u) (fReducedDerivEta t xi eta) eta := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  have hy : HasDerivAt
      (fun u : ℝ => (brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi + u) 1 eta := by
    convert (hasDerivAt_const eta
      ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi)).add (hasDerivAt_id eta) using 1 <;>
      first | rfl | ring_nf
  have hyys : HasDerivAt
      (fun u : ℝ => sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
        brick.yXiSlope * xi + u)) (cos yy) eta := by
    convert (Real.hasDerivAt_sin yy).comp eta hy using 1 <;> try rfl
    ring
  have hb := (((hasDerivAt_const eta ((lamMid : ℝ) + t)).mul hy).add
    (hasDerivAt_const eta (π / 2))).sub (hasDerivAt_const eta xx)
  convert ((hasDerivAt_const eta (cos xx)).mul
      (hyys.sub (hasDerivAt_const eta (sin xx)))).sub
        (((hasDerivAt_const eta (sin xx)).mul hyys).mul hb) using 1 <;> try rfl
  simp [fReducedDerivEta, xx, yy]
  ring

/- Exact point certificate at the lower `xi` face, before the small `t` and
`eta` variations are introduced. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem fReduced_low_anchor :
    (97 / 1000000000 : ℝ) < fReduced 0 (-(1 / 10000000)) 0 := by
  let xq : ℚ := brick.centers 0 - 1 / 10000000
  let yq : ℚ := brick.centers 1 - brick.yXiSlope / 10000000
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let b : CertificateExpr :=
    .add (.rational (lamMid * yq - xq)) (.mul (.rational (1 / 2)) p)
  let e : CertificateExpr :=
    .add (.mul cx (.add sy (.neg sx)))
      (.neg (.mul (.mul sx sy) b))
  have he := CertificateExpr.sound e
  have hv : e.value = fReduced 0 (-(1 / 10000000)) 0 := by
    norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.value,
      fReduced, brick, lamMid]
    ring
  rw [hv] at he
  have hlo := he.1
  norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial, brick, lamMid] at hlo
  linarith


/- Exact point certificate at the upper `xi` face. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem fReduced_high_anchor :
    fReduced 0 (1 / 10000000) 0 < -(95 / 1000000000 : ℝ) := by
  let xq : ℚ := brick.centers 0 + 1 / 10000000
  let yq : ℚ := brick.centers 1 + brick.yXiSlope / 10000000
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let b : CertificateExpr :=
    .add (.rational (lamMid * yq - xq)) (.mul (.rational (1 / 2)) p)
  let e : CertificateExpr :=
    .add (.mul cx (.add sy (.neg sx)))
      (.neg (.mul (.mul sx sy) b))
  have he := CertificateExpr.sound e
  have hv : e.value = fReduced 0 (1 / 10000000) 0 := by
    norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.value,
      fReduced, brick, lamMid]
    ring
  rw [hv] at he
  have hhi := he.2
  norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial, brick, lamMid] at hhi
  linarith

/- Correlation-preserving interval bound for the `t` derivative of `F`.
The complete derivative is enclosed as one expression, so its large summands
are never rounded independently before cancellation. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem fReducedDerivT_abs_le {q xi : ℝ}
    (hq : -(1 / 200000 : ℝ) ≤ q ∧ q ≤ 1 / 200000)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000) :
    |fReducedDerivT q xi 0| ≤ (1 / 2000 : ℝ) := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * q + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * q +
    brick.yXiSlope * xi
  let ll := (lamMid : ℝ) + q
  have hxx : (18511 / 100000 : ℝ) ≤ xx ∧ xx ≤ 18514 / 100000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (27048 / 100000 : ℝ) ≤ yy ∧ yy ≤ 27054 / 100000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hll : (51 / 50 : ℝ) ≤ ll ∧ ll ≤ 102001 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hsx := c4_sin_x_range hxx
  have hcx := c4_cos_x_range hxx
  have hsy := c4_sin_y_range hyy
  have hcy := c4_cos_y_range hyy
  let exx : CertificateExpr := .atom xx
    ⟨18511 / 100000, 18514 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let eyy : CertificateExpr := .atom yy
    ⟨27048 / 100000, 27054 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ell : CertificateExpr := .atom ll
    ⟨51 / 50, 102001 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨184054 / 1000000, 184085 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsx)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨982910 / 1000000, 982917 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcx)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨267194 / 1000000, 267252 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsy)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨963626 / 1000000, 963643 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcy)
  let ep : CertificateExpr := .atom π
    ⟨3141592 / 1000000, 3141593 / 1000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d6]
        · norm_num at ⊢
          linarith [Real.pi_lt_d6])
  let ebb : CertificateExpr :=
    .add (.add (.mul ell eyy) (.mul (.rational (1 / 2)) ep)) (.neg exx)
  let ea : CertificateExpr := .rational (brick.slopes 0)
  let eb : CertificateExpr := .rational (brick.slopes 1)
  let e1 : CertificateExpr :=
    .mul (.mul (.neg ea) esx) (.add esy (.neg esx))
  let e2 : CertificateExpr :=
    .mul ecx (.add (.mul eb ecy) (.neg (.mul ea ecx)))
  let e3 : CertificateExpr :=
    .add
      (.add (.mul (.mul (.mul ea ecx) esy) ebb)
        (.mul (.mul (.mul esx eb) ecy) ebb))
      (.mul (.mul esx esy)
        (.add (.add eyy (.mul ell eb)) (.neg ea)))
  let ed : CertificateExpr := .add (.add e1 e2) (.neg e3)
  have he := CertificateExpr.sound ed
  have hv : ed.value = fReducedDerivT q xi 0 := by
    simp [ed, e1, e2, e3, ea, eb, ebb, ep, exx, eyy, ell, esx, ecx,
      esy, ecy, CertificateExpr.value, fReducedDerivT, xx, yy, ll]
    ring
  rw [hv] at he
  rw [abs_le]
  norm_num [ed, e1, e2, e3, ea, eb, ebb, ep, exx, eyy, ell, esx, ecx,
    esy, ecy, CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, brick] at he ⊢
  constructor <;> linarith [he.1, he.2]

/- Uniform derivative bound in the thin `eta` direction. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem fReducedDerivEta_abs_le {t xi eta : ℝ}
    (ht : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta : -(1 / 100000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 100000000) :
    |fReducedDerivEta t xi eta| ≤ (61 / 100 : ℝ) := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ll := (lamMid : ℝ) + t
  have hxx : (18511 / 100000 : ℝ) ≤ xx ∧ xx ≤ 18514 / 100000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (27048 / 100000 : ℝ) ≤ yy ∧ yy ≤ 27054 / 100000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hll : (51 / 50 : ℝ) ≤ ll ∧ ll ≤ 102001 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hsx := c4_sin_x_range hxx
  have hcx := c4_cos_x_range hxx
  have hsy := c4_sin_y_range hyy
  have hcy := c4_cos_y_range hyy
  let exx : CertificateExpr := .atom xx
    ⟨18511 / 100000, 18514 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let eyy : CertificateExpr := .atom yy
    ⟨27048 / 100000, 27054 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ell : CertificateExpr := .atom ll
    ⟨51 / 50, 102001 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨184054 / 1000000, 184085 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsx)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨982910 / 1000000, 982917 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcx)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨267194 / 1000000, 267252 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsy)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨963626 / 1000000, 963643 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcy)
  let ep : CertificateExpr := .atom π
    ⟨3141592 / 1000000, 3141593 / 1000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d6]
        · norm_num at ⊢
          linarith [Real.pi_lt_d6])
  let ebb : CertificateExpr :=
    .add (.add (.mul ell eyy) (.mul (.rational (1 / 2)) ep)) (.neg exx)
  let ed : CertificateExpr :=
    .add
      (.add (.mul ecx ecy) (.neg (.mul (.mul esx ecy) ebb)))
      (.neg (.mul (.mul esx esy) ell))
  have he := CertificateExpr.sound ed
  have hv : ed.value = fReducedDerivEta t xi eta := by
    simp [ed, ebb, ep, exx, eyy, ell, esx, ecx, esy, ecy,
      CertificateExpr.value, fReducedDerivEta, xx, yy, ll]
    ring
  rw [hv] at he
  rw [abs_le]
  norm_num [ed, ebb, ep, exx, eyy, ell, esx, ecx, esy, ecy,
    CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point] at he ⊢
  constructor <;> linarith [he.1, he.2]

/-- The two thin directions move `F` by at most the exact rational
`43/5 · 10⁻⁹`, uniformly at either `xi` face. -/
private theorem fReduced_face_deviation {t xi eta : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta : -(1 / 100000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 100000000) :
    |fReduced t xi eta - fReduced 0 xi 0| ≤
      (43 / 5000000000 : ℝ) := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have htChange :
      |fReduced t xi 0 - fReduced 0 xi 0| ≤
        (1 / 2000 : ℝ) * |t| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => fReduced u xi 0)
      (f' := fun q => fReducedDerivT q xi 0)
      (R := (1 / 200000 : ℝ)) (M := (1 / 2000 : ℝ))
      (u := t) (by norm_num) ht'
    · intro q hq
      exact fReduced_hasDerivAt_t q xi 0
    · intro q hq
      exact fReducedDerivT_abs_le hq hxi
  have hetaChange :
      |fReduced t xi eta - fReduced t xi 0| ≤
        (61 / 100 : ℝ) * |eta| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => fReduced t xi u)
      (f' := fun q => fReducedDerivEta t xi q)
      (R := (1 / 100000000 : ℝ)) (M := (61 / 100 : ℝ))
      (u := eta) (by norm_num) heta
    · intro q hq
      exact fReduced_hasDerivAt_eta t xi q
    · intro q hq
      exact fReducedDerivEta_abs_le ht' hxi hq
  have htAbs : |t| ≤ (1 / 200000 : ℝ) := (abs_le).2 ht'
  have hetaAbs : |eta| ≤ (1 / 100000000 : ℝ) := (abs_le).2 heta
  have htriangle :
      |fReduced t xi eta - fReduced 0 xi 0| ≤
        |fReduced t xi eta - fReduced t xi 0| +
          |fReduced t xi 0 - fReduced 0 xi 0| := by
    calc
      |fReduced t xi eta - fReduced 0 xi 0| =
          |(fReduced t xi eta - fReduced t xi 0) +
            (fReduced t xi 0 - fReduced 0 xi 0)| := by ring
      _ ≤ |fReduced t xi eta - fReduced t xi 0| +
          |fReduced t xi 0 - fReduced 0 xi 0| := abs_add_le _ _
  norm_num at htChange hetaChange htAbs hetaAbs htriangle ⊢
  nlinarith

/-- On the lower `xi` face, `F` is uniformly positive with exact strict
margin `88 · 10⁻⁹` over the complete first brick. -/
theorem F_xi_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 0 = -radiiReal 0 →
      (88 / 1000000000 : ℝ) < F (pointOf t z) := by
  intro t z ht hz hxiFace
  have heta := hz 1
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at heta
  have hxi : z 0 = -(1 / 10000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hxiFace
    exact hxiFace
  have hdev := fReduced_face_deviation ht
    (xi := -(1 / 10000000 : ℝ)) (eta := z 1)
    (by constructor <;> norm_num) heta
  have hdevLo := (abs_le.mp hdev).1
  rw [F_pointOf_eq_fReduced, hxi]
  have hanchor := fReduced_low_anchor
  norm_num at hdevLo hanchor ⊢
  linarith

/-- On the upper `xi` face, `F` is uniformly negative with exact strict
margin `86 · 10⁻⁹` over the complete first brick. -/
theorem F_xi_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 0 = radiiReal 0 →
      F (pointOf t z) < -(86 / 1000000000 : ℝ) := by
  intro t z ht hz hxiFace
  have heta := hz 1
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at heta
  have hxi : z 0 = (1 / 10000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hxiFace
    exact hxiFace
  have hdev := fReduced_face_deviation ht
    (xi := (1 / 10000000 : ℝ)) (eta := z 1)
    (by constructor <;> norm_num) heta
  have hdevHi := (abs_le.mp hdev).2
  rw [F_pointOf_eq_fReduced, hxi]
  have hanchor := fReduced_high_anchor
  norm_num at hdevHi hanchor ⊢
  linarith


/-- At `sigma = 0`, the correlated `C3` residual stays within
`17/5 · 10⁻⁹`.  The shared `t` and `rho` dependence of both cosine arguments
is retained through one-dimensional mean-value estimates. -/
private theorem c3Reduced_sigma_zero_abs_lt {t rho : ℝ}
    (ht : tInterval.RealContains t)
    (hrho : -(1 / 10000000 : ℝ) ≤ rho ∧ rho ≤ 1 / 10000000) :
    |c3Reduced t rho 0| < (17 / 5000000000 : ℝ) := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hanchor :
      |c3Reduced 0 0 0| < (3 / 10000000000 : ℝ) := by
    have hwlo := (cosTaylor26Interval_sound (brick.centers 2)).1
    have hwhi := (cosTaylor26Interval_sound (brick.centers 2)).2
    have hvlo := (cosTaylor26Interval_sound (brick.centers 3)).1
    have hvhi := (cosTaylor26Interval_sound (brick.centers 3)).2
    norm_num [c3Reduced, brick, lamMid, Matrix.cons_val_two,
      Matrix.cons_val_three, cosTaylor26Interval, cosTaylor26,
      Finset.sum_range_succ, Nat.factorial] at hwlo hwhi hvlo hvhi ⊢
    rw [abs_lt]
    constructor <;> nlinarith
  have htChange :
      |c3Reduced t 0 0 - c3Reduced 0 0 0| ≤
        (3 / 5000 : ℝ) * |t| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => c3Reduced u 0 0)
      (f' := fun q =>
        -(brick.slopes 2 : ℝ) *
            sin ((brick.centers 2 : ℝ) + brick.slopes 2 * q) -
          cos ((brick.centers 3 : ℝ) + brick.slopes 3 * q) +
          (brick.slopes 3 : ℝ) * (((lamMid : ℝ) + q) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * q)))
      (R := (1 / 200000 : ℝ)) (M := (3 / 5000 : ℝ))
      (u := t) (by norm_num) ht'
    · intro q hq
      have hw : HasDerivAt
          (fun u : ℝ => (brick.centers 2 : ℝ) + brick.slopes 2 * u)
          (brick.slopes 2 : ℝ) q := by
        convert (hasDerivAt_const q (brick.centers 2 : ℝ)).add
            ((hasDerivAt_const q (brick.slopes 2 : ℝ)).mul
              (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      have hv : HasDerivAt
          (fun u : ℝ => (brick.centers 3 : ℝ) + brick.slopes 3 * u)
          (brick.slopes 3 : ℝ) q := by
        convert (hasDerivAt_const q (brick.centers 3 : ℝ)).add
            ((hasDerivAt_const q (brick.slopes 3 : ℝ)).mul
              (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      have hlam : HasDerivAt (fun u : ℝ => (lamMid : ℝ) + u) 1 q := by
        convert (hasDerivAt_const q (lamMid : ℝ)).add (hasDerivAt_id q) using 1 <;>
          first | rfl | ring_nf
      convert ((Real.hasDerivAt_cos _).comp q hw).sub
          (hlam.mul ((Real.hasDerivAt_cos _).comp q hv)) using 1 <;> try rfl
      · funext u
        simp [c3Reduced, Function.comp_apply]
      · simp only [Function.comp_apply]
        ring
    · intro q hq
      have hq' : -(1 / 200000 : ℝ) ≤ q ∧ q ≤ 1 / 200000 := hq
      have hwArg :
          (41869 / 100000 : ℝ) ≤
              (brick.centers 2 : ℝ) + brick.slopes 2 * q ∧
            (brick.centers 2 : ℝ) + brick.slopes 2 * q ≤
              41877 / 100000 := by
        norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
        constructor <;> linarith
      have hvArg :
          (46078 / 100000 : ℝ) ≤
              (brick.centers 3 : ℝ) + brick.slopes 3 * q ∧
            (brick.centers 3 : ℝ) + brick.slopes 3 * q ≤
              46086 / 100000 := by
        norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
        constructor <;> linarith
      have hsw := c3_sin_w_range hwArg
      have hsv := c3_sin_v_range hvArg
      have hcv := c3_cos_v_range hvArg
      have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + q := by
        norm_num [lamMid, brick]
        linarith
      have hlamHi : (lamMid : ℝ) + q ≤ (102001 / 100000 : ℝ) := by
        norm_num [lamMid, brick]
        linarith
      have hprodLo :
          (51 / 50 : ℝ) * (444646 / 1000000 : ℝ) ≤
            ((lamMid : ℝ) + q) *
              sin ((brick.centers 3 : ℝ) + brick.slopes 3 * q) :=
        mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
      have hprodHi :
          ((lamMid : ℝ) + q) *
              sin ((brick.centers 3 : ℝ) + brick.slopes 3 * q) ≤
            (102001 / 100000 : ℝ) * (444719 / 1000000 : ℝ) :=
        mul_le_mul hlamHi hsv.2 (by linarith) (by norm_num)
      rw [abs_le]
      norm_num [brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
        at hsw hsv hcv hprodLo hprodHi ⊢
      constructor <;> linarith
  have hrhoChange :
      |c3Reduced t rho 0 - c3Reduced t 0 0| ≤
        (3 / 10000 : ℝ) * |rho| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => c3Reduced t u 0)
      (f' := fun q =>
        -sin ((brick.centers 2 : ℝ) + brick.slopes 2 * t + q) +
          (brick.vRhoSlope : ℝ) * (((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * q)))
      (R := (1 / 10000000 : ℝ)) (M := (3 / 10000 : ℝ))
      (u := rho) (by norm_num) hrho
    · intro q hq
      have hw : HasDerivAt
          (fun u : ℝ =>
            (brick.centers 2 : ℝ) + brick.slopes 2 * t + u) 1 q := by
        convert (hasDerivAt_const q
            ((brick.centers 2 : ℝ) + brick.slopes 2 * t)).add
              (hasDerivAt_id q) using 1 <;>
          first | rfl | ring_nf
      have hv : HasDerivAt
          (fun u : ℝ =>
            (brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * u) (brick.vRhoSlope : ℝ) q := by
        convert (hasDerivAt_const q
            ((brick.centers 3 : ℝ) + brick.slopes 3 * t)).add
              ((hasDerivAt_const q (brick.vRhoSlope : ℝ)).mul
                (hasDerivAt_id q)) using 1 <;>
          first | rfl | ring_nf
      convert ((Real.hasDerivAt_cos _).comp q hw).sub
          ((hasDerivAt_const q ((lamMid : ℝ) + t)).mul
            ((Real.hasDerivAt_cos _).comp q hv)) using 1 <;> try rfl
      · funext u
        simp [c3Reduced, Function.comp_apply]
      · simp only [Function.comp_apply]
        ring
    · intro q hq
      have hq' : -(1 / 10000000 : ℝ) ≤ q ∧
          q ≤ 1 / 10000000 := hq
      have hwArg :
          (41869 / 100000 : ℝ) ≤
              (brick.centers 2 : ℝ) + brick.slopes 2 * t + q ∧
            (brick.centers 2 : ℝ) + brick.slopes 2 * t + q ≤
              41877 / 100000 := by
        norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
        constructor <;> linarith
      have hvArg :
          (46078 / 100000 : ℝ) ≤
              (brick.centers 3 : ℝ) + brick.slopes 3 * t +
                brick.vRhoSlope * q ∧
            (brick.centers 3 : ℝ) + brick.slopes 3 * t +
                brick.vRhoSlope * q ≤ 46086 / 100000 := by
        norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
        constructor <;> linarith
      have hsw := c3_sin_w_range hwArg
      have hsv := c3_sin_v_range hvArg
      have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
        norm_num [lamMid, brick]
        linarith
      have hlamHi : (lamMid : ℝ) + t ≤ (102001 / 100000 : ℝ) := by
        norm_num [lamMid, brick]
        linarith
      have hprodLo :
          (51 / 50 : ℝ) * (444646 / 1000000 : ℝ) ≤
            ((lamMid : ℝ) + t) *
              sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
                brick.vRhoSlope * q) :=
        mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
      have hprodHi :
          ((lamMid : ℝ) + t) *
              sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
                brick.vRhoSlope * q) ≤
            (102001 / 100000 : ℝ) * (444719 / 1000000 : ℝ) :=
        mul_le_mul hlamHi hsv.2 (by linarith) (by norm_num)
      rw [abs_le]
      norm_num [brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
        at hsw hsv hprodLo hprodHi ⊢
      constructor <;> linarith
  have htAbs : |t| ≤ (1 / 200000 : ℝ) := (abs_le).2 ht'
  have hrhoAbs : |rho| ≤ (1 / 10000000 : ℝ) := (abs_le).2 hrho
  have hsum :
      |c3Reduced t rho 0| ≤
        |c3Reduced t rho 0 - c3Reduced t 0 0| +
          |c3Reduced t 0 0 - c3Reduced 0 0 0| +
            |c3Reduced 0 0 0| := by
    calc
      |c3Reduced t rho 0| =
          |(c3Reduced t rho 0 - c3Reduced t 0 0) +
            (c3Reduced t 0 0 - c3Reduced 0 0 0) +
              c3Reduced 0 0 0| := by ring
      _ ≤ |(c3Reduced t rho 0 - c3Reduced t 0 0) +
              (c3Reduced t 0 0 - c3Reduced 0 0 0)| +
            |c3Reduced 0 0 0| := abs_add_le _ _
      _ ≤ |c3Reduced t rho 0 - c3Reduced t 0 0| +
              |c3Reduced t 0 0 - c3Reduced 0 0 0| +
            |c3Reduced 0 0 0| := by
        have hab := abs_add_le
          (c3Reduced t rho 0 - c3Reduced t 0 0)
          (c3Reduced t 0 0 - c3Reduced 0 0 0)
        linarith
  norm_num at htChange hrhoChange htAbs hrhoAbs hanchor hsum ⊢
  nlinarith

/-- Quantitative monotonicity in `sigma`: on the complete first brick the
`sigma` derivative of `C3` is at least the exact rational `9/20`. -/
private theorem c3Reduced_sigma_growth {t rho sigma₁ sigma₂ : ℝ}
    (ht : tInterval.RealContains t)
    (hrho : -(1 / 10000000 : ℝ) ≤ rho ∧ rho ≤ 1 / 10000000)
    (hsigma₁ : sigma₁ ∈ Icc (-(1 / 100000000 : ℝ)) (1 / 100000000))
    (hsigma₂ : sigma₂ ∈ Icc (-(1 / 100000000 : ℝ)) (1 / 100000000))
    (hsigma : sigma₁ ≤ sigma₂) :
    (9 / 20 : ℝ) * (sigma₂ - sigma₁) ≤
      c3Reduced t rho sigma₂ - c3Reduced t rho sigma₁ := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  apply (convex_Icc (-(1 / 100000000 : ℝ))
    (1 / 100000000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold c3Reduced; fun_prop) (by unfold c3Reduced; fun_prop) ?_
        sigma₁ hsigma₁ sigma₂ hsigma₂ hsigma
  intro q hq
  have hq' : -(1 / 100000000 : ℝ) < q ∧
      q < 1 / 100000000 := by
    simpa only [interior_Icc, mem_Ioo] using hq
  have hvArg :
      (46078 / 100000 : ℝ) ≤
          (brick.centers 3 : ℝ) + brick.slopes 3 * t +
            brick.vRhoSlope * rho + q ∧
        (brick.centers 3 : ℝ) + brick.slopes 3 * t +
            brick.vRhoSlope * rho + q ≤ 46086 / 100000 := by
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    constructor <;> linarith
  have hsv := c3_sin_v_range hvArg
  have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
    norm_num [lamMid, brick]
    linarith
  have hprodLo :
      (51 / 50 : ℝ) * (444646 / 1000000 : ℝ) ≤
        ((lamMid : ℝ) + t) *
          sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
            brick.vRhoSlope * rho + q) :=
    mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
  have hv : HasDerivAt
      (fun u : ℝ =>
        (brick.centers 3 : ℝ) + brick.slopes 3 * t +
          brick.vRhoSlope * rho + u) 1 q := by
    convert (hasDerivAt_const q
      ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
        brick.vRhoSlope * rho)).add (hasDerivAt_id q) using 1 <;>
      first | rfl | ring_nf
  have hC3 : HasDerivAt (fun u => c3Reduced t rho u)
      (((lamMid : ℝ) + t) *
        sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
          brick.vRhoSlope * rho + q)) q := by
    convert (hasDerivAt_const q
        (cos ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho))).sub
      ((hasDerivAt_const q ((lamMid : ℝ) + t)).mul
        ((Real.hasDerivAt_cos _).comp q hv)) using 1 <;> try rfl
    simp only [Function.comp_apply]
    ring
  rw [hC3.deriv]
  norm_num [brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
    at hprodLo ⊢
  linarith

/-- The lower `sigma` face has the required `C3` sign with the strict exact
rational margin `10⁻⁹`. -/
theorem C3_sigma_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 3 = -radiiReal 3 →
      C3 (pointOf t z) < -(1 / 1000000000 : ℝ) := by
  intro t z ht hz hsigma
  have hrho := hz 2
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hrho
  have hsigma' : z 3 = -(1 / 100000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at hsigma
    exact hsigma
  have hzero := c3Reduced_sigma_zero_abs_lt ht hrho
  have hgrowth := c3Reduced_sigma_growth ht hrho
    (sigma₁ := -(1 / 100000000 : ℝ)) (sigma₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [C3_pointOf_eq_c3Reduced, hsigma']
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

/-- The upper `sigma` face has the required `C3` sign with the strict exact
rational margin `10⁻⁹`. -/
theorem C3_sigma_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 3 = radiiReal 3 →
      (1 / 1000000000 : ℝ) < C3 (pointOf t z) := by
  intro t z ht hz hsigma
  have hrho := hz 2
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hrho
  have hsigma' : z 3 = (1 / 100000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at hsigma
    exact hsigma
  have hzero := c3Reduced_sigma_zero_abs_lt ht hrho
  have hgrowth := c3Reduced_sigma_growth ht hrho
    (sigma₁ := 0) (sigma₂ := (1 / 100000000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [C3_pointOf_eq_c3Reduced, hsigma']
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

set_option maxHeartbeats 1000000 in
-- Six exact degree-27/26 point enclosures require extra normalization time.
private theorem eReduced_origin_abs_lt :
    |eReduced 0 0 0 0 0| < (3 / 1000000000 : ℝ) := by
  let xq : ℚ := brick.centers 0
  let yq : ℚ := brick.centers 1
  let wq : ℚ := brick.centers 2
  let vq : ℚ := brick.centers 3
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let sw : CertificateExpr :=
    .atom (sin (wq : ℝ)) (sinTaylor27Interval wq)
      (sinTaylor27Interval_sound wq)
  let cw : CertificateExpr :=
    .atom (cos (wq : ℝ)) (cosTaylor26Interval wq)
      (cosTaylor26Interval_sound wq)
  let sv : CertificateExpr :=
    .atom (sin (vq : ℝ)) (sinTaylor27Interval vq)
      (sinTaylor27Interval_sound vq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let n4 : CertificateExpr :=
    .add
      (.add
        (.add (.rational (lamMid * yq))
          (.mul (.rational (1 / 2)) p))
        (.neg (.rational xq)))
      (.mul cx (.add sy (.neg sx)))
  let n3 : CertificateExpr :=
    .add
      (.add
        (.add (.rational (lamMid * vq)) p)
        (.neg (.rational wq)))
      (.mul (.add cw (.rational 2)) (.add sv (.neg sw)))
  let e : CertificateExpr :=
    .add
      (.mul (.mul (.rational 2) (.mul cx cx)) n3)
      (.neg
        (.mul
          (.mul (.add (.rational 1) cw) (.add (.rational 1) cw))
          n4))
  have he := CertificateExpr.sound e
  have hv : e.value = eReduced 0 0 0 0 0 := by
    norm_num [e, n3, n4, p, sx, cx, sy, sw, cw, sv, xq, yq, wq, vq,
      CertificateExpr.value, eReduced, brick, lamMid, Matrix.cons_val_two,
      Matrix.cons_val_three]
    ring
  rw [hv] at he
  rw [abs_lt]
  norm_num [e, n3, n4, p, sx, cx, sy, sw, cw, sv, xq, yq, wq, vq,
    CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, sinTaylor27Interval, sinTaylor27,
    cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ, Nat.factorial,
    brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three] at he ⊢
  constructor <;> linarith [he.1, he.2]

private theorem eReduced_rho_zero_abs_lt {t xi eta sigma : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta : -(1 / 100000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 100000000)
    (hsigma : -(1 / 100000000 : ℝ) ≤ sigma ∧
      sigma ≤ 1 / 100000000) :
    |eReduced t xi eta 0 sigma| < (175 / 1000000000 : ℝ) := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hzeroT : (0 : ℝ) ∈ Icc (-(1 / 200000)) (1 / 200000) := by
    constructor <;> norm_num
  have hzeroXi : (0 : ℝ) ∈ Icc (-(1 / 10000000)) (1 / 10000000) := by
    constructor <;> norm_num
  have hzeroEta : (0 : ℝ) ∈ Icc (-(1 / 100000000)) (1 / 100000000) := by
    constructor <;> norm_num
  have hzeroRho : (0 : ℝ) ∈ Icc (-(1 / 10000000)) (1 / 10000000) := by
    constructor <;> norm_num
  have hzeroSigma : (0 : ℝ) ∈ Icc (-(1 / 100000000)) (1 / 100000000) := by
    constructor <;> norm_num
  have htChange :
      |eReduced t 0 0 0 0 - eReduced 0 0 0 0 0| ≤
        (51 / 10000 : ℝ) * |t| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => eReduced u 0 0 0 0)
      (f' := fun q => eReducedDerivT q 0 0 0 0)
      (R := (1 / 200000 : ℝ)) (M := (51 / 10000 : ℝ))
      (u := t) (by norm_num) ht'
    · intro q hq
      exact eReduced_hasDerivAt_t q 0 0 0 0
    · intro q hq
      exact (eReduced_deriv_bounds hq hzeroXi hzeroEta hzeroRho
        hzeroSigma).1
  have hxiChange :
      |eReduced t xi 0 0 0 - eReduced t 0 0 0 0| ≤
        (39 / 1000 : ℝ) * |xi| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => eReduced t u 0 0 0)
      (f' := fun q => eReducedDerivXi t q 0 0 0)
      (R := (1 / 10000000 : ℝ)) (M := (39 / 1000 : ℝ))
      (u := xi) (by norm_num) hxi
    · intro q hq
      exact eReduced_hasDerivAt_xi t q 0 0 0
    · intro q hq
      exact (eReduced_deriv_bounds ht' hq hzeroEta hzeroRho hzeroSigma).2.1
  have hetaChange :
      |eReduced t xi eta 0 0 - eReduced t xi 0 0 0| ≤
        (721 / 100 : ℝ) * |eta| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => eReduced t xi u 0 0)
      (f' := fun q => eReducedDerivEta t xi q 0 0)
      (R := (1 / 100000000 : ℝ)) (M := (721 / 100 : ℝ))
      (u := eta) (by norm_num) heta
    · intro q hq
      exact eReduced_hasDerivAt_eta t xi q 0 0
    · intro q hq
      exact (eReduced_deriv_bounds ht' hxi hq hzeroRho hzeroSigma).2.2.1
  have hsigmaChange :
      |eReduced t xi eta 0 sigma - eReduced t xi eta 0 0| ≤
        (351 / 50 : ℝ) * |sigma| := by
    apply abs_image_sub_le_of_hasDerivAt
      (f := fun u => eReduced t xi eta 0 u)
      (f' := fun q => eReducedDerivSigma t xi eta 0 q)
      (R := (1 / 100000000 : ℝ)) (M := (351 / 50 : ℝ))
      (u := sigma) (by norm_num) hsigma
    · intro q hq
      exact eReduced_hasDerivAt_sigma t xi eta 0 q
    · intro q hq
      exact (eReduced_deriv_bounds ht' hxi heta hzeroRho hq).2.2.2.2
  have htAbs : |t| ≤ (1 / 200000 : ℝ) := (abs_le).2 ht'
  have hxiAbs : |xi| ≤ (1 / 10000000 : ℝ) := (abs_le).2 hxi
  have hetaAbs : |eta| ≤ (1 / 100000000 : ℝ) := (abs_le).2 heta
  have hsigmaAbs : |sigma| ≤ (1 / 100000000 : ℝ) := (abs_le).2 hsigma
  have htriangle :
      |eReduced t xi eta 0 sigma| ≤
        |eReduced t xi eta 0 sigma - eReduced t xi eta 0 0| +
        |eReduced t xi eta 0 0 - eReduced t xi 0 0 0| +
        |eReduced t xi 0 0 0 - eReduced t 0 0 0 0| +
        |eReduced t 0 0 0 0 - eReduced 0 0 0 0 0| +
        |eReduced 0 0 0 0 0| := by
    calc
      |eReduced t xi eta 0 sigma| =
          |(eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
           (eReduced t xi eta 0 0 - eReduced t xi 0 0 0) +
           (eReduced t xi 0 0 0 - eReduced t 0 0 0 0) +
           (eReduced t 0 0 0 0 - eReduced 0 0 0 0 0) +
           eReduced 0 0 0 0 0| := by ring
      _ ≤
          |(eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
            (eReduced t xi eta 0 0 - eReduced t xi 0 0 0) +
            (eReduced t xi 0 0 0 - eReduced t 0 0 0 0) +
            (eReduced t 0 0 0 0 - eReduced 0 0 0 0 0)| +
          |eReduced 0 0 0 0 0| := abs_add_le _ _
      _ ≤
          (|(eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
            (eReduced t xi eta 0 0 - eReduced t xi 0 0 0) +
            (eReduced t xi 0 0 0 - eReduced t 0 0 0 0)| +
          |eReduced t 0 0 0 0 - eReduced 0 0 0 0 0|) +
          |eReduced 0 0 0 0 0| := by
        linarith [abs_add_le
          ((eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
           (eReduced t xi eta 0 0 - eReduced t xi 0 0 0) +
           (eReduced t xi 0 0 0 - eReduced t 0 0 0 0))
          (eReduced t 0 0 0 0 - eReduced 0 0 0 0 0)]
      _ ≤
          ((|(eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
            (eReduced t xi eta 0 0 - eReduced t xi 0 0 0)| +
          |eReduced t xi 0 0 0 - eReduced t 0 0 0 0|) +
          |eReduced t 0 0 0 0 - eReduced 0 0 0 0 0|) +
          |eReduced 0 0 0 0 0| := by
        linarith [abs_add_le
          ((eReduced t xi eta 0 sigma - eReduced t xi eta 0 0) +
           (eReduced t xi eta 0 0 - eReduced t xi 0 0 0))
          (eReduced t xi 0 0 0 - eReduced t 0 0 0 0)]
      _ ≤
          ((|eReduced t xi eta 0 sigma - eReduced t xi eta 0 0| +
            |eReduced t xi eta 0 0 - eReduced t xi 0 0 0|) +
          |eReduced t xi 0 0 0 - eReduced t 0 0 0 0|) +
          |eReduced t 0 0 0 0 - eReduced 0 0 0 0 0| +
          |eReduced 0 0 0 0 0| := by
        linarith [abs_add_le
          (eReduced t xi eta 0 sigma - eReduced t xi eta 0 0)
          (eReduced t xi eta 0 0 - eReduced t xi 0 0 0)]
  have hanchor := eReduced_origin_abs_lt
  norm_num at htChange hxiChange hetaChange hsigmaChange htAbs hxiAbs hetaAbs
  norm_num at hsigmaAbs htriangle hanchor ⊢
  nlinarith

private theorem eReduced_rho_growth {t xi eta sigma rho₁ rho₂ : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : -(1 / 10000000 : ℝ) ≤ xi ∧ xi ≤ 1 / 10000000)
    (heta : -(1 / 100000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 100000000)
    (hsigma : -(1 / 100000000 : ℝ) ≤ sigma ∧
      sigma ≤ 1 / 100000000)
    (hrho₁ : rho₁ ∈ Icc (-(1 / 10000000 : ℝ)) (1 / 10000000))
    (hrho₂ : rho₂ ∈ Icc (-(1 / 10000000 : ℝ)) (1 / 10000000))
    (hrho : rho₁ ≤ rho₂) :
    (189 / 100 : ℝ) * (rho₂ - rho₁) ≤
      eReduced t xi eta rho₂ sigma - eReduced t xi eta rho₁ sigma := by
  have ht' : -(1 / 200000 : ℝ) ≤ t ∧ t ≤ 1 / 200000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  apply (convex_Icc (-(1 / 10000000 : ℝ))
    (1 / 10000000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold eReduced; fun_prop) (by unfold eReduced; fun_prop) ?_
        rho₁ hrho₁ rho₂ hrho₂ hrho
  intro q hq
  have hq' : -(1 / 10000000 : ℝ) ≤ q ∧ q ≤ 1 / 10000000 := by
    have hqi : q ∈ Ioo (-(1 / 10000000 : ℝ)) (1 / 10000000) := by
      simpa only [interior_Icc] using hq
    exact ⟨hqi.1.le, hqi.2.le⟩
  rw [(eReduced_hasDerivAt_rho t xi eta q sigma).deriv]
  exact (eReduced_deriv_bounds ht' hxi heta hq' hsigma).2.2.2.1

theorem E_rho_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 2 = -radiiReal 2 →
      E (pointOf t z) < -(14 / 1000000000 : ℝ) := by
  intro t z ht hz hrhoFace
  have hxi := hz 0
  have heta := hz 1
  have hsigma := hz 3
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi heta hsigma
  have hrho : z 2 = -(1 / 10000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hrhoFace
    exact hrhoFace
  have hzero := eReduced_rho_zero_abs_lt ht hxi heta hsigma
  have hgrowth := eReduced_rho_growth ht hxi heta hsigma
    (rho₁ := -(1 / 10000000 : ℝ)) (rho₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [E_pointOf_eq_eReduced, hrho]
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

theorem E_rho_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 2 = radiiReal 2 →
      (14 / 1000000000 : ℝ) < E (pointOf t z) := by
  intro t z ht hz hrhoFace
  have hxi := hz 0
  have heta := hz 1
  have hsigma := hz 3
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi heta hsigma
  have hrho : z 2 = (1 / 10000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hrhoFace
    exact hrhoFace
  have hzero := eReduced_rho_zero_abs_lt ht hxi heta hsigma
  have hgrowth := eReduced_rho_growth ht hxi heta hsigma
    (rho₁ := 0) (rho₂ := (1 / 10000000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [E_pointOf_eq_eReduced, hrho]
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

/-- Kernel-checked bundle of all eight opposite-face signs used by the
root-existence argument. -/
structure AnalyticFaceBounds : Prop where
  lowFaces : ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
    ∀ j, z j = -radiiReal j → rootMap t z j ≤ 0
  highFaces : ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
    ∀ j, z j = radiiReal j → 0 ≤ rootMap t z j

theorem analyticFaceBounds : AnalyticFaceBounds := by
  constructor
  · intro t z ht hz j hj
    fin_cases j
    · have h := F_xi_low_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := C4_eta_low_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := E_rho_low_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := C3_sigma_low_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
  · intro t z ht hz j hj
    fin_cases j
    · have h := F_xi_high_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := C4_eta_high_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := E_rho_high_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith
    · have h := C3_sigma_high_face_margin t z ht hz hj
      norm_num [rootMap] at ⊢
      linarith

private theorem radiiReal_pos (j : Fin 4) : 0 < radiiReal j := by
  change 0 < (brick.radii j : ℝ)
  exact_mod_cast brick.radiiPos j

private theorem zero_mem_coordinate (j : Fin 4) :
    (0 : ℝ) ∈ Icc (-radiiReal j) (radiiReal j) := by
  exact ⟨(neg_lt_zero.mpr (radiiReal_pos j)).le, (radiiReal_pos j).le⟩

private theorem vector_mem_box {xi eta rho sigma : ℝ}
    (hxi : xi ∈ Icc (-radiiReal 0) (radiiReal 0))
    (heta : eta ∈ Icc (-radiiReal 1) (radiiReal 1))
    (hrho : rho ∈ Icc (-radiiReal 2) (radiiReal 2))
    (hsigma : sigma ∈ Icc (-radiiReal 3) (radiiReal 3)) :
    InSymmetricBox radiiReal ![xi, eta, rho, sigma] := by
  intro j
  fin_cases j
  · simpa using hxi
  · simpa using heta
  · simpa [Matrix.cons_val_two] using hrho
  · simpa [Matrix.cons_val_three] using hsigma

/-- The explicit `C4 = 0` graph over the `xi` coordinate; continuity is
inherited from `arccos`. -/
private def etaRoot (t xi : ℝ) : ℝ :=
  arccos
      (cos ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi) /
        ((lamMid : ℝ) + t)) -
    ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
      brick.yXiSlope * xi)

private theorem etaRoot_continuous (t : ℝ) : Continuous (etaRoot t) := by
  unfold etaRoot
  fun_prop

/-- The explicit `C4` root stays inside the certified `eta` interval. -/
private theorem etaRoot_spec {t xi : ℝ}
    (ht : tInterval.RealContains t)
    (hxi : xi ∈ Icc (-radiiReal 0) (radiiReal 0)) :
    etaRoot t xi ∈ Icc (-radiiReal 1) (radiiReal 1) ∧
      C4 (pointOf t ![xi, etaRoot t xi, 0, 0]) = 0 := by
  let zAt : ℝ → Vec4 := fun eta => ![xi, eta, 0, 0]
  have hzAt : Continuous zAt := by
    apply continuous_pi
    intro j
    fin_cases j <;> simp [zAt] <;> fun_prop
  have hz (eta : ℝ) (heta : eta ∈ Icc (-radiiReal 1) (radiiReal 1)) :
      InSymmetricBox radiiReal (zAt eta) := by
    exact vector_mem_box hxi heta (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hlo : C4 (pointOf t (zAt (-radiiReal 1))) ≤ 0 := by
    have h := analyticFaceBounds.lowFaces t (zAt (-radiiReal 1)) ht
      (hz _ ⟨le_rfl, (neg_le_self (radiiReal_pos 1).le)⟩) 1 (by simp [zAt])
    simpa [rootMap] using h
  have hhi : 0 ≤ C4 (pointOf t (zAt (radiiReal 1))) := by
    have h := analyticFaceBounds.highFaces t (zAt (radiiReal 1)) ht
      (hz _ ⟨(neg_le_self (radiiReal_pos 1).le), le_rfl⟩) 1 (by simp [zAt])
    simpa [rootMap] using h
  have hcont : Continuous (fun eta => C4 (pointOf t (zAt eta))) := by
    unfold C4 pointOf x y lam
    fun_prop
  rcases oppositeFace_zero
      (show -radiiReal 1 ≤ radiiReal 1 from neg_le_self (radiiReal_pos 1).le)
      hcont.continuousOn hlo hhi with ⟨eta, heta, hzero⟩
  let p := pointOf t (zAt eta)
  have hzeta : InSymmetricBox radiiReal (zAt eta) := hz eta heta
  have hbranches := affine_branches t (zAt eta) ht hzeta
  rcases hbranches with ⟨_, _, hy0, hyq, _, _, _, _⟩
  have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
    have ht' := ht
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht'
    norm_num [lamMid, brick]
    linarith
  have hlamPos : 0 < lam p := by
    change 0 < (lamMid : ℝ) + t
    linarith
  have hC4 : C4 p = 0 := by simpa [p] using hzero
  have hratio : cos (x p) / lam p = cos (y p) := by
    apply (div_eq_iff (ne_of_gt hlamPos)).2
    unfold C4 at hC4
    nlinarith
  have harccos : arccos (cos (x p) / lam p) = y p :=
    Real.arccos_eq_of_eq_cos hy0.le
      (hyq.trans (by linarith [Real.pi_pos])).le hratio
  have hetaEq : etaRoot t xi = eta := by
    calc
      etaRoot t xi =
          arccos (cos (x p) / lam p) -
            ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
              brick.yXiSlope * xi) := by rfl
      _ = y p -
            ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
              brick.yXiSlope * xi) := by rw [harccos]
      _ = eta := by
        simp [p, zAt, y, pointOf]
  rw [hetaEq]
  exact ⟨heta, hzero⟩

/-- The explicit `C3 = 0` graph over the `rho` coordinate. -/
private def sigmaRoot (t rho : ℝ) : ℝ :=
  arccos
      (cos ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho) /
        ((lamMid : ℝ) + t)) -
    ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
      brick.vRhoSlope * rho)

private theorem sigmaRoot_continuous (t : ℝ) : Continuous (sigmaRoot t) := by
  unfold sigmaRoot
  fun_prop

/-- The explicit `C3` root stays inside the certified `sigma` interval. -/
private theorem sigmaRoot_spec {t rho : ℝ}
    (ht : tInterval.RealContains t)
    (hrho : rho ∈ Icc (-radiiReal 2) (radiiReal 2)) :
    sigmaRoot t rho ∈ Icc (-radiiReal 3) (radiiReal 3) ∧
      C3 (pointOf t ![0, 0, rho, sigmaRoot t rho]) = 0 := by
  let zAt : ℝ → Vec4 := fun sigma => ![0, 0, rho, sigma]
  have hzAt : Continuous zAt := by
    apply continuous_pi
    intro j
    fin_cases j <;> simp [zAt] <;> fun_prop
  have hz (sigma : ℝ) (hsigma : sigma ∈ Icc (-radiiReal 3) (radiiReal 3)) :
      InSymmetricBox radiiReal (zAt sigma) := by
    exact vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1) hrho hsigma
  have hlo : C3 (pointOf t (zAt (-radiiReal 3))) ≤ 0 := by
    have h := analyticFaceBounds.lowFaces t (zAt (-radiiReal 3)) ht
      (hz _ ⟨le_rfl, (neg_le_self (radiiReal_pos 3).le)⟩) 3 (by simp [zAt])
    simpa [rootMap] using h
  have hhi : 0 ≤ C3 (pointOf t (zAt (radiiReal 3))) := by
    have h := analyticFaceBounds.highFaces t (zAt (radiiReal 3)) ht
      (hz _ ⟨(neg_le_self (radiiReal_pos 3).le), le_rfl⟩) 3 (by simp [zAt])
    simpa [rootMap] using h
  have hcont : Continuous (fun sigma => C3 (pointOf t (zAt sigma))) := by
    unfold C3 pointOf w v lam
    fun_prop
  rcases oppositeFace_zero
      (show -radiiReal 3 ≤ radiiReal 3 from neg_le_self (radiiReal_pos 3).le)
      hcont.continuousOn hlo hhi with ⟨sigma, hsigma, hzero⟩
  let p := pointOf t (zAt sigma)
  have hzsigma : InSymmetricBox radiiReal (zAt sigma) := hz sigma hsigma
  have hbranches := affine_branches t (zAt sigma) ht hzsigma
  rcases hbranches with ⟨_, _, _, _, _, _, hv0, hvq⟩
  have hlamLo : (51 / 50 : ℝ) ≤ (lamMid : ℝ) + t := by
    have ht' := ht
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht'
    norm_num [lamMid, brick]
    linarith
  have hlamPos : 0 < lam p := by
    change 0 < (lamMid : ℝ) + t
    linarith
  have hC3 : C3 p = 0 := by simpa [p] using hzero
  have hratio : cos (w p) / lam p = cos (v p) := by
    apply (div_eq_iff (ne_of_gt hlamPos)).2
    unfold C3 at hC3
    nlinarith
  have harccos : arccos (cos (w p) / lam p) = v p :=
    Real.arccos_eq_of_eq_cos hv0.le
      (hvq.trans (by linarith [Real.pi_pos])).le hratio
  have hsigmaEq : sigmaRoot t rho = sigma := by
    calc
      sigmaRoot t rho =
          arccos (cos (w p) / lam p) -
            ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho) := by rfl
      _ = v p -
            ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho) := by rw [harccos]
      _ = sigma := by
        simp [p, zAt, v, pointOf, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [hsigmaEq]
  exact ⟨hsigma, hzero⟩

/-- The type-(iii) curvature represented by the certified `rho` coordinate. -/
def typeThreeCellHeight (t rho : ℝ) : ℝ :=
  (1 + cos ((brick.centers 2 : ℝ) + brick.slopes 2 * t + rho)) / 2

/-- The compact type-(iii) curvature projection of the prototype cell.  The
endpoints are reversed because cosine is decreasing on the certified branch. -/
def typeThreeCellInterval (t : ℝ) : Set ℝ :=
  Icc (typeThreeCellHeight t (radiiReal 2))
    (typeThreeCellHeight t (-radiiReal 2))

private theorem typeThreeCellAngle_mem_Icc_zero_pi
    {t rho : ℝ} (ht : tInterval.RealContains t)
    (hrho : rho ∈ Icc (-radiiReal 2) (radiiReal 2)) :
    (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho ∈ Icc (0 : ℝ) π := by
  rcases sigmaRoot_spec ht hrho with ⟨hsigma, _⟩
  have hz := vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1)
    hrho hsigma
  rcases affine_branches t ![0, 0, rho, sigmaRoot t rho] ht hz with
    ⟨_, _, _, _, hw0, hwq, _, _⟩
  have hwpi : w (pointOf t ![0, 0, rho, sigmaRoot t rho]) < π :=
    hwq.trans (by linarith [Real.pi_pos])
  simpa [w, pointOf, Matrix.cons_val_two, Matrix.cons_val_three] using
    And.intro hw0.le hwpi.le

theorem typeThreeCellHeight_mem_interval
    {t rho : ℝ} (ht : tInterval.RealContains t)
    (hrho : rho ∈ Icc (-radiiReal 2) (radiiReal 2)) :
    typeThreeCellHeight t rho ∈ typeThreeCellInterval t := by
  have hcur := typeThreeCellAngle_mem_Icc_zero_pi ht hrho
  have hright := typeThreeCellAngle_mem_Icc_zero_pi ht
    (show radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)
  have hleft := typeThreeCellAngle_mem_Icc_zero_pi ht
    (show -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)
  constructor
  · have hangle :
        (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho ≤
          (brick.centers 2 : ℝ) + brick.slopes 2 * t + radiiReal 2 := by
      linarith [hrho.2]
    have hcos := Real.strictAntiOn_cos.antitoneOn hcur hright hangle
    unfold typeThreeCellHeight
    linarith
  · have hangle :
        (brick.centers 2 : ℝ) + brick.slopes 2 * t - radiiReal 2 ≤
          (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho := by
      linarith [hrho.1]
    have hcos := Real.strictAntiOn_cos.antitoneOn hleft hcur hangle
    unfold typeThreeCellHeight
    linarith

private theorem typeThreeCellHeight_mem_Ioo
    {t rho : ℝ} (ht : tInterval.RealContains t)
    (hrho : rho ∈ Icc (-radiiReal 2) (radiiReal 2)) :
    typeThreeCellHeight t rho ∈ Ioo (0 : ℝ) 1 := by
  rcases sigmaRoot_spec ht hrho with ⟨hsigma, _⟩
  have hz := vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1)
    hrho hsigma
  rcases affine_branches t ![0, 0, rho, sigmaRoot t rho] ht hz with
    ⟨_, _, _, _, hw0, hwq, _, _⟩
  have hwpi : w (pointOf t ![0, 0, rho, sigmaRoot t rho]) < π :=
    hwq.trans (by linarith [Real.pi_pos])
  have hwpi2 : w (pointOf t ![0, 0, rho, sigmaRoot t rho]) < π / 2 := by
    linarith [Real.pi_pos]
  have hcos_pos : 0 <
      cos (w (pointOf t ![0, 0, rho, sigmaRoot t rho])) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hwpi2⟩
  have hcos_lt_one : cos
      (w (pointOf t ![0, 0, rho, sigmaRoot t rho])) < 1 := by
    have hzero : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
    have hwmem : w (pointOf t ![0, 0, rho, sigmaRoot t rho]) ∈ Icc 0 π :=
      ⟨hw0.le, hwpi.le⟩
    simpa using Real.strictAntiOn_cos hzero hwmem hw0
  simpa [typeThreeCellHeight, w, pointOf, Matrix.cons_val_two,
    Matrix.cons_val_three] using
    (show 0 < (1 + cos
        (w (pointOf t ![0, 0, rho, sigmaRoot t rho]))) / 2 ∧
      (1 + cos
        (w (pointOf t ![0, 0, rho, sigmaRoot t rho]))) / 2 < 1 by
      constructor <;> linarith)

theorem typeThreeCellInterval_subset_regular
    {t : ℝ} (ht : tInterval.RealContains t) :
    typeThreeCellInterval t ⊆ Ioo (0 : ℝ) 1 := by
  intro h hh
  have hlo := typeThreeCellHeight_mem_Ioo ht
    (show radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)
  have hhi := typeThreeCellHeight_mem_Ioo ht
    (show -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)
  exact ⟨hlo.1.trans_le hh.1, hh.2.trans_lt hhi.2⟩

/-- Every curvature in the compact projection has negative type-(iii) area
derivative.  The proof reconstructs its certified `rho` coordinate by IVT and
then applies the uniform `K3 < 0` certificate on the explicit `C3 = 0` graph. -/
theorem typeThreeArea_deriv_neg_on_cellInterval
    {t h₃ : ℝ} (ht : tInterval.RealContains t)
    (hh₃ : h₃ ∈ typeThreeCellInterval t) :
    deriv (LeanSuffixAnalytic.typeThreeArea ((lamMid : ℝ) + t)) h₃ < 0 := by
  have hrad : -radiiReal 2 ≤ radiiReal 2 :=
    neg_le_self (radiiReal_pos 2).le
  have hcont : ContinuousOn (typeThreeCellHeight t)
      (Icc (-radiiReal 2) (radiiReal 2)) := by
    apply Continuous.continuousOn
    unfold typeThreeCellHeight
    fun_prop
  have hh₃' : h₃ ∈ Icc
      (typeThreeCellHeight t (radiiReal 2))
      (typeThreeCellHeight t (-radiiReal 2)) := by
    simpa [typeThreeCellInterval] using hh₃
  rcases intermediate_value_Icc' hrad hcont hh₃' with
    ⟨rho, hrho, hrfl⟩
  let z : Vec4 := ![0, 0, rho, sigmaRoot t rho]
  let p : Point := pointOf t z
  rcases sigmaRoot_spec ht hrho with ⟨hsigma, hC3'⟩
  have hz : InSymmetricBox radiiReal z := by
    simpa [z] using vector_mem_box (zero_mem_coordinate 0)
      (zero_mem_coordinate 1) hrho hsigma
  rcases affine_branches t z ht hz with
    ⟨_, _, _, _, hw0, hwq, hv0, hvq⟩
  have hC3 : C3 p = 0 := by
    simpa [p, z] using hC3'
  have hlamCell : lamInterval.RealContains ((lamMid : ℝ) + t) := by
    apply lambda_iff_centered.mpr
    convert ht using 1 <;> ring
  have hlamPoint : 1 < lam p := by
    simpa [p, z, lam, pointOf] using
      (lambda_in_retainedSuffix hlamCell).one_lt
  have hlamEq : lam p = (lamMid : ℝ) + t := by
    simp [p, z, lam, pointOf]
  have hhEq :
      (1 + cos (w p)) / 2 = typeThreeCellHeight t rho := by
    simp [p, z, w, pointOf, typeThreeCellHeight, Matrix.cons_val_two,
      Matrix.cons_val_three]
  rw [← hrfl, ← hlamEq, ← hhEq]
  rw [typeThreeArea_deriv_eq_K3 p hlamPoint
    ⟨hw0, hwq, hv0, hvq⟩ hC3]
  exact div_neg_of_neg_of_pos
    (by simpa [p] using descendingK3 t z ht hz)
    (pow_pos (by
      rw [hhEq]
      exact (typeThreeCellHeight_mem_Ioo ht hrho).1) 3)

/-- The actual type-(iii) area is strictly decreasing on the entire compact
curvature projection of the first prototype cell. -/
theorem typeThreeArea_strictAntiOn_cellInterval
    {t : ℝ} (ht : tInterval.RealContains t) :
    StrictAntiOn
      (LeanSuffixAnalytic.typeThreeArea ((lamMid : ℝ) + t))
      (typeThreeCellInterval t) := by
  have hlamCell : lamInterval.RealContains ((lamMid : ℝ) + t) := by
    apply lambda_iff_centered.mpr
    convert ht using 1 <;> ring
  have hlo := typeThreeCellHeight_mem_Ioo ht
    (show radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)
  have hhi := typeThreeCellHeight_mem_Ioo ht
    (show -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)
  apply LeanSuffixAnalytic.typeThreeArea_strictAntiOn_Icc
    (lambda_in_retainedSuffix hlamCell).one_lt hlo.1 hhi.2
  intro h hh
  exact typeThreeArea_deriv_neg_on_cellInterval ht ⟨hh.1.le, hh.2.le⟩

/-- The type-(iv) curvature represented by the certified `xi` coordinate. -/
def typeFourCellHeight (t xi : ℝ) : ℝ :=
  cos ((brick.centers 0 : ℝ) + brick.slopes 0 * t + xi)

/-- The compact type-(iv) curvature projection of the prototype cell.  The
endpoints are reversed because cosine is decreasing on the certified branch. -/
def typeFourCellInterval (t : ℝ) : Set ℝ :=
  Icc (typeFourCellHeight t (radiiReal 0))
    (typeFourCellHeight t (-radiiReal 0))

private theorem typeFourCellAngle_mem_Icc_zero_pi
    {t xi : ℝ} (ht : tInterval.RealContains t)
    (hxi : xi ∈ Icc (-radiiReal 0) (radiiReal 0)) :
    (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi ∈ Icc (0 : ℝ) π := by
  rcases etaRoot_spec ht hxi with ⟨heta, _⟩
  have hz := vector_mem_box hxi heta (zero_mem_coordinate 2)
    (zero_mem_coordinate 3)
  rcases affine_branches t ![xi, etaRoot t xi, 0, 0] ht hz with
    ⟨hx0, hxq, _, _, _, _, _, _⟩
  have hxpi : x (pointOf t ![xi, etaRoot t xi, 0, 0]) < π :=
    hxq.trans (by linarith [Real.pi_pos])
  simpa [x, pointOf] using And.intro hx0.le hxpi.le

theorem typeFourCellHeight_mem_interval
    {t xi : ℝ} (ht : tInterval.RealContains t)
    (hxi : xi ∈ Icc (-radiiReal 0) (radiiReal 0)) :
    typeFourCellHeight t xi ∈ typeFourCellInterval t := by
  have hcur := typeFourCellAngle_mem_Icc_zero_pi ht hxi
  have hright := typeFourCellAngle_mem_Icc_zero_pi ht
    (show radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) from
      ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩)
  have hleft := typeFourCellAngle_mem_Icc_zero_pi ht
    (show -radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩)
  constructor
  · have hangle :
        (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi ≤
          (brick.centers 0 : ℝ) + brick.slopes 0 * t + radiiReal 0 := by
      linarith [hxi.2]
    exact Real.strictAntiOn_cos.antitoneOn hcur hright hangle
  · have hangle :
        (brick.centers 0 : ℝ) + brick.slopes 0 * t - radiiReal 0 ≤
          (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi := by
      linarith [hxi.1]
    exact Real.strictAntiOn_cos.antitoneOn hleft hcur hangle

private theorem typeFourCellHeight_mem_Ioo
    {t xi : ℝ} (ht : tInterval.RealContains t)
    (hxi : xi ∈ Icc (-radiiReal 0) (radiiReal 0)) :
    typeFourCellHeight t xi ∈ Ioo (0 : ℝ) 1 := by
  rcases etaRoot_spec ht hxi with ⟨heta, _⟩
  have hz := vector_mem_box hxi heta (zero_mem_coordinate 2)
    (zero_mem_coordinate 3)
  rcases affine_branches t ![xi, etaRoot t xi, 0, 0] ht hz with
    ⟨hx0, hxq, _, _, _, _, _, _⟩
  have hxpi : x (pointOf t ![xi, etaRoot t xi, 0, 0]) < π :=
    hxq.trans (by linarith [Real.pi_pos])
  have hxpi2 : x (pointOf t ![xi, etaRoot t xi, 0, 0]) < π / 2 := by
    linarith [Real.pi_pos]
  have hcos_pos :
      0 < cos (x (pointOf t ![xi, etaRoot t xi, 0, 0])) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxpi2⟩
  have hcos_lt_one :
      cos (x (pointOf t ![xi, etaRoot t xi, 0, 0])) < 1 := by
    have hzero : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
    have hxmem : x (pointOf t ![xi, etaRoot t xi, 0, 0]) ∈ Icc 0 π :=
      ⟨hx0.le, hxpi.le⟩
    simpa using Real.strictAntiOn_cos hzero hxmem hx0
  simpa [typeFourCellHeight, x, pointOf] using And.intro hcos_pos hcos_lt_one

theorem typeFourCellInterval_subset_regular
    {t : ℝ} (ht : tInterval.RealContains t) :
    typeFourCellInterval t ⊆ Ioo (0 : ℝ) 1 := by
  intro h hh
  have hlo := typeFourCellHeight_mem_Ioo ht
    (show radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) from
      ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩)
  have hhi := typeFourCellHeight_mem_Ioo ht
    (show -radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩)
  exact ⟨hlo.1.trans_le hh.1, hh.2.trans_lt hhi.2⟩

/-- Every type-(iv) curvature in the projected prototype cell has a
type-(iii) curvature in its projected cell with the same modeled area and
strictly smaller modeled perimeter. -/
theorem projected_typeFour_scalarImprovement_exists
    {t h₄ : ℝ} (ht : tInterval.RealContains t)
    (hh₄ : h₄ ∈ typeFourCellInterval t) :
    ∃ h₃, h₃ ∈ typeThreeCellInterval t ∧
      LeanSuffixAnalytic.typeThreeArea ((lamMid : ℝ) + t) h₃ =
        LeanSuffixAnalytic.typeFourArea ((lamMid : ℝ) + t) h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter ((lamMid : ℝ) + t) h₃ <
        LeanSuffixAnalytic.typeFourPerimeter ((lamMid : ℝ) + t) h₄ := by
  have hrad : -radiiReal 0 ≤ radiiReal 0 :=
    neg_le_self (radiiReal_pos 0).le
  have hcont : ContinuousOn (typeFourCellHeight t)
      (Icc (-radiiReal 0) (radiiReal 0)) := by
    apply Continuous.continuousOn
    unfold typeFourCellHeight
    fun_prop
  have hh₄' : h₄ ∈ Icc
      (typeFourCellHeight t (radiiReal 0))
      (typeFourCellHeight t (-radiiReal 0)) := by
    simpa [typeFourCellInterval] using hh₄
  rcases intermediate_value_Icc' hrad hcont hh₄' with
    ⟨xi, hxi, hheight⟩
  let eta := etaRoot t xi
  have hetaSpec := etaRoot_spec ht hxi
  have heta : eta ∈ Icc (-radiiReal 1) (radiiReal 1) := hetaSpec.1
  have hC4' : C4 (pointOf t ![xi, eta, 0, 0]) = 0 := by
    simpa [eta] using hetaSpec.2
  let zE : ℝ → Vec4 := fun rho => ![xi, eta, rho, sigmaRoot t rho]
  have hzE_cont : Continuous zE := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun _ : ℝ => xi)
      fun_prop
    · change Continuous (fun _ : ℝ => eta)
      fun_prop
    · change Continuous (fun rho : ℝ => rho)
      fun_prop
    · change Continuous (fun rho : ℝ => sigmaRoot t rho)
      exact sigmaRoot_continuous t
  have hrhoLow : -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩
  have hrhoHigh : radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) :=
    ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩
  have hsigmaLow := (sigmaRoot_spec ht hrhoLow).1
  have hsigmaHigh := (sigmaRoot_spec ht hrhoHigh).1
  have hzELow : InSymmetricBox radiiReal (zE (-radiiReal 2)) :=
    vector_mem_box hxi heta hrhoLow hsigmaLow
  have hzEHigh : InSymmetricBox radiiReal (zE (radiiReal 2)) :=
    vector_mem_box hxi heta hrhoHigh hsigmaHigh
  have hloE : rootMap t (zE (-radiiReal 2)) 2 ≤ 0 :=
    analyticFaceBounds.lowFaces t _ ht hzELow 2
      (by simp [zE, Matrix.cons_val_two])
  have hhiE : 0 ≤ rootMap t (zE (radiiReal 2)) 2 :=
    analyticFaceBounds.highFaces t _ ht hzEHigh 2
      (by simp [zE, Matrix.cons_val_two])
  have hcontE : Continuous (fun rho => rootMap t (zE rho) 2) :=
    (continuous_apply (2 : Fin 4)).comp ((rootMap_continuous t).comp hzE_cont)
  rcases oppositeFace_zero
      (show -radiiReal 2 ≤ radiiReal 2 from neg_le_self (radiiReal_pos 2).le)
      hcontE.continuousOn hloE hhiE with ⟨rho, hrho, hE⟩
  let sigma := sigmaRoot t rho
  have hsigmaSpec := sigmaRoot_spec ht hrho
  have hsigma : sigma ∈ Icc (-radiiReal 3) (radiiReal 3) := hsigmaSpec.1
  have hC3' : C3 (pointOf t ![0, 0, rho, sigma]) = 0 := by
    simpa [sigma] using hsigmaSpec.2
  let z : Vec4 := ![xi, eta, rho, sigma]
  let p : Point := pointOf t z
  have hz : InSymmetricBox radiiReal z :=
    vector_mem_box hxi heta hrho hsigma
  have hbranches := affine_branches t z ht hz
  have hC4 : C4 p = 0 := by
    simpa [p, z, C4, x, y, lam, pointOf] using hC4'
  have hC3 : C3 p = 0 := by
    simpa [p, z, C3, w, v, lam, pointOf, Matrix.cons_val_three] using hC3'
  have hEPoint : E p = 0 := by
    simpa [p, z, zE, sigma, rootMap, Matrix.cons_val_two] using hE
  have hlamCell : lamInterval.RealContains ((lamMid : ℝ) + t) := by
    apply lambda_iff_centered.mpr
    convert ht using 1 <;> ring
  have hlamPoint : 1 < lam p := by
    simpa [p, z, lam, pointOf] using
      (lambda_in_retainedSuffix hlamCell).one_lt
  have hsem := pointEquationSemantics p hlamPoint hbranches hC4 hC3
  have harea := hsem.equalArea_of_E_zero hEPoint
  have hG : G p < 0 := by
    have hcertified : G p < -(437 / 1000000 : ℝ) := by
      simpa [p] using gap_upper t z ht hz
    exact hcertified.trans (by norm_num)
  have hperimeter := hsem.perimeter_lt_of_G_neg hG
  have hlamEq : lam p = (lamMid : ℝ) + t := by
    simp [p, z, lam, pointOf]
  have hh₃Eq :
      (1 + cos (w p)) / 2 = typeThreeCellHeight t rho := by
    simp [p, z, w, pointOf, typeThreeCellHeight, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh₄Eq : cos (x p) = typeFourCellHeight t xi := by
    simp [p, z, x, pointOf, typeFourCellHeight]
  refine ⟨typeThreeCellHeight t rho,
    typeThreeCellHeight_mem_interval ht hrho, ?_, ?_⟩
  · simpa [hlamEq, hh₃Eq, hh₄Eq, hheight] using harea
  · simpa [hlamEq, hh₃Eq, hh₄Eq, hheight] using hperimeter

/-- A selected equal-area type-(iii) root for each projected type-(iv)
curvature.  Values outside the projected cell are immaterial. -/
noncomputable def pilotEqualAreaRoot
    (t : ℝ) (ht : tInterval.RealContains t) : ℝ → ℝ := by
  classical
  intro h₄
  exact if hh₄ : h₄ ∈ typeFourCellInterval t then
    Classical.choose (projected_typeFour_scalarImprovement_exists ht hh₄)
  else
    typeThreeCellHeight t (radiiReal 2)

theorem pilotEqualAreaRoot_spec
    {t h₄ : ℝ} (ht : tInterval.RealContains t)
    (hh₄ : h₄ ∈ typeFourCellInterval t) :
    pilotEqualAreaRoot t ht h₄ ∈ typeThreeCellInterval t ∧
      LeanSuffixAnalytic.typeThreeArea ((lamMid : ℝ) + t)
          (pilotEqualAreaRoot t ht h₄) =
        LeanSuffixAnalytic.typeFourArea ((lamMid : ℝ) + t) h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter ((lamMid : ℝ) + t)
          (pilotEqualAreaRoot t ht h₄) <
        LeanSuffixAnalytic.typeFourPerimeter ((lamMid : ℝ) + t) h₄ := by
  classical
  simpa [pilotEqualAreaRoot, dif_pos hh₄] using
    (Classical.choose_spec
      (projected_typeFour_scalarImprovement_exists ht hh₄))

theorem pilotEqualAreaRoot_continuousOn
    {t : ℝ} (ht : tInterval.RealContains t) :
    ContinuousOn (pilotEqualAreaRoot t ht) (typeFourCellInterval t) := by
  have hlamCell : lamInterval.RealContains ((lamMid : ℝ) + t) := by
    apply lambda_iff_centered.mpr
    convert ht using 1 <;> ring
  apply LeanSuffixAnalytic.equalAreaRoot_continuousOn_of_Icc_deriv_neg
    (lambda_in_retainedSuffix hlamCell).one_lt
    (typeFourCellInterval_subset_regular ht)
    (typeThreeCellHeight_mem_Ioo ht
      (show radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
        ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)).1
    (typeThreeCellHeight_mem_Ioo ht
      (show -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) from
        ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)).2
  · intro h₄ hh₄
    simpa [typeThreeCellInterval] using
      (pilotEqualAreaRoot_spec ht hh₄).1
  · intro h₄ hh₄
    exact (pilotEqualAreaRoot_spec ht hh₄).2.1
  · intro y hy
    exact typeThreeArea_deriv_neg_on_cellInterval ht ⟨hy.1.le, hy.2.le⟩

/-- The first prototype cell has a checker root by four scalar IVTs.  The
triangular dependence avoids any unproved multidimensional root principle. -/
theorem triangular_root (t : ℝ) (ht : tInterval.RealContains t) :
    ∃ z, InSymmetricBox radiiReal z ∧ ∀ j, rootMap t z j = 0 := by
  let zF : ℝ → Vec4 := fun xi => ![xi, etaRoot t xi, 0, 0]
  have hzF_cont : Continuous zF := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun xi : ℝ => xi)
      fun_prop
    · change Continuous (fun xi : ℝ => etaRoot t xi)
      exact etaRoot_continuous t
    · change Continuous (fun _ : ℝ => (0 : ℝ))
      fun_prop
    · change Continuous (fun _ : ℝ => (0 : ℝ))
      fun_prop
  have hxiLow : -radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩
  have hxiHigh : radiiReal 0 ∈ Icc (-radiiReal 0) (radiiReal 0) :=
    ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩
  have hetaLow := (etaRoot_spec ht hxiLow).1
  have hetaHigh := (etaRoot_spec ht hxiHigh).1
  have hzFLow : InSymmetricBox radiiReal (zF (-radiiReal 0)) :=
    vector_mem_box hxiLow hetaLow (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hzFHigh : InSymmetricBox radiiReal (zF (radiiReal 0)) :=
    vector_mem_box hxiHigh hetaHigh (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hloF : rootMap t (zF (-radiiReal 0)) 0 ≤ 0 :=
    analyticFaceBounds.lowFaces t _ ht hzFLow 0 (by simp [zF])
  have hhiF : 0 ≤ rootMap t (zF (radiiReal 0)) 0 :=
    analyticFaceBounds.highFaces t _ ht hzFHigh 0 (by simp [zF])
  have hcontF : Continuous (fun xi => rootMap t (zF xi) 0) :=
    (continuous_apply (0 : Fin 4)).comp ((rootMap_continuous t).comp hzF_cont)
  rcases oppositeFace_zero
      (show -radiiReal 0 ≤ radiiReal 0 from neg_le_self (radiiReal_pos 0).le)
      hcontF.continuousOn hloF hhiF with ⟨xi, hxi, hF⟩
  let eta := etaRoot t xi
  have hetaSpec := etaRoot_spec ht hxi
  have heta : eta ∈ Icc (-radiiReal 1) (radiiReal 1) := hetaSpec.1
  have hC4 : C4 (pointOf t ![xi, eta, 0, 0]) = 0 := by
    simpa [eta] using hetaSpec.2
  let zE : ℝ → Vec4 := fun rho => ![xi, eta, rho, sigmaRoot t rho]
  have hzE_cont : Continuous zE := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun _ : ℝ => xi)
      fun_prop
    · change Continuous (fun _ : ℝ => eta)
      fun_prop
    · change Continuous (fun rho : ℝ => rho)
      fun_prop
    · change Continuous (fun rho : ℝ => sigmaRoot t rho)
      exact sigmaRoot_continuous t
  have hrhoLow : -radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩
  have hrhoHigh : radiiReal 2 ∈ Icc (-radiiReal 2) (radiiReal 2) :=
    ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩
  have hsigmaLow := (sigmaRoot_spec ht hrhoLow).1
  have hsigmaHigh := (sigmaRoot_spec ht hrhoHigh).1
  have hzELow : InSymmetricBox radiiReal (zE (-radiiReal 2)) :=
    vector_mem_box hxi heta hrhoLow hsigmaLow
  have hzEHigh : InSymmetricBox radiiReal (zE (radiiReal 2)) :=
    vector_mem_box hxi heta hrhoHigh hsigmaHigh
  have hloE : rootMap t (zE (-radiiReal 2)) 2 ≤ 0 :=
    analyticFaceBounds.lowFaces t _ ht hzELow 2
      (by simp [zE, Matrix.cons_val_two])
  have hhiE : 0 ≤ rootMap t (zE (radiiReal 2)) 2 :=
    analyticFaceBounds.highFaces t _ ht hzEHigh 2
      (by simp [zE, Matrix.cons_val_two])
  have hcontE : Continuous (fun rho => rootMap t (zE rho) 2) :=
    (continuous_apply (2 : Fin 4)).comp ((rootMap_continuous t).comp hzE_cont)
  rcases oppositeFace_zero
      (show -radiiReal 2 ≤ radiiReal 2 from neg_le_self (radiiReal_pos 2).le)
      hcontE.continuousOn hloE hhiE with ⟨rho, hrho, hE⟩
  let sigma := sigmaRoot t rho
  have hsigmaSpec := sigmaRoot_spec ht hrho
  have hsigma : sigma ∈ Icc (-radiiReal 3) (radiiReal 3) := hsigmaSpec.1
  have hC3 : C3 (pointOf t ![0, 0, rho, sigma]) = 0 := by
    simpa [sigma] using hsigmaSpec.2
  let z : Vec4 := ![xi, eta, rho, sigma]
  refine ⟨z, vector_mem_box hxi heta hrho hsigma, ?_⟩
  intro j
  fin_cases j
  · simpa [zF, z, eta, rootMap, F, B4, D4, x, y, lam, pointOf] using hF
  · simpa [z, rootMap, C4, x, y, lam, pointOf] using hC4
  · simpa [zE, z, sigma, rootMap, Matrix.cons_val_two] using hE
  · simpa [z, rootMap, C3, w, v, lam, pointOf, Matrix.cons_val_three] using hC3

theorem rational_guards :
    (1 : ℚ) < brick.lamLo ∧ (∀ j, 0 < brick.radii j) ∧ brick.lamHi < 9 / 7 := by
  refine ⟨by norm_num [brick], brick.radiiPos, ?_⟩
  norm_num [brick]

/-- Fold/equal-area/gap consequence of the kernel-checked triangular root
construction. -/
theorem realConclusion
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃ p : Point, lam p = lam0 ∧ InSymmetricBox radiiReal (vars p) ∧
      C4 p = 0 ∧ F p = 0 ∧ C3 p = 0 ∧ E p = 0 ∧ G p < 0 := by
  let t : ℝ := lam0 - (lamMid : ℝ)
  have ht : tInterval.RealContains t := lambda_iff_centered.mp hlam
  rcases triangular_root t ht with ⟨z, hz, hzero⟩
  let p := pointOf t z
  have h0 := hzero 0
  have h1 := hzero 1
  have h2 := hzero 2
  have h3 := hzero 3
  refine ⟨p, ?_, ?_, ?_, ?_, ?_, ?_, lt_trans (gap_upper t z ht hz) (by norm_num)⟩
  · simp [p, pointOf, lam, t]
  · intro j
    have hj := hz j
    fin_cases j <;> simpa [p, vars, pointOf] using hj
  · simpa [rootMap, p] using h1
  · have hn : -F p = 0 := by simpa [rootMap, p] using h0
    exact neg_eq_zero.mp hn
  · simpa [rootMap, p] using h3
  · simpa [rootMap, p] using h2

/-- The prototype-cell root is a genuine stationary equal-area scalar
comparison with a certified simple descending type-(iii) root, rather than an
uninterpreted zero of the checker coordinates. -/
theorem realConclusion_scalarImprovement
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃ p : Point, lam p = lam0 ∧ InSymmetricBox radiiReal (vars p) ∧
      let h₃ := (1 + cos (w p)) / 2
      let h₄ := cos (x p)
      1 / 2 < h₃ ∧ h₃ < 1 ∧
        0 < h₄ ∧ h₄ < 1 ∧
        LeanSuffixAnalytic.typeThreeArea (lam p) h₃ =
          LeanSuffixAnalytic.typeFourArea (lam p) h₄ ∧
        LeanSuffixAnalytic.typeFourFold (lam p) h₄ = 0 ∧
        LeanSuffixAnalytic.typeThreePerimeter (lam p) h₃ <
          LeanSuffixAnalytic.typeFourPerimeter (lam p) h₄ ∧
        LeanSuffixAnalytic.reducedFoldGap (lam p) h₃ h₄ < 0 ∧
        deriv (LeanSuffixAnalytic.typeThreeArea (lam p)) h₃ < 0 := by
  rcases realConclusion hlam with
    ⟨p, hpLam, hpbox, hC4, hF, hC3, hE, hG⟩
  refine ⟨p, hpLam, hpbox, ?_⟩
  have ht0 : tInterval.RealContains (lam0 - (lamMid : ℝ)) :=
    lambda_iff_centered.mp hlam
  have hpt : p.t = lam0 - (lamMid : ℝ) := by
    unfold lam at hpLam
    linarith
  have ht : tInterval.RealContains p.t := by
    rw [hpt]
    exact ht0
  have hbranches0 := affine_branches p.t (vars p) ht hpbox
  have hbranches :
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4 := by
    simpa [pointOf, vars] using hbranches0
  have hlamPoint : 1 < lam p := by
    rw [hpLam]
    exact (lambda_in_retainedSuffix hlam).one_lt
  rcases hbranches with
    ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  have hscalar := point_equations_to_scalar_improvement p hlamPoint
    ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
    hC4 hF hC3 hE hG
  dsimp only at hscalar ⊢
  rcases hscalar with
    ⟨hh₃_half, hh₃_one, hh₄_pos, hh₄_one, harea, hfold,
      hperimeter, hgap⟩
  refine ⟨hh₃_half, hh₃_one, hh₄_pos, hh₄_one, harea, hfold,
    hperimeter, hgap, ?_⟩
  rw [typeThreeArea_deriv_eq_K3 p hlamPoint
    ⟨hw0, hwq, hv0, hvq⟩ hC3]
  exact div_neg_of_neg_of_pos
    (by simpa [pointOf, vars] using descendingK3 p.t (vars p) ht hpbox)
    (pow_pos (lt_trans (by norm_num) hh₃_half) 3)

/-- At the certified stationary type-(iv) fold, the equal-area type-(iii)
curvature is the unique root in the prototype cell's compact projection.
Unlike pointwise derivative negativity, this is a branch-level consequence of
the uniform cell certificate. -/
theorem regularStationaryFold_equalAreaRoot_existsUniqueInCell
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃ fold : ℝ, fold ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourFold lam0 fold = 0 ∧
      ∃! h₃ : ℝ,
        h₃ ∈ typeThreeCellInterval (lam0 - (lamMid : ℝ)) ∧
        LeanSuffixAnalytic.typeThreeArea lam0 h₃ =
          LeanSuffixAnalytic.typeFourArea lam0 fold := by
  rcases realConclusion_scalarImprovement hlam with
    ⟨p, hpLam, hpbox, hscalar⟩
  dsimp only at hscalar
  rcases hscalar with
    ⟨_hh₃_half, _hh₃_one, hh₄_pos, hh₄_one, harea, hfold,
      _hperimeter, _hgap, _hderiv⟩
  let t : ℝ := lam0 - (lamMid : ℝ)
  have ht : tInterval.RealContains t := by
    exact lambda_iff_centered.mp hlam
  have hpt : p.t = t := by
    unfold lam at hpLam
    dsimp [t]
    linarith
  have hpRho : p.rho ∈ Icc (-radiiReal 2) (radiiReal 2) := by
    simpa [vars, Matrix.cons_val_two, Matrix.cons_val_three] using hpbox 2
  have hhEq :
      typeThreeCellHeight t p.rho = (1 + cos (w p)) / 2 := by
    simp [typeThreeCellHeight, w, hpt]
  have hh₃_mem :
      (1 + cos (w p)) / 2 ∈ typeThreeCellInterval t := by
    rw [← hhEq]
    exact typeThreeCellHeight_mem_interval ht hpRho
  have harea0 :
      LeanSuffixAnalytic.typeThreeArea lam0 ((1 + cos (w p)) / 2) =
        LeanSuffixAnalytic.typeFourArea lam0 (cos (x p)) := by
    simpa [hpLam] using harea
  have hfold0 :
      LeanSuffixAnalytic.typeFourFold lam0 (cos (x p)) = 0 := by
    simpa [hpLam] using hfold
  have hanti := typeThreeArea_strictAntiOn_cellInterval ht
  have hcenter : (lamMid : ℝ) + t = lam0 := by
    dsimp [t]
    ring
  rw [hcenter] at hanti
  refine ⟨cos (x p), ⟨hh₄_pos, hh₄_one⟩, hfold0, ?_⟩
  refine ⟨(1 + cos (w p)) / 2, ⟨hh₃_mem, harea0⟩, ?_⟩
  intro y hy
  exact hanti.injOn hy.1 hh₃_mem (hy.2.trans harea0.symm)

/-- The exact pilot cell contains exactly one regular stationary type-(iv)
curvature.  Existence is supplied by the triangular certificate root; global
uniqueness on `0 < h₄ < 1` is analytic and does not depend on the cell box. -/
theorem regularStationaryFold_existsUnique
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃! h₄ : ℝ, h₄ ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourFold lam0 h₄ = 0 := by
  rcases realConclusion_scalarImprovement hlam with
    ⟨p, hpLam, _hpbox, hscalar⟩
  dsimp only at hscalar
  rcases hscalar with
    ⟨_hh₃_half, _hh₃_one, hh₄_pos, hh₄_one, _harea, hfold,
      _hperimeter, _hgap, _hderiv⟩
  have hfold0 :
      LeanSuffixAnalytic.typeFourFold lam0 (cos (x p)) = 0 := by
    simpa [hpLam] using hfold
  refine ⟨cos (x p), ⟨⟨hh₄_pos, hh₄_one⟩, hfold0⟩, ?_⟩
  intro h₄ hh₄
  exact LeanSuffixAnalytic.typeFourFold_zero_unique
    (lambda_in_retainedSuffix hlam).one_lt
    hh₄.1 ⟨hh₄_pos, hh₄_one⟩ hh₄.2 hfold0

/-- The pilot certificate supplies a stationary fold with the exact
before/after derivative signs needed by the equal-area envelope.  The signs
are consequences of the analytic fold identity, not certificate hypotheses. -/
theorem regularStationaryFold_areaDerivativeSigns
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃ fold : ℝ, fold ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourFold lam0 fold = 0 ∧
      (∀ ⦃h : ℝ⦄, h ∈ Ioo (0 : ℝ) 1 → h < fold →
        deriv (LeanSuffixAnalytic.typeFourArea lam0) h < 0) ∧
      (∀ ⦃h : ℝ⦄, h ∈ Ioo (0 : ℝ) 1 → fold < h →
        0 < deriv (LeanSuffixAnalytic.typeFourArea lam0) h) := by
  rcases regularStationaryFold_existsUnique hlam with ⟨fold, hfold, _hunique⟩
  refine ⟨fold, hfold.1, hfold.2, ?_, ?_⟩
  · intro h hh hlt
    exact LeanSuffixAnalytic.typeFourArea_deriv_neg_before_zero
      (lambda_in_retainedSuffix hlam).one_lt hfold.1 hfold.2 hh hlt
  · intro h hh hlt
    exact LeanSuffixAnalytic.typeFourArea_deriv_pos_after_zero
      (lambda_in_retainedSuffix hlam).one_lt hfold.1 hfold.2 hh hlt

/-- Every regular stationary type-(iv) curvature in the pilot cell is the
certified fold and therefore has a genuine equal-area, strictly shorter
type-(iii) scalar comparison whose type-(iii) area derivative is negative. -/
theorem regularStationaryFold_scalarImprovement
    {lam0 h₄ : ℝ} (hlam : lamInterval.RealContains lam0)
    (hh₄ : h₄ ∈ Ioo (0 : ℝ) 1)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam0 h₄ = 0) :
    ∃ h₃ : ℝ, 1 / 2 < h₃ ∧ h₃ < 1 ∧
      LeanSuffixAnalytic.typeThreeArea lam0 h₃ =
        LeanSuffixAnalytic.typeFourArea lam0 h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter lam0 h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam0 h₄ ∧
      LeanSuffixAnalytic.reducedFoldGap lam0 h₃ h₄ < 0 ∧
      deriv (LeanSuffixAnalytic.typeThreeArea lam0) h₃ < 0 := by
  rcases realConclusion_scalarImprovement hlam with
    ⟨p, hpLam, _hpbox, hscalar⟩
  dsimp only at hscalar
  rcases hscalar with
    ⟨hh₃_half, hh₃_one, hh₄_pos, hh₄_one, harea, hfold,
      hperimeter, hgap, hderiv⟩
  have hfold0 :
      LeanSuffixAnalytic.typeFourFold lam0 (cos (x p)) = 0 := by
    simpa [hpLam] using hfold
  have hh₄_eq : cos (x p) = h₄ :=
    LeanSuffixAnalytic.typeFourFold_zero_unique
      (lambda_in_retainedSuffix hlam).one_lt
      ⟨hh₄_pos, hh₄_one⟩ hh₄ hfold0 hstationary
  refine ⟨(1 + cos (w p)) / 2, hh₃_half, hh₃_one, ?_, ?_, ?_, ?_⟩
  · simpa [hpLam, hh₄_eq] using harea
  · simpa [hpLam, hh₄_eq] using hperimeter
  · simpa [hpLam, hh₄_eq] using hgap
  · simpa [hpLam] using hderiv

/-- The pilot certificate supplies one stationary equal-area pair on the
descending type-(iii) branch.  This pair promotes the local certificate to the
global equal-area envelope without restricting the eventual candidate
curvature to the pilot projection. -/
theorem stationaryEqualAreaPair_exists
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0) :
    ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair lam0,
      LeanSuffixAnalytic.typeThreeFold lam0 pair.h₃ < 0 ∧
        LeanSuffixAnalytic.typeThreePerimeter lam0 pair.h₃ <
          LeanSuffixAnalytic.typeFourPerimeter lam0 pair.h₄ := by
  rcases regularStationaryFold_existsUnique hlam with
    ⟨h₄, ⟨hh₄, hstationary⟩, _hunique⟩
  rcases regularStationaryFold_scalarImprovement hlam hh₄ hstationary with
    ⟨h₃, hh₃_half, hh₃_one, harea, hperimeter, _hgap, hderiv⟩
  have hh₃_pos : 0 < h₃ := lt_trans (by norm_num) hh₃_half
  have hfoldThree : LeanSuffixAnalytic.typeThreeFold lam0 h₃ < 0 := by
    rw [(LeanSuffixAnalytic.hasDerivAt_typeThreeArea
      (lambda_in_retainedSuffix hlam).one_lt hh₃_pos hh₃_one).deriv] at hderiv
    rcases div_neg_iff.mp hderiv with hbad | hgood
    · linarith [pow_pos hh₃_pos 3]
    · exact hgood.1
  let pair : LeanSuffixAnalytic.StationaryEqualAreaPair lam0 :=
    { h₃ := h₃
      h₄ := h₄
      h₃_gt_half := hh₃_half
      h₃_lt_one := hh₃_one
      h₄_pos := hh₄.1
      h₄_lt_one := hh₄.2
      equalArea := harea
      stationary := hstationary }
  refine ⟨pair, ?_, ?_⟩
  · simpa [pair] using hfoldThree
  · simpa [pair] using hperimeter

/-- A single stationary pair from the pilot certificate excludes every modeled
type-(iv) candidate at that density, including the `h₄ = 1` endpoint. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases stationaryEqualAreaPair_exists hlam with
    ⟨pair, hfoldThree, hperimeter⟩
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair
      candidate hcandidate pair hfoldThree hperimeter

/-- Candidate-facing end of the pilot-cell vertical slice for every regular
stationary type-(iv) root.  No stationarity is inferred from minimality: the
fold equation remains an explicit hypothesis, and `h₄ = 1` remains separate. -/
theorem regularStationaryCandidate_not_isWeightedPerimeterMinimizer
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1)
    (hstationary :
      LeanSuffixAnalytic.typeFourFold lam0 candidate.h = 0) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases regularStationaryFold_scalarImprovement hlam
      ⟨candidate.h_pos, hregular⟩ hstationary with
    ⟨h₃, hh₃_half, hh₃_one, harea, hperimeter, _hgap, _hderiv⟩
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
      candidate hcandidate (lt_trans (by norm_num) hh₃_half) hh₃_one
      harea hperimeter

/-- Every modeled type-(iv) candidate whose curvature lies in the exact pilot
cell projection has a genuine equal-area type-(iii) competitor with strictly
smaller weighted perimeter.  No stationarity hypothesis is required. -/
theorem projectedCandidate_not_isWeightedPerimeterMinimizer
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hprojected :
      candidate.h ∈ typeFourCellInterval (lam0 - (lamMid : ℝ))) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  have ht : tInterval.RealContains (lam0 - (lamMid : ℝ)) :=
    lambda_iff_centered.mp hlam
  rcases projected_typeFour_scalarImprovement_exists ht hprojected with
    ⟨h₃, hh₃Cell, harea, hperimeter⟩
  have hh₃ := typeThreeCellInterval_subset_regular ht hh₃Cell
  have hcenter : (lamMid : ℝ) + (lam0 - (lamMid : ℝ)) = lam0 := by
    ring
  rw [hcenter] at harea hperimeter
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
      candidate hcandidate hh₃.1 hh₃.2 harea hperimeter

end FirstPrototypeCell
end ScalarSuffixCertificate
