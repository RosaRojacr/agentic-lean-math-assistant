/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FourArcCandidate

/-!
# Kernel-checked exact-rational suffix certificates

This file defines the small interval language used by the reflective lane.
Certificate endpoints and all checker side conditions live in `ℚ`; `RealContains`
is the soundness boundary into the analytic model.
-/

noncomputable section

namespace LeanSuffixReflective

/-- A closed interval with exact rational endpoints. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

namespace QInterval

/-- Membership interpreted in exact rational arithmetic. -/
def Contains (i : QInterval) (x : ℚ) : Prop := i.lo ≤ x ∧ x ≤ i.hi

/-- Membership after the canonical embedding into the real analytic model. -/
def RealContains (i : QInterval) (x : ℝ) : Prop :=
  (i.lo : ℝ) ≤ x ∧ x ≤ (i.hi : ℝ)

/-- Point intervals are the leaves of exact certificate evaluation. -/
def point (x : ℚ) : QInterval := ⟨x, x, le_rfl⟩

/-- Exact interval addition. -/
def add (i j : QInterval) : QInterval :=
  ⟨i.lo + j.lo, i.hi + j.hi, add_le_add i.ordered j.ordered⟩

/-- Exact interval negation. -/
def neg (i : QInterval) : QInterval :=
  ⟨-i.hi, -i.lo, neg_le_neg i.ordered⟩

/-- Exact interval subtraction. -/
def sub (i j : QInterval) : QInterval := i.add j.neg

/-- Exact nonnegative scaling, sufficient for Taylor error radii and seams. -/
def nsmul (q : ℚ) (hq : 0 ≤ q) (i : QInterval) : QInterval :=
  ⟨q * i.lo, q * i.hi, mul_le_mul_of_nonneg_left i.ordered hq⟩

@[simp] theorem realContains_point (x : ℚ) (y : ℝ) :
    (point x).RealContains y ↔ y = (x : ℝ) := by
  constructor
  · intro h
    exact le_antisymm h.2 h.1
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-- Rational membership transports without loss to real membership. -/
theorem contains_toReal {i : QInterval} {x : ℚ} (h : i.Contains x) :
    i.RealContains (x : ℝ) := by
  simpa [Contains, RealContains] using h

/-- Soundness of exact interval addition. -/
theorem realContains_add {i j : QInterval} {x y : ℝ}
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (i.add j).RealContains (x + y) := by
  exact ⟨by simpa [RealContains, add] using add_le_add hx.1 hy.1,
    by simpa [RealContains, add] using add_le_add hx.2 hy.2⟩

/-- Soundness of exact interval negation. -/
theorem realContains_neg {i : QInterval} {x : ℝ}
    (hx : i.RealContains x) : i.neg.RealContains (-x) := by
  exact ⟨by simpa [RealContains, neg] using neg_le_neg hx.2,
    by simpa [RealContains, neg] using neg_le_neg hx.1⟩

/-- Soundness of exact interval subtraction. -/
theorem realContains_sub {i j : QInterval} {x y : ℝ}
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (i.sub j).RealContains (x - y) := by
  exact realContains_add hx (realContains_neg hy)

end QInterval

/-- The exact suffix covered by the retained certificate families. -/
def suffixDomain : QInterval :=
  ⟨51 / 50, 9 / 7, by norm_num⟩

/-- First retained seam: pilot face to middle-face tiling. -/
def pilotMiddleSeam : ℚ := 102001 / 100000

/-- Second retained seam: middle-face tiling to compact fold-gap boxes. -/
def middleCompactSeam : ℚ := 33 / 32

/-- The two exact seams are ordered and lie in the requested suffix. -/
theorem retained_seams_ordered :
    suffixDomain.lo < pilotMiddleSeam ∧
      pilotMiddleSeam < middleCompactSeam ∧
      middleCompactSeam < suffixDomain.hi := by
  norm_num [suffixDomain, pilotMiddleSeam, middleCompactSeam]

end LeanSuffixReflective
