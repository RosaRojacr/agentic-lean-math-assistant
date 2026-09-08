/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneScalarNormalization
import NearOneLocalInterval

/-!
# Source-native scalar interval certificates

A three-variable first-order interval jet.  Values and all three actual partial
 derivatives are enclosed on one rational box.  The centered enclosure theorem
is a telescope of three scalar mean-value applications; no numerical evaluator
is trusted.
-/

namespace NearOneScalarInterval

open Real Set
open NearOneScalarNormalization

noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

private theorem point_sound (q : ℚ) :
    (LeanSuffixReflective.QInterval.point q).RealContains (q : ℝ) :=
  (LeanSuffixReflective.QInterval.realContains_point q (q : ℝ)).2 rfl

private theorem mul_sound {i j : QInterval} {x y : ℝ}
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (ScalarSuffixCertificate.QInterval.mul i j).RealContains (x * y) :=
  ScalarSuffixCertificate.QInterval.realContains_mul hx hy

/-- Rational boxes for the scale and two moving-bracket errors. -/
structure Box3 where
  t : QInterval
  e4 : QInterval
  e3 : QInterval

namespace Box3

def Contains (box : Box3) (t e4 e3 : ℝ) : Prop :=
  box.t.RealContains t ∧ box.e4.RealContains e4 ∧ box.e3.RealContains e3

end Box3

/-- Exact value and actual first partials, each with a rational enclosure on a
single box. -/
structure Jet3 (box : Box3) where
  value : ℝ → ℝ → ℝ → ℝ
  dt : ℝ → ℝ → ℝ → ℝ
  de4 : ℝ → ℝ → ℝ → ℝ
  de3 : ℝ → ℝ → ℝ → ℝ
  range : QInterval
  dtRange : QInterval
  de4Range : QInterval
  de3Range : QInterval
  value_sound : ∀ {t e4 e3}, box.Contains t e4 e3 →
    range.RealContains (value t e4 e3)
  dt_sound : ∀ {t e4 e3}, box.Contains t e4 e3 →
    dtRange.RealContains (dt t e4 e3)
  de4_sound : ∀ {t e4 e3}, box.Contains t e4 e3 →
    de4Range.RealContains (de4 t e4 e3)
  de3_sound : ∀ {t e4 e3}, box.Contains t e4 e3 →
    de3Range.RealContains (de3 t e4 e3)
  hasDerivAt_t : ∀ {t e4 e3}, box.Contains t e4 e3 →
    HasDerivAt (fun x => value x e4 e3) (dt t e4 e3) t
  hasDerivAt_e4 : ∀ {t e4 e3}, box.Contains t e4 e3 →
    HasDerivAt (fun x => value t x e3) (de4 t e4 e3) e4
  hasDerivAt_e3 : ∀ {t e4 e3}, box.Contains t e4 e3 →
    HasDerivAt (fun x => value t e4 x) (de3 t e4 e3) e3

namespace Jet3
variable {box : Box3}

/-- Replace the four computed interval ranges by checked wider intervals
without changing the represented function or any derivative. -/
def widen (a : Jet3 box)
    (range dtRange de4Range de3Range : QInterval)
    (hRange : range.lo ≤ a.range.lo ∧ a.range.hi ≤ range.hi)
    (hDtRange : dtRange.lo ≤ a.dtRange.lo ∧ a.dtRange.hi ≤ dtRange.hi)
    (hDe4Range : de4Range.lo ≤ a.de4Range.lo ∧ a.de4Range.hi ≤ de4Range.hi)
    (hDe3Range : de3Range.lo ≤ a.de3Range.lo ∧ a.de3Range.hi ≤ de3Range.hi) :
    Jet3 box where
  value := a.value
  dt := a.dt
  de4 := a.de4
  de3 := a.de3
  range := range
  dtRange := dtRange
  de4Range := de4Range
  de3Range := de3Range
  value_sound := fun h => by
    have ha := a.value_sound h
    constructor
    · exact le_trans (by exact_mod_cast hRange.1) ha.1
    · exact le_trans ha.2 (by exact_mod_cast hRange.2)
  dt_sound := fun h => by
    have ha := a.dt_sound h
    constructor
    · exact le_trans (by exact_mod_cast hDtRange.1) ha.1
    · exact le_trans ha.2 (by exact_mod_cast hDtRange.2)
  de4_sound := fun h => by
    have ha := a.de4_sound h
    constructor
    · exact le_trans (by exact_mod_cast hDe4Range.1) ha.1
    · exact le_trans ha.2 (by exact_mod_cast hDe4Range.2)
  de3_sound := fun h => by
    have ha := a.de3_sound h
    constructor
    · exact le_trans (by exact_mod_cast hDe3Range.1) ha.1
    · exact le_trans ha.2 (by exact_mod_cast hDe3Range.2)
  hasDerivAt_t := a.hasDerivAt_t
  hasDerivAt_e4 := a.hasDerivAt_e4
  hasDerivAt_e3 := a.hasDerivAt_e3
/-- Variant of `widen` whose four enclosure checks can be discharged by one
exact-arithmetic proof. -/
def widenAll (a : Jet3 box)
    (range dtRange de4Range de3Range : QInterval)
    (h : (range.lo ≤ a.range.lo ∧ a.range.hi ≤ range.hi) ∧
      (dtRange.lo ≤ a.dtRange.lo ∧ a.dtRange.hi ≤ dtRange.hi) ∧
      (de4Range.lo ≤ a.de4Range.lo ∧ a.de4Range.hi ≤ de4Range.hi) ∧
      (de3Range.lo ≤ a.de3Range.lo ∧ a.de3Range.hi ≤ de3Range.hi)) :
    Jet3 box :=
  a.widen range dtRange de4Range de3Range h.1 h.2.1 h.2.2.1 h.2.2.2

@[simp] theorem value_widenAll (a : Jet3 box)
    (range dtRange de4Range de3Range : QInterval) h (t e4 e3 : ℝ) :
    (a.widenAll range dtRange de4Range de3Range h).value t e4 e3 =
      a.value t e4 e3 := rfl


@[simp] theorem value_widen (a : Jet3 box)
    (range dtRange de4Range de3Range : QInterval)
    (hRange hDtRange hDe4Range hDe3Range) (t e4 e3 : ℝ) :
    (a.widen range dtRange de4Range de3Range
      hRange hDtRange hDe4Range hDe3Range).value t e4 e3 =
        a.value t e4 e3 := rfl



/-- A real atom with supplied value enclosure and zero partials. -/
def atom (x : ℝ) (i : QInterval) (hx : i.RealContains x) : Jet3 box where
  value := fun _ _ _ => x
  dt := fun _ _ _ => 0
  de4 := fun _ _ _ => 0
  de3 := fun _ _ _ => 0
  range := i
  dtRange := LeanSuffixReflective.QInterval.point 0
  de4Range := LeanSuffixReflective.QInterval.point 0
  de3Range := LeanSuffixReflective.QInterval.point 0
  value_sound := fun _ => hx
  dt_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de4_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de3_sound := fun _ => by simpa using point_sound (0 : ℚ)
  hasDerivAt_t := fun _ => hasDerivAt_const _ _
  hasDerivAt_e4 := fun _ => hasDerivAt_const _ _
  hasDerivAt_e3 := fun _ => hasDerivAt_const _ _

/-- An exact rational constant. -/
def rational (q : ℚ) : Jet3 box := atom (q : ℝ)
  (LeanSuffixReflective.QInterval.point q) (point_sound q)

/-- The checked 160-bit dyadic enclosure of `Real.pi`. -/
def pi : Jet3 box := atom Real.pi NearOneLocalInterval.piInterval
  NearOneLocalInterval.piInterval_sound

/-- Scale coordinate. -/
def tVar (box : Box3) : Jet3 box where
  value := fun t _ _ => t
  dt := fun _ _ _ => 1
  de4 := fun _ _ _ => 0
  de3 := fun _ _ _ => 0
  range := box.t
  dtRange := LeanSuffixReflective.QInterval.point 1
  de4Range := LeanSuffixReflective.QInterval.point 0
  de3Range := LeanSuffixReflective.QInterval.point 0
  value_sound := fun h => h.1
  dt_sound := fun _ => by simpa using point_sound (1 : ℚ)
  de4_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de3_sound := fun _ => by simpa using point_sound (0 : ℚ)
  hasDerivAt_t := fun _ => hasDerivAt_id _
  hasDerivAt_e4 := fun _ => hasDerivAt_const _ _
  hasDerivAt_e3 := fun _ => hasDerivAt_const _ _

/-- Type-(iv) bracket-error coordinate. -/
def e4Var (box : Box3) : Jet3 box where
  value := fun _ e4 _ => e4
  dt := fun _ _ _ => 0
  de4 := fun _ _ _ => 1
  de3 := fun _ _ _ => 0
  range := box.e4
  dtRange := LeanSuffixReflective.QInterval.point 0
  de4Range := LeanSuffixReflective.QInterval.point 1
  de3Range := LeanSuffixReflective.QInterval.point 0
  value_sound := fun h => h.2.1
  dt_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de4_sound := fun _ => by simpa using point_sound (1 : ℚ)
  de3_sound := fun _ => by simpa using point_sound (0 : ℚ)
  hasDerivAt_t := fun _ => hasDerivAt_const _ _
  hasDerivAt_e4 := fun _ => hasDerivAt_id _
  hasDerivAt_e3 := fun _ => hasDerivAt_const _ _

/-- Type-(iii) bracket-error coordinate. -/
def e3Var (box : Box3) : Jet3 box where
  value := fun _ _ e3 => e3
  dt := fun _ _ _ => 0
  de4 := fun _ _ _ => 0
  de3 := fun _ _ _ => 1
  range := box.e3
  dtRange := LeanSuffixReflective.QInterval.point 0
  de4Range := LeanSuffixReflective.QInterval.point 0
  de3Range := LeanSuffixReflective.QInterval.point 1
  value_sound := fun h => h.2.2
  dt_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de4_sound := fun _ => by simpa using point_sound (0 : ℚ)
  de3_sound := fun _ => by simpa using point_sound (1 : ℚ)
  hasDerivAt_t := fun _ => hasDerivAt_const _ _
  hasDerivAt_e4 := fun _ => hasDerivAt_const _ _
  hasDerivAt_e3 := fun _ => hasDerivAt_id _

/-- Exact addition. -/
def add (a b : Jet3 box) : Jet3 box where
  value := fun t x y => a.value t x y + b.value t x y
  dt := fun t x y => a.dt t x y + b.dt t x y
  de4 := fun t x y => a.de4 t x y + b.de4 t x y
  de3 := fun t x y => a.de3 t x y + b.de3 t x y
  range := a.range.add b.range
  dtRange := a.dtRange.add b.dtRange
  de4Range := a.de4Range.add b.de4Range
  de3Range := a.de3Range.add b.de3Range
  value_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (a.value_sound h) (b.value_sound h)
  dt_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (a.dt_sound h) (b.dt_sound h)
  de4_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (a.de4_sound h) (b.de4_sound h)
  de3_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (a.de3_sound h) (b.de3_sound h)
  hasDerivAt_t := fun h => (a.hasDerivAt_t h).add (b.hasDerivAt_t h)
  hasDerivAt_e4 := fun h => (a.hasDerivAt_e4 h).add (b.hasDerivAt_e4 h)
  hasDerivAt_e3 := fun h => (a.hasDerivAt_e3 h).add (b.hasDerivAt_e3 h)

/-- Exact negation. -/
def neg (a : Jet3 box) : Jet3 box where
  value := fun t x y => -a.value t x y
  dt := fun t x y => -a.dt t x y
  de4 := fun t x y => -a.de4 t x y
  de3 := fun t x y => -a.de3 t x y
  range := a.range.neg
  dtRange := a.dtRange.neg
  de4Range := a.de4Range.neg
  de3Range := a.de3Range.neg
  value_sound := fun h => LeanSuffixReflective.QInterval.realContains_neg (a.value_sound h)
  dt_sound := fun h => LeanSuffixReflective.QInterval.realContains_neg (a.dt_sound h)
  de4_sound := fun h => LeanSuffixReflective.QInterval.realContains_neg (a.de4_sound h)
  de3_sound := fun h => LeanSuffixReflective.QInterval.realContains_neg (a.de3_sound h)
  hasDerivAt_t := fun h => (a.hasDerivAt_t h).neg
  hasDerivAt_e4 := fun h => (a.hasDerivAt_e4 h).neg
  hasDerivAt_e3 := fun h => (a.hasDerivAt_e3 h).neg

/-- Exact subtraction. -/
def sub (a b : Jet3 box) : Jet3 box := a.add b.neg

/-- Exact multiplication with the product rule in every coordinate. -/
def mul (a b : Jet3 box) : Jet3 box where
  value := fun t x y => a.value t x y * b.value t x y
  dt := fun t x y => a.dt t x y * b.value t x y +
    a.value t x y * b.dt t x y
  de4 := fun t x y => a.de4 t x y * b.value t x y +
    a.value t x y * b.de4 t x y
  de3 := fun t x y => a.de3 t x y * b.value t x y +
    a.value t x y * b.de3 t x y
  range := ScalarSuffixCertificate.QInterval.mul a.range b.range
  dtRange := (ScalarSuffixCertificate.QInterval.mul a.dtRange b.range).add
    (ScalarSuffixCertificate.QInterval.mul a.range b.dtRange)
  de4Range := (ScalarSuffixCertificate.QInterval.mul a.de4Range b.range).add
    (ScalarSuffixCertificate.QInterval.mul a.range b.de4Range)
  de3Range := (ScalarSuffixCertificate.QInterval.mul a.de3Range b.range).add
    (ScalarSuffixCertificate.QInterval.mul a.range b.de3Range)
  value_sound := fun h => mul_sound (a.value_sound h) (b.value_sound h)
  dt_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (mul_sound (a.dt_sound h) (b.value_sound h))
    (mul_sound (a.value_sound h) (b.dt_sound h))
  de4_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (mul_sound (a.de4_sound h) (b.value_sound h))
    (mul_sound (a.value_sound h) (b.de4_sound h))
  de3_sound := fun h => LeanSuffixReflective.QInterval.realContains_add
    (mul_sound (a.de3_sound h) (b.value_sound h))
    (mul_sound (a.value_sound h) (b.de3_sound h))
  hasDerivAt_t := fun h => (a.hasDerivAt_t h).mul (b.hasDerivAt_t h)
  hasDerivAt_e4 := fun h => (a.hasDerivAt_e4 h).mul (b.hasDerivAt_e4 h)
  hasDerivAt_e3 := fun h => (a.hasDerivAt_e3 h).mul (b.hasDerivAt_e3 h)

/-- Exact square. -/
def sq (a : Jet3 box) : Jet3 box := a.mul a

/-- Exact cube. -/
def cube (a : Jet3 box) : Jet3 box := a.sq.mul a

/-- Exact fourth power. -/
def fourth (a : Jet3 box) : Jet3 box := a.sq.sq

/-- Positive reciprocal with its actual derivative. -/
def invPos (a : Jet3 box) (ha : 0 < a.range.lo) : Jet3 box := by
  let inverse := ScalarSuffixCertificate.QInterval.recipPos a.range ha
  let factor := (ScalarSuffixCertificate.QInterval.mul inverse inverse).neg
  refine
    { value := fun t x y => (a.value t x y)⁻¹
      dt := fun t x y => -a.dt t x y / (a.value t x y) ^ 2
      de4 := fun t x y => -a.de4 t x y / (a.value t x y) ^ 2
      de3 := fun t x y => -a.de3 t x y / (a.value t x y) ^ 2
      range := inverse
      dtRange := ScalarSuffixCertificate.QInterval.mul factor a.dtRange
      de4Range := ScalarSuffixCertificate.QInterval.mul factor a.de4Range
      de3Range := ScalarSuffixCertificate.QInterval.mul factor a.de3Range
      value_sound := ?_
      dt_sound := ?_
      de4_sound := ?_
      de3_sound := ?_
      hasDerivAt_t := ?_
      hasDerivAt_e4 := ?_
      hasDerivAt_e3 := ?_ }
  · intro t e4 e3 h
    simpa only [one_div] using
      ScalarSuffixCertificate.QInterval.realContains_recipPos ha (a.value_sound h)
  · intro t e4 e3 h
    have hinv := ScalarSuffixCertificate.QInterval.realContains_recipPos ha
      (a.value_sound h)
    have hproduct := mul_sound
      (LeanSuffixReflective.QInterval.realContains_neg (mul_sound hinv hinv))
      (a.dt_sound h)
    dsimp only [factor, inverse]
    convert hproduct using 1
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  · intro t e4 e3 h
    have hinv := ScalarSuffixCertificate.QInterval.realContains_recipPos ha
      (a.value_sound h)
    have hproduct := mul_sound
      (LeanSuffixReflective.QInterval.realContains_neg (mul_sound hinv hinv))
      (a.de4_sound h)
    dsimp only [factor, inverse]
    convert hproduct using 1
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  · intro t e4 e3 h
    have hinv := ScalarSuffixCertificate.QInterval.realContains_recipPos ha
      (a.value_sound h)
    have hproduct := mul_sound
      (LeanSuffixReflective.QInterval.realContains_neg (mul_sound hinv hinv))
      (a.de3_sound h)
    dsimp only [factor, inverse]
    convert hproduct using 1
    rw [div_eq_mul_inv, ← inv_pow, pow_two]
    ring
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have haR : (0 : ℝ) < (a.range.lo : ℝ) := by exact_mod_cast ha
      exact haR.trans_le hav.1
    exact (a.hasDerivAt_t h).inv (ne_of_gt havPos)
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have haR : (0 : ℝ) < (a.range.lo : ℝ) := by exact_mod_cast ha
      exact haR.trans_le hav.1
    exact (a.hasDerivAt_e4 h).inv (ne_of_gt havPos)
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have haR : (0 : ℝ) < (a.range.lo : ℝ) := by exact_mod_cast ha
      exact haR.trans_le hav.1
    exact (a.hasDerivAt_e3 h).inv (ne_of_gt havPos)

/-- A supplied rational square-root interval.  Its two square comparisons are
all a generated certificate must check. -/
def sqrt (a : Jet3 box) (out : QInterval)
    (hout : 0 < out.lo)
    (hlo : out.lo ^ 2 ≤ a.range.lo)
    (hhi : a.range.hi ≤ out.hi ^ 2) : Jet3 box := by
  let inverse := ScalarSuffixCertificate.QInterval.recipPos out hout
  let halfInverse := ScalarSuffixCertificate.QInterval.mul
    (LeanSuffixReflective.QInterval.point (1 / 2)) inverse
  refine
    { value := fun t x y => Real.sqrt (a.value t x y)
      dt := fun t x y => (((1 / 2 : ℚ) : ℝ) *
        (Real.sqrt (a.value t x y))⁻¹) * a.dt t x y
      de4 := fun t x y => (((1 / 2 : ℚ) : ℝ) *
        (Real.sqrt (a.value t x y))⁻¹) * a.de4 t x y
      de3 := fun t x y => (((1 / 2 : ℚ) : ℝ) *
        (Real.sqrt (a.value t x y))⁻¹) * a.de3 t x y
      range := out
      dtRange := ScalarSuffixCertificate.QInterval.mul halfInverse a.dtRange
      de4Range := ScalarSuffixCertificate.QInterval.mul halfInverse a.de4Range
      de3Range := ScalarSuffixCertificate.QInterval.mul halfInverse a.de3Range
      value_sound := ?_
      dt_sound := ?_
      de4_sound := ?_
      de3_sound := ?_
      hasDerivAt_t := ?_
      hasDerivAt_e4 := ?_
      hasDerivAt_e3 := ?_ }
  · intro t e4 e3 h
    have hav := a.value_sound h
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt (i := out)
    · exact_mod_cast hout.le
    · exact (by exact_mod_cast hlo : ((out.lo : ℝ) ^ 2 ≤
        (a.range.lo : ℝ))).trans hav.1
    · exact hav.2.trans (by exact_mod_cast hhi)
  · intro t e4 e3 h
    have hsqrt : out.RealContains (Real.sqrt (a.value t e4 e3)) := by
      apply ScalarSuffixCertificate.QInterval.realContains_sqrt (i := out)
      · exact_mod_cast hout.le
      · exact (by exact_mod_cast hlo : ((out.lo : ℝ) ^ 2 ≤
          (a.range.lo : ℝ))).trans (a.value_sound h).1
      · exact (a.value_sound h).2.trans (by exact_mod_cast hhi)
    have hfactor := mul_sound (point_sound (1 / 2))
      (ScalarSuffixCertificate.QInterval.realContains_recipPos hout hsqrt)
    have hproduct := mul_sound hfactor (a.dt_sound h)
    simpa only [halfInverse, inverse, one_div] using hproduct
  · intro t e4 e3 h
    have hsqrt : out.RealContains (Real.sqrt (a.value t e4 e3)) := by
      apply ScalarSuffixCertificate.QInterval.realContains_sqrt (i := out)
      · exact_mod_cast hout.le
      · exact (by exact_mod_cast hlo : ((out.lo : ℝ) ^ 2 ≤
          (a.range.lo : ℝ))).trans (a.value_sound h).1
      · exact (a.value_sound h).2.trans (by exact_mod_cast hhi)
    have hfactor := mul_sound (point_sound (1 / 2))
      (ScalarSuffixCertificate.QInterval.realContains_recipPos hout hsqrt)
    have hproduct := mul_sound hfactor (a.de4_sound h)
    simpa only [halfInverse, inverse, one_div] using hproduct
  · intro t e4 e3 h
    have hsqrt : out.RealContains (Real.sqrt (a.value t e4 e3)) := by
      apply ScalarSuffixCertificate.QInterval.realContains_sqrt (i := out)
      · exact_mod_cast hout.le
      · exact (by exact_mod_cast hlo : ((out.lo : ℝ) ^ 2 ≤
          (a.range.lo : ℝ))).trans (a.value_sound h).1
      · exact (a.value_sound h).2.trans (by exact_mod_cast hhi)
    have hfactor := mul_sound (point_sound (1 / 2))
      (ScalarSuffixCertificate.QInterval.realContains_recipPos hout hsqrt)
    have hproduct := mul_sound hfactor (a.de3_sound h)
    simpa only [halfInverse, inverse, one_div] using hproduct
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have houtSq : (0 : ℝ) < (out.lo : ℝ) ^ 2 :=
        sq_pos_of_pos (by exact_mod_cast hout)
      exact lt_of_lt_of_le (houtSq.trans_le (by exact_mod_cast hlo)) hav.1
    convert (a.hasDerivAt_t h).sqrt (ne_of_gt havPos) using 1
    norm_num [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have houtSq : (0 : ℝ) < (out.lo : ℝ) ^ 2 :=
        sq_pos_of_pos (by exact_mod_cast hout)
      exact lt_of_lt_of_le (houtSq.trans_le (by exact_mod_cast hlo)) hav.1
    convert (a.hasDerivAt_e4 h).sqrt (ne_of_gt havPos) using 1
    norm_num [div_eq_mul_inv, mul_inv_rev]
    ring
  · intro t e4 e3 h
    have hav := a.value_sound h
    have havPos : 0 < a.value t e4 e3 := by
      have houtSq : (0 : ℝ) < (out.lo : ℝ) ^ 2 :=
        sq_pos_of_pos (by exact_mod_cast hout)
      exact lt_of_lt_of_le (houtSq.trans_le (by exact_mod_cast hlo)) hav.1
    convert (a.hasDerivAt_e3 h).sqrt (ne_of_gt havPos) using 1
    norm_num [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The first exact arctangent remainder.  The value bound is the checked
centered `-1/3` estimate; the derivative bound is the global integral estimate. -/
def atanRemainderOne (a : Jet3 box) (B : ℚ)
    (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hlo : -B ≤ a.range.lo) (hhi : a.range.hi ≤ B) : Jet3 box := by
  let valueRange : QInterval :=
    ⟨-1 / 3, -1 / 3 + B ^ 2 / 5, by
      have : 0 ≤ B ^ 2 / 5 := by positivity
      linarith⟩
  let derivativeRange : QInterval :=
    ⟨-(2 * B / 5), 2 * B / 5, by
      have : 0 ≤ 2 * B / 5 := by positivity
      linarith⟩
  refine
    { value := fun t x y => NearOneAtanRemainder.atanRemainder 1 (a.value t x y)
      dt := fun t x y => NearOneAtanRemainder.atanRemainderDerivative 1
        (a.value t x y) * a.dt t x y
      de4 := fun t x y => NearOneAtanRemainder.atanRemainderDerivative 1
        (a.value t x y) * a.de4 t x y
      de3 := fun t x y => NearOneAtanRemainder.atanRemainderDerivative 1
        (a.value t x y) * a.de3 t x y
      range := valueRange
      dtRange := ScalarSuffixCertificate.QInterval.mul derivativeRange a.dtRange
      de4Range := ScalarSuffixCertificate.QInterval.mul derivativeRange a.de4Range
      de3Range := ScalarSuffixCertificate.QInterval.mul derivativeRange a.de3Range
      value_sound := ?_
      dt_sound := ?_
      de4_sound := ?_
      de3_sound := ?_
      hasDerivAt_t := ?_
      hasDerivAt_e4 := ?_
      hasDerivAt_e3 := ?_ }
  · intro t e4 e3 h
    have hav := a.value_sound h
    have habs : |a.value t e4 e3| ≤ (B : ℝ) := by
      rw [abs_le]
      constructor
      · have hloR : (-(B : ℝ)) ≤ (a.range.lo : ℝ) := by exact_mod_cast hlo
        exact hloR.trans hav.1
      · have hhiR : (a.range.hi : ℝ) ≤ (B : ℝ) := by exact_mod_cast hhi
        exact hav.2.trans hhiR
    have hxSq : (a.value t e4 e3) ^ 2 ≤ (B : ℝ) ^ 2 := by
      simpa only [sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (a.value t e4 e3)) habs 2)
    have hsq : (a.value t e4 e3) ^ 2 ≤ 1 := by
      have hBR : (0 : ℝ) ≤ B := by exact_mod_cast hB
      have hB1R : (B : ℝ) ≤ 1 := by exact_mod_cast hB1
      nlinarith [sq_nonneg ((B : ℝ) - 1)]
    have hr := NearOneRegularizedThirdRow.atanQuotientSqRemainder_centered_bounds hsq
    rw [NearOneAtanRemainder.atanRemainder_one]
    dsimp only [valueRange, LeanSuffixReflective.QInterval.RealContains]
    push_cast
    constructor <;> nlinarith [hr.1, hr.2]
  · intro t e4 e3 h
    apply mul_sound
    · have hav := a.value_sound h
      have habs : |a.value t e4 e3| ≤ (B : ℝ) := by
        rw [abs_le]
        constructor
        · have hloR : (-(B : ℝ)) ≤ (a.range.lo : ℝ) := by exact_mod_cast hlo
          exact hloR.trans hav.1
        · have hhiR : (a.range.hi : ℝ) ≤ (B : ℝ) := by exact_mod_cast hhi
          exact hav.2.trans hhiR
      have hd := NearOneAtanRemainder.abs_atanRemainderDerivative_le 1
        (a.value t e4 e3)
      rw [abs_le] at hd
      dsimp only [derivativeRange, LeanSuffixReflective.QInterval.RealContains]
      push_cast
      norm_num at hd
      constructor <;> nlinarith
    · exact a.dt_sound h
  · intro t e4 e3 h
    apply mul_sound
    · have hav := a.value_sound h
      have habs : |a.value t e4 e3| ≤ (B : ℝ) := by
        rw [abs_le]
        constructor
        · have hloR : (-(B : ℝ)) ≤ (a.range.lo : ℝ) := by exact_mod_cast hlo
          exact hloR.trans hav.1
        · have hhiR : (a.range.hi : ℝ) ≤ (B : ℝ) := by exact_mod_cast hhi
          exact hav.2.trans hhiR
      have hd := NearOneAtanRemainder.abs_atanRemainderDerivative_le 1
        (a.value t e4 e3)
      rw [abs_le] at hd
      dsimp only [derivativeRange, LeanSuffixReflective.QInterval.RealContains]
      push_cast
      norm_num at hd
      constructor <;> nlinarith
    · exact a.de4_sound h
  · intro t e4 e3 h
    apply mul_sound
    · have hav := a.value_sound h
      have habs : |a.value t e4 e3| ≤ (B : ℝ) := by
        rw [abs_le]
        constructor
        · have hloR : (-(B : ℝ)) ≤ (a.range.lo : ℝ) := by exact_mod_cast hlo
          exact hloR.trans hav.1
        · have hhiR : (a.range.hi : ℝ) ≤ (B : ℝ) := by exact_mod_cast hhi
          exact hav.2.trans hhiR
      have hd := NearOneAtanRemainder.abs_atanRemainderDerivative_le 1
        (a.value t e4 e3)
      rw [abs_le] at hd
      dsimp only [derivativeRange, LeanSuffixReflective.QInterval.RealContains]
      push_cast
      norm_num at hd
      constructor <;> nlinarith
    · exact a.de3_sound h
  · intro t e4 e3 h
    change HasDerivAt
      (NearOneAtanRemainder.atanRemainder 1 ∘ fun x => a.value x e4 e3)
      (NearOneAtanRemainder.atanRemainderDerivative 1 (a.value t e4 e3) *
        a.dt t e4 e3) t
    exact (NearOneAtanRemainder.hasDerivAt_atanRemainder 1
      (a.value t e4 e3)).comp t (a.hasDerivAt_t h)
  · intro t e4 e3 h
    change HasDerivAt
      (NearOneAtanRemainder.atanRemainder 1 ∘ fun x => a.value t x e3)
      (NearOneAtanRemainder.atanRemainderDerivative 1 (a.value t e4 e3) *
        a.de4 t e4 e3) e4
    exact (NearOneAtanRemainder.hasDerivAt_atanRemainder 1
      (a.value t e4 e3)).comp e4 (a.hasDerivAt_e4 h)
  · intro t e4 e3 h
    change HasDerivAt
      (NearOneAtanRemainder.atanRemainder 1 ∘ fun x => a.value t e4 x)
      (NearOneAtanRemainder.atanRemainderDerivative 1 (a.value t e4 e3) *
        a.de3 t e4 e3) e3
    exact (NearOneAtanRemainder.hasDerivAt_atanRemainder 1
      (a.value t e4 e3)).comp e3 (a.hasDerivAt_e3 h)

/-- Exact source arctangent quotient assembled from the first remainder. -/
def atanQuotient (a : Jet3 box) (B : ℚ)
    (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hlo : -B ≤ a.range.lo) (hhi : a.range.hi ≤ B) : Jet3 box :=
  (rational 1).add (a.sq.mul (a.atanRemainderOne B hB hB1 hlo hhi))

@[simp] theorem value_atom (x : ℝ) i h (t e4 e3 : ℝ) :
    (atom (box := box) x i h).value t e4 e3 = x := rfl
@[simp] theorem value_rational (q : ℚ) (t e4 e3 : ℝ) :
    (rational (box := box) q).value t e4 e3 = (q : ℝ) := rfl
@[simp] theorem value_pi (t e4 e3 : ℝ) :
    (pi (box := box)).value t e4 e3 = Real.pi := rfl
@[simp] theorem value_add (a b : Jet3 box) (t x y : ℝ) :
    (a.add b).value t x y = a.value t x y + b.value t x y := rfl
@[simp] theorem value_neg (a : Jet3 box) (t x y : ℝ) :
    a.neg.value t x y = -a.value t x y := rfl
@[simp] theorem value_sub (a b : Jet3 box) (t x y : ℝ) :
    (a.sub b).value t x y = a.value t x y - b.value t x y := rfl
@[simp] theorem value_mul (a b : Jet3 box) (t x y : ℝ) :
    (a.mul b).value t x y = a.value t x y * b.value t x y := rfl
@[simp] theorem value_sq (a : Jet3 box) (t x y : ℝ) :
    a.sq.value t x y = (a.value t x y) ^ 2 := by simp [sq, pow_two]
@[simp] theorem value_cube (a : Jet3 box) (t x y : ℝ) :
    a.cube.value t x y = (a.value t x y) ^ 3 := by simp [cube]; ring
@[simp] theorem value_fourth (a : Jet3 box) (t x y : ℝ) :
    a.fourth.value t x y = (a.value t x y) ^ 4 := by
  simp [fourth]
  ring
@[simp] theorem value_invPos (a : Jet3 box) h (t x y : ℝ) :
    (a.invPos h).value t x y = 1 / a.value t x y := by
  simp [invPos]
@[simp] theorem value_sqrt (a : Jet3 box) out hp hlo hhi (t x y : ℝ) :
    (a.sqrt out hp hlo hhi).value t x y = Real.sqrt (a.value t x y) := by
  simp [sqrt]
@[simp] theorem value_atanRemainderOne (a : Jet3 box) B hB hB1 hlo hhi
    (t x y : ℝ) :
    (a.atanRemainderOne B hB hB1 hlo hhi).value t x y =
      NearOneAtanRemainder.atanRemainder 1 (a.value t x y) := rfl
@[simp] theorem value_atanQuotient (a : Jet3 box) B hB hB1 hlo hhi
    (t x y : ℝ) :
    (a.atanQuotient B hB hB1 hlo hhi).value t x y =
      NearOneAnalyticSystem.atanQuotient (a.value t x y) := by
  rw [NearOneRegularizedThirdRow.atanQuotient_eq_one_add_sq_mul,
    ← NearOneAtanRemainder.atanRemainder_one]
  simp [atanQuotient]

end Jet3

private theorem interval_of_uIcc {i : QInterval} {a b x : ℝ}
    (ha : i.RealContains a) (hb : i.RealContains b) (hx : x ∈ uIcc a b) :
    i.RealContains x := by
  rcases Set.mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  · exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩

/-- Exact centered first-order enclosure, justified by three actual scalar
mean-value applications. -/
def centeredRange {wholeBox centerBox : Box3}
    (whole : Jet3 wholeBox) (center : Jet3 centerBox)
    (tDisplacement e4Displacement e3Displacement : QInterval) : QInterval :=
  ((center.range.add
    (ScalarSuffixCertificate.QInterval.mul whole.dtRange tDisplacement)).add
    (ScalarSuffixCertificate.QInterval.mul whole.de4Range e4Displacement)).add
    (ScalarSuffixCertificate.QInterval.mul whole.de3Range e3Displacement)

/-- Soundness of `centeredRange`; the equality premise only identifies the two
independently certified copies of the same source expression. -/
theorem centeredRange_sound {wholeBox centerBox : Box3}
    (whole : Jet3 wholeBox) (center : Jet3 centerBox)
    (t0 e40 e30 t e4 e3 : ℝ)
    (tDisplacement e4Displacement e3Displacement : QInterval)
    (hwhole0 : wholeBox.Contains t0 e40 e30)
    (hwhole : wholeBox.Contains t e4 e3)
    (hcenter : centerBox.Contains t0 e40 e30)
    (hsame : ∀ t e4 e3, center.value t e4 e3 = whole.value t e4 e3)
    (htd : tDisplacement.RealContains (t - t0))
    (h4d : e4Displacement.RealContains (e4 - e40))
    (h3d : e3Displacement.RealContains (e3 - e30)) :
    (centeredRange whole center tDisplacement e4Displacement e3Displacement).RealContains
      (whole.value t e4 e3) := by
  have hbase : center.range.RealContains (whole.value t0 e40 e30) := by
    rw [← hsame]
    exact center.value_sound hcenter
  have ht : (center.range.add
      (ScalarSuffixCertificate.QInterval.mul whole.dtRange tDisplacement)).RealContains
      (whole.value t e40 e30) := by
    apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
      (fun x => whole.value x e40 e30) (fun x => whole.dt x e40 e30)
      center.range whole.dtRange tDisplacement
    · intro x hx
      apply whole.hasDerivAt_t
      exact ⟨interval_of_uIcc hwhole0.1 hwhole.1 hx, hwhole0.2⟩
    · exact hbase
    · intro x hx
      apply whole.dt_sound
      exact ⟨interval_of_uIcc hwhole0.1 hwhole.1 hx, hwhole0.2⟩
    · exact htd
  have h4 : ((center.range.add
      (ScalarSuffixCertificate.QInterval.mul whole.dtRange tDisplacement)).add
      (ScalarSuffixCertificate.QInterval.mul whole.de4Range e4Displacement)).RealContains
      (whole.value t e4 e30) := by
    apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
      (fun x => whole.value t x e30) (fun x => whole.de4 t x e30)
      (center.range.add
        (ScalarSuffixCertificate.QInterval.mul whole.dtRange tDisplacement))
      whole.de4Range e4Displacement
    · intro x hx
      apply whole.hasDerivAt_e4
      exact ⟨hwhole.1, interval_of_uIcc hwhole0.2.1 hwhole.2.1 hx, hwhole0.2.2⟩
    · exact ht
    · intro x hx
      apply whole.de4_sound
      exact ⟨hwhole.1, interval_of_uIcc hwhole0.2.1 hwhole.2.1 hx, hwhole0.2.2⟩
    · exact h4d
  apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun x => whole.value t e4 x) (fun x => whole.de3 t e4 x)
    ((center.range.add
      (ScalarSuffixCertificate.QInterval.mul whole.dtRange tDisplacement)).add
      (ScalarSuffixCertificate.QInterval.mul whole.de4Range e4Displacement))
    whole.de3Range e3Displacement
  · intro x hx
    apply whole.hasDerivAt_e3
    exact ⟨hwhole.1, hwhole.2.1, interval_of_uIcc hwhole0.2.2 hwhole.2.2 hx⟩
  · exact h4
  · intro x hx
    apply whole.de3_sound
    exact ⟨hwhole.1, hwhole.2.1, interval_of_uIcc hwhole0.2.2 hwhole.2.2 hx⟩
  · exact h3d

end

end NearOneScalarInterval
