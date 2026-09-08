/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalCoordinates

/-!
# Cancellation-preserving generated third row

This module transcribes the fixed fourth-order jet used by the scale-local atlas.
The low algebraic source row is built from exact `Jet4` operations, so its two
vanishing coefficients and its divided value are checked by Lean rather than by
the external symbolic producer.
-/


set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace NearOneLocalGeneratedThird

open NearOneAnalyticSystem NearOneRegularizedThirdRow
open NearOneLocalJet NearOneLocalCoordinates
noncomputable section

private def j (s q : ℝ) : Jet4 s := Jet4.const s q
private def scale {s : ℝ} (q : ℝ) (a : Jet4 s) : Jet4 s := (j s q).mul a


/-- Fixed generated jet for the algebraic third-row numerator before its first
exact division by `s²`.  The grouping is the source grouping in `model.py`, not
an unproved imported polynomial expansion. -/
def algebraicThirdJet (s p u v w : ℝ) : Jet4 s :=
  let t := Jet4.id s
  let z := zJet s p u
  let a := aJet s p v
  let b := bJet s p w
  let A := (j s 1).add (t.mul z)
  let R := (j s 2).add (t.mul a)
  let e := (scale 6 a).sub (scale 2 z) |>.add (t.mul b)
  let E := scale 2 e
  let B := (scale 2 R).add (scale 2 (t.mul e))
  let K :=
    (scale 2 R.sq).sub (j s 4) |>.add
      (t.pow 2 |>.mul ((R.pow 4).sub (scale 4 R.sq))) |>.add
      (scale 2 (t.pow 4 |>.mul (R.sq.sub (R.pow 4)))) |>.add
      (t.pow 6 |>.mul (R.pow 4))
  let U := ((j s 1).sub (t.pow 2)).pow 2 |>.mul
    ((j s 1).add (t.pow 2 |>.mul A.sq))
  let WW := ((j s 1).add (t.pow 2 |>.mul R.sq)).pow 2 |>.mul
    ((j s 4).add (t.pow 2 |>.mul B.sq))
  let X := ((j s 3).add (t.pow 2 |>.mul R.sq)).mul
    ((j s 2).sub (t.pow 2 |>.mul (R.mul B)))
  let Z := ((j s 1).sub (t.pow 2)).mul
    ((j s 1).sub (t.pow 2 |>.mul A))
  let L := ((j s 1).add (t.pow 2 |>.mul A.sq)).mul
    ((j s 4).add (t.pow 2 |>.mul B.sq)) |>.mul K
  let fn := z.mul ((j s 1).sub (t.pow 2)) |>.mul
      ((j s 1).sub (t.pow 2 |>.mul A)) |>.sub
    (scale p (A.mul ((j s 1).add (t.pow 2))))
  let cn :=
    (scale 4 (E.mul R)).sub (scale 8 z) |>.add
      (t.mul (E.sq.sub (scale 4 z.sq))) |>.add
      (t.pow 4 |>.mul ((scale 8 ((R.pow 4).mul z)).sub (scale 4 (E.mul R)))) |>.add
      (t.pow 5 |>.mul
        ((E.sq.neg).add (scale 8 (E.mul (R.pow 3) |>.mul z)) |>.sub
          (scale 8 (E.mul R |>.mul z)) |>.add
          (scale 4 ((R.pow 4).mul z.sq)))) |>.add
      (t.pow 6 |>.mul
        ((scale 2 (E.sq.mul R.sq |>.mul z)).sub (scale 2 (E.sq.mul z)) |>.add
          (scale 4 (E.mul (R.pow 3) |>.mul z.sq)) |>.sub
          (scale 4 (E.mul R |>.mul z.sq)))) |>.add
      (t.pow 7 |>.mul ((E.sq.mul R.sq |>.mul z.sq).sub (E.sq.mul z.sq)))
  let an :=
    (scale p L).add ((E.sub (scale 4 z)).mul U |>.mul WW) |>.add
      (scale 2 (E.mul U |>.mul X)) |>.sub
      (scale 4 (z.mul ((j s 4).add (t.pow 2 |>.mul B.sq)) |>.mul Z))
  an.sub (scale 2 cn) |>.add (scale 16 fn) |>.add
    (t.mul
      (((scale 4 a).sub (scale (2 / 3 : ℝ) z) |>.sub (j s (p / 3))).mul cn |>.sub
        (scale (8 / 3 : ℝ) (z.mul fn))))


/-- The generated algebraic jet denotes the genuine source polynomial
numerator at the physical atlas coordinates. -/
theorem algebraicThirdJet_value (s p u v w : ℝ) :
    (algebraicThirdJet s p u v w).value =
      (NearOneNormalizedFlow.thirdRowNumerator
        (physicalZ s p u) (physicalA s p v) (physicalB s p w) p).eval s := by
  simp [algebraicThirdJet, physicalZ, physicalA, physicalB,
    NearOneNormalizedFlow.thirdRowNumerator,
    NearOneNormalizedFlow.areaNumerator, NearOneNormalizedFlow.areaL,
    NearOneNormalizedFlow.areaZ, NearOneNormalizedFlow.areaX,
    NearOneNormalizedFlow.W, NearOneNormalizedFlow.U, NearOneNormalizedFlow.K,
    NearOneNormalizedFlow.cosineNumerator, NearOneNormalizedFlow.foldNumerator,
    NearOneNormalizedFlow.qPrime, NearOneNormalizedFlow.B,
    NearOneNormalizedFlow.E, NearOneNormalizedFlow.R, NearOneNormalizedFlow.A,
    j, scale]
  ring

/-- The constant coefficient cancellation is replayed in the generated jet. -/
theorem algebraicThirdJet_c0 (s p u v w : ℝ) :
    (algebraicThirdJet s p u v w).c0 = 0 := by
  simp [algebraicThirdJet, zJet, aJet, bJet, j, scale, Jet4.pow, Jet4.sq,
    Jet4.sub, Jet4.neg, Jet4.add, Jet4.mul]
  ring

/-- The linear coefficient cancellation is replayed in the generated jet. -/
theorem algebraicThirdJet_c1 (s p u v w : ℝ) :
    (algebraicThirdJet s p u v w).c1 = 0 := by
  simp [algebraicThirdJet, zJet, aJet, bJet, j, scale, Jet4.pow, Jet4.sq,
    Jet4.sub, Jet4.neg, Jet4.add, Jet4.mul]
  ring

/-- First exact source division: the generated polynomial jet denotes
`H3hatPolynomial` at every nonzero scale. -/
def algebraicThirdDivided (s p u v w : ℝ) (hs : s ≠ 0) : Jet2 s :=
  Jet2.divideSq (algebraicThirdJet s p u v w)
    (algebraicThirdJet_c0 s p u v w) (algebraicThirdJet_c1 s p u v w) hs

/-- The first divided generated value is the existing pole-free algebraic row. -/
theorem algebraicThirdDivided_value (s p u v w : ℝ) (hs : s ≠ 0) :
    (algebraicThirdDivided s p u v w hs).value =
      NearOneNormalizedFlow.H3hatPolynomial s
        (physicalZ s p u) (physicalA s p v) (physicalB s p w) p := by
  rw [show (algebraicThirdDivided s p u v w hs).value =
      (algebraicThirdJet s p u v w).value / s ^ 2 by rfl,
    algebraicThirdJet_value]
  have h := congrArg (Polynomial.eval s)
    (NearOneNormalizedFlow.X_sq_mul_normalizedThirdRow
      (physicalZ s p u) (physicalA s p v) (physicalB s p w) p)
  change s ^ 2 *
      NearOneNormalizedFlow.H3hatPolynomial s
        (physicalZ s p u) (physicalA s p v) (physicalB s p w) p =
    (NearOneNormalizedFlow.thirdRowNumerator
      (physicalZ s p u) (physicalA s p v) (physicalB s p w) p).eval s at h
  apply (div_eq_iff (pow_ne_zero 2 hs)).2
  nlinarith [h]

end

end NearOneLocalGeneratedThird
