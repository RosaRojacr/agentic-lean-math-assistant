/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenTaylorMajorantBase

namespace NearOneRegularizedThirdRow
open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
noncomputable section
set_option maxRecDepth 10000
namespace NearOneRescaledFirstCell
section FrozenPolynomial
namespace FrozenTaylorMajorant

open TaylorMajorant

private abbrev TM (p : ℝ[X]) := TaylorMajorant p

def algAraw {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgA Z) :=
  one.add (TaylorMajorant.X.mul Zb)

def algA {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgA Z) := algAraw Zb

def algRraw {A : ℝ[X]} (Ab : TM A) : TM (frozenAlgR A) := by
  simpa [frozenAlgR] using (nat 2).add (TaylorMajorant.X.mul Ab)

def algR {A : ℝ[X]} (Ab : TM A) : TM (frozenAlgR A) := algRraw Ab

def algEraw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgE Z A B) := by
  simpa [frozenAlgE] using
    (((nat 6).mul Ab).sub ((nat 2).mul Zb)).add (TaylorMajorant.X.mul Bb)

def algE {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgE Z A B) := algEraw Zb Ab Bb

def algDoubleEraw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgDoubleE Z A B) := by
  simpa [frozenAlgDoubleE, mul_assoc] using
    (((nat 12).mul Ab).sub ((nat 4).mul Zb)).add
      (((nat 2).mul TaylorMajorant.X).mul Bb)

def algDoubleE {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgDoubleE Z A B) := algDoubleEraw Zb Ab Bb

def algDoubleBraw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgDoubleB Z A B) := by
  simpa [frozenAlgDoubleB] using
    ((nat 2).mul (algR Ab)).add
      (TaylorMajorant.X.mul (algDoubleE Zb Ab Bb))

def algDoubleB {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgDoubleB Z A B) := algDoubleBraw Zb Ab Bb

def algFoldRaw {Z : ℝ[X]} (Zb : TM Z) (pb : TM (Polynomial.C π)) :
    TM (frozenAlgFoldNumerator Z π) :=
  let A := algA Zb
  ((Zb.mul oneSubX2).mul
    (one.sub ((TaylorMajorant.X.pow 2).mul A))).sub
    ((pb.mul A).mul oneAddX2)
def algFold {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgFoldNumerator Z π) :=
  algFoldRaw Zb piC

def algCosineRaw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgCosineNumerator Z A B) := by
  let R := algR Ab
  let E := algDoubleE Zb Ab Bb
  let t0 := ((nat 4).mul E).mul R |>.sub ((nat 8).mul Zb)
  let t1 := TaylorMajorant.X.mul ((E.pow 2).sub ((nat 4).mul (Zb.pow 2)))
  let t4 := (TaylorMajorant.X.pow 4).mul
    ((((nat 4).mul E).mul R).neg.add (((nat 8).mul (R.pow 4)).mul Zb))
  let t5 := (TaylorMajorant.X.pow 5).mul
    ((((E.pow 2).neg.add (((nat 8).mul E).mul (R.pow 3) |>.mul Zb)).sub
      (((nat 8).mul E).mul R |>.mul Zb)).add
      (((nat 4).mul (R.pow 4)).mul (Zb.pow 2)))
  let t6 := (TaylorMajorant.X.pow 6).mul
    (((((nat 2).mul (E.pow 2)).mul (R.pow 2)).mul Zb).sub
      (((nat 2).mul (E.pow 2)).mul Zb) |>.add
      (((nat 4).mul E).mul (R.pow 3) |>.mul (Zb.pow 2)) |>.sub
      (((nat 4).mul E).mul R |>.mul (Zb.pow 2)))
  let t7 := (TaylorMajorant.X.pow 7).mul
    ((((E.pow 2).mul (R.pow 2)).mul (Zb.pow 2)).sub
      ((E.pow 2).mul (Zb.pow 2)))
  simpa [frozenAlgCosineNumerator, R, E, t0, t1, t4, t5, t6, t7] using
    (((((t0.add t1).add t4).add t5).add t6).add t7)

def algCosine {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgCosineNumerator Z A B) := algCosineRaw Zb Ab Bb

def algKRaw {A : ℝ[X]} (Ab : TM A) : TM (frozenAlgK A) := by
  let R := algR Ab
  simpa [frozenAlgK, R] using
    (((nat 2).mul (R.pow 2)).sub (nat 4)).add
      ((TaylorMajorant.X.pow 2).mul ((R.pow 4).sub ((nat 4).mul (R.pow 2)))) |>.add
      (((nat 2).mul (TaylorMajorant.X.pow 4)).mul ((R.pow 2).sub (R.pow 4))) |>.add
      ((TaylorMajorant.X.pow 6).mul (R.pow 4))

def algK {A : ℝ[X]} (Ab : TM A) : TM (frozenAlgK A) := algKRaw Ab

def algURaw {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgU Z) := by
  simpa [frozenAlgU] using
    (oneSubX2.pow 2).mul
      (one.add ((TaylorMajorant.X.pow 2).mul ((algA Zb).pow 2)))

def algU {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgU Z) := algURaw Zb

def algWRaw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgW Z A B) := by
  simpa [frozenAlgW] using
    (one.add ((TaylorMajorant.X.pow 2).mul ((algR Ab).pow 2))).pow 2 |>.mul
      ((nat 4).add ((TaylorMajorant.X.pow 2).mul ((algDoubleB Zb Ab Bb).pow 2)))

def algW {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgW Z A B) := algWRaw Zb Ab Bb

def algAreaXRaw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaX Z A B) := by
  let R := algR Ab
  let DB := algDoubleB Zb Ab Bb
  simpa [frozenAlgAreaX, R, DB] using
    ((nat 3).add ((TaylorMajorant.X.pow 2).mul (R.pow 2))).mul
      ((nat 2).sub (((TaylorMajorant.X.pow 2).mul R).mul DB))

def algAreaX {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaX Z A B) := algAreaXRaw Zb Ab Bb

def algAreaZRaw {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgAreaZ Z) := by
  simpa [frozenAlgAreaZ] using
    oneSubX2.mul (one.sub ((TaylorMajorant.X.pow 2).mul (algA Zb)))

def algAreaZ {Z : ℝ[X]} (Zb : TM Z) : TM (frozenAlgAreaZ Z) := algAreaZRaw Zb

def algAreaLRaw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaL Z A B) := by
  simpa [frozenAlgAreaL] using
    (one.add ((TaylorMajorant.X.pow 2).mul ((algA Zb).pow 2))).mul
      ((nat 4).add ((TaylorMajorant.X.pow 2).mul ((algDoubleB Zb Ab Bb).pow 2))) |>.mul
      (algK Ab)

def algAreaL {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaL Z A B) := algAreaLRaw Zb Ab Bb

def algAreaNumeratorRaw {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaNumerator Z A B π) := by
  let E := algDoubleE Zb Ab Bb
  let U := algU Zb
  let W := algW Zb Ab Bb
  let AX := algAreaX Zb Ab Bb
  let AZ := algAreaZ Zb
  let AL := algAreaL Zb Ab Bb
  simpa [frozenAlgAreaNumerator, E, U, W, AX, AZ, AL] using
    (piC.mul AL).add ((((E.sub ((nat 4).mul Zb)).mul U).mul W)) |>.add
      ((((nat 2).mul E).mul U).mul AX) |>.sub
      (((nat 4).mul Zb).mul
        ((nat 4).add ((TaylorMajorant.X.pow 2).mul ((algDoubleB Zb Ab Bb).pow 2))) |>.mul AZ)

def algAreaNumerator {Z A B : ℝ[X]} (Zb : TM Z) (Ab : TM A) (Bb : TM B) :
    TM (frozenAlgAreaNumerator Z A B π) := algAreaNumeratorRaw Zb Ab Bb

def algQPrimeRaw {Z A : ℝ[X]} (Zb : TM Z) (Ab : TM A) :
    TM (frozenAlgQPrime Z A π) := by
  simpa [frozenAlgQPrime] using
    ((nat 4).mul Ab).sub
      ((rational (1 / 3 : ℝ)).mul (((nat 2).mul Zb).add piC))

def algQPrime {Z A : ℝ[X]} (Zb : TM Z) (Ab : TM A) :
    TM (frozenAlgQPrime Z A π) := algQPrimeRaw Zb Ab

def algThirdNumeratorRaw {Z A B : ℝ[X]}
    (Zb : TM Z) (Ab : TM A) (Bb : TM B) : TM (frozenAlgThirdNumerator Z A B π) := by
  let area := algAreaNumerator Zb Ab Bb
  let cosine := algCosine Zb Ab Bb
  let fold := algFold Zb
  let qprime := algQPrime Zb Ab
  simpa [frozenAlgThirdNumerator, area, cosine, fold, qprime] using
    area.sub ((nat 2).mul cosine) |>.add ((nat 16).mul fold) |>.add
      (TaylorMajorant.X.mul
        ((qprime.mul cosine).sub
          (((rational (8 / 3 : ℝ)).mul Zb).mul fold)))

/-- Compositionally certified twice-normalized H3 majorant. -/
def h3 (q : Fin 3 → ℝ) (hq : InEndpointBox q) : TM (frozenH3PathPolynomial q) := by
  let N : TM (frozenH3PathNumerator q) := by
    simpa [frozenH3PathNumerator] using
      algThirdNumeratorRaw (z q hq) (a q hq) (b q hq)
  simpa [frozenH3PathPolynomial] using N.divXTwo

end FrozenTaylorMajorant
end FrozenPolynomial
end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
