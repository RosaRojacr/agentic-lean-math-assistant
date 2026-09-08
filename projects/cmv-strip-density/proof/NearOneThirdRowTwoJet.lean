/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneShearCoordinates
import NearOneTwoJet

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real
open Filter NearOneTwoJet
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

private def physicalZ (q : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 0

private def physicalA (q : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 1

private def physicalB (q : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 2

private theorem physicalZ_eq (q : Fin 3 → ℝ) (s : ℝ) :
    physicalZ q s = Real.pi + s * Real.pi ^ 2 + s ^ 2 * q 0 := by
  simp [physicalZ, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem physicalA_eq (q : Fin 3 → ℝ) (s : ℝ) :
    physicalA q s = 5 * Real.pi / 12 +
      s * ((43 * Real.pi ^ 2 + 1056) / 144) +
      s ^ 2 * (5 * q 0 / 12 + q 1) := by
  simp [physicalA, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem physicalB_eq (q : Fin 3 → ℝ) (s : ℝ) :
    physicalB q s = -44 + 19 * Real.pi ^ 2 / 24 +
      s * (Real.pi * (295 * Real.pi ^ 2 - 14256) / 216) +
      s ^ 2 * ((109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * q 0 +
        (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * q 1 + q 2) := by
  simp [physicalB, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private def physicalZJet (q : Fin 3 → ℝ) :
    HasTwoJet (physicalZ q) Real.pi (Real.pi ^ 2) (q 0) := by
  refine ⟨fun _ => q 0, continuousAt_const, rfl, ?_⟩
  filter_upwards
  intro s
  rw [physicalZ_eq]

private def physicalAJet (q : Fin 3 → ℝ) :
    HasTwoJet (physicalA q) (5 * Real.pi / 12)
      ((43 * Real.pi ^ 2 + 1056) / 144) (5 * q 0 / 12 + q 1) := by
  refine ⟨fun _ => 5 * q 0 / 12 + q 1, continuousAt_const, rfl, ?_⟩
  filter_upwards
  intro s
  rw [physicalA_eq]

private def physicalBJet (q : Fin 3 → ℝ) :
    HasTwoJet (physicalB q) (-44 + 19 * Real.pi ^ 2 / 24)
      (Real.pi * (295 * Real.pi ^ 2 - 14256) / 216)
      ((109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * q 0 +
        (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * q 1 + q 2) := by
  refine ⟨fun _ => (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * q 0 +
      (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * q 1 + q 2,
    continuousAt_const, rfl, ?_⟩
  filter_upwards
  intro s
  rw [physicalB_eq]

/-- The two-jet of `atanQuotient` on a zero-constant input uses only the
continuous square remainder. -/
private def atanQuotientJet {x : ℝ → ℝ} {x₁ x₂ : ℝ}
    (hx : HasTwoJet x 0 x₁ x₂) :
    HasTwoJet (fun s => atanQuotient (x s)) 1 0 (-(x₁ ^ 2) / 3) := by
  have h := hx.one_add_sq_mul_continuous
    continuous_atanQuotientSqRemainder.continuousAt
  have heq : (fun s => atanQuotient (x s)) =ᶠ[𝓝 0]
      fun s => 1 + x s ^ 2 * atanQuotientSqRemainder (x s) := by
    filter_upwards
    intro s
    exact atanQuotient_eq_one_add_sq_mul (x s)
  have hc := h.congr heq
  convert hc using 1 <;> norm_num [atanQuotientSqRemainder_zero] <;> ring

private def arctanJet {x : ℝ → ℝ} {x₁ x₂ : ℝ}
    (hx : HasTwoJet x 0 x₁ x₂) :
    HasTwoJet (fun s => Real.arctan (x s)) 0 x₁ x₂ := by
  have h := hx.mul (atanQuotientJet hx)
  have heq : (fun s => Real.arctan (x s)) =ᶠ[𝓝 0]
      fun s => x s * atanQuotient (x s) := by
    filter_upwards
    intro s
    exact (mul_atanQuotient (x s)).symm
  have hc := h.congr heq
  convert hc using 1 <;> ring

macro "poly_jet" : tactic =>
  `(tactic|
    repeat'
      first
      | apply SomePolynomialTwoJet.add
      | apply SomePolynomialTwoJet.sub
      | apply SomePolynomialTwoJet.neg
      | apply SomePolynomialTwoJet.mul
      | apply SomePolynomialTwoJet.sq
      | apply SomePolynomialTwoJet.pow
      | (apply SomePolynomialTwoJet.C; assumption))

set_option maxHeartbeats 0 in
-- The high-degree polynomial expansion exceeds Lean's default command budget.
private def normalizedThirdRowPolynomialJet (q : Fin 3 → ℝ) :
    SomePolynomialTwoJet (fun s =>
      normalizedThirdRow (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  have hz := physicalZJet q
  have ha := physicalAJet q
  have hb := physicalBJet q
  unfold normalizedThirdRow thirdRowNumerator areaNumerator areaL areaZ areaX
    W U K cosineNumerator foldNumerator qPrime B E R A
  apply SomePolynomialTwoJet.divX
  apply SomePolynomialTwoJet.divX
  poly_jet
  all_goals exact SomePolynomialTwoJet.const _

private def H3hatPolynomialJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      H3hatPolynomial s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  let hp := normalizedThirdRowPolynomialJet q
  exact ⟨hp.P₀.coeff 0, hp.P₀.coeff 1 + hp.P₁.coeff 0,
    hp.P₀.coeff 2 + hp.P₁.coeff 1 + hp.P₂.coeff 0,
    hp.diagonalEval⟩

macro "scalar_jet" : tactic =>
  `(tactic|
    repeat'
      first
      | apply SomeHasTwoJet.add
      | apply SomeHasTwoJet.sub
      | apply SomeHasTwoJet.neg
      | apply SomeHasTwoJet.mul
      | apply SomeHasTwoJet.sq
      | apply SomeHasTwoJet.cube
      | apply SomeHasTwoJet.pow
      | assumption
      | exact SomeHasTwoJet.id
      | exact SomeHasTwoJet.const _)

private def physicalZSomeJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (physicalZ q) :=
  ⟨Real.pi, Real.pi ^ 2, q 0, physicalZJet q⟩

private def physicalASomeJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (physicalA q) :=
  ⟨5 * Real.pi / 12, (43 * Real.pi ^ 2 + 1056) / 144,
    5 * q 0 / 12 + q 1, physicalAJet q⟩

private def physicalBSomeJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (physicalB q) :=
  ⟨-44 + 19 * Real.pi ^ 2 / 24,
    Real.pi * (295 * Real.pi ^ 2 - 14256) / 216,
    (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * q 0 +
      (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * q 1 + q 2,
    physicalBJet q⟩

private def aCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => aCoord s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let h := one.add (hs.mul hz)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold aCoord
    rfl⟩

private def rCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => rCoord s (physicalA q s)) := by
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let ha := physicalASomeJet q
  let h := two.add (hs.mul ha)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold rCoord
    rfl⟩

private def eCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      eCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) := by
  let two := SomeHasTwoJet.const 2
  let six := SomeHasTwoJet.const 6
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let ha := physicalASomeJet q
  let hb := physicalBSomeJet q
  let h := ((six.mul ha).sub (two.mul hz)).add (hs.mul hb)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold eCoord
    rfl⟩

private def yCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => yCoord s (physicalZ q s)) := by
  let hs := SomeHasTwoJet.id
  let hA := aCoordPathJet q
  let h := hs.mul hA
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold yCoord
    rfl⟩

private def wCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => wCoord s (physicalA q s)) := by
  let hs := SomeHasTwoJet.id
  let hR := rCoordPathJet q
  let h := hs.mul hR
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold wCoord
    rfl⟩

private def vCoordPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) := by
  let hs := SomeHasTwoJet.id
  let hR := rCoordPathJet q
  let hE := eCoordPathJet q
  let h := hs.mul (hR.add (hs.mul hE))
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold vCoord
    rfl⟩

private def halfCosJet {x : ℝ → ℝ} (hx : SomeHasTwoJet x) :
    SomeHasTwoJet (fun s => halfCos (x s)) := by
  let one := SomeHasTwoJet.const 1
  let xx := hx.sq
  have hden : (one.add xx).c₀ ≠ 0 := by
    change 1 + hx.c₀ ^ 2 ≠ 0
    positivity
  let h := (one.sub xx).div (one.add xx) hden
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold halfCos
    rfl⟩

private def densityPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => density s (physicalZ q s)) := by
  let hs := halfCosJet SomeHasTwoJet.id
  let hy := halfCosJet (yCoordPathJet q)
  have hy0 : hy.c₀ = 1 := by
    rw [← hy.jet.value]
    simp [hy, halfCos, yCoord, aCoord, physicalZ, tangentCenteredPoint,
      exactCuspPoint, exactCuspTangent, exactCuspShear, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  let h := hs.div hy (by rw [hy0]; norm_num)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold density
    rfl⟩

private def densityCubeQuotientPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => densityCubeQuotient s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hy := yCoordPathJet q
  let num := (two.mul hz).mul (two.add (hs.mul hz))
  let den := (one.add hs.sq).mul (one.sub hy.sq)
  have hden : den.c₀ ≠ 0 := by
    rw [← den.jet.value]
    simp [den, one, two, hs, hz, hy, yCoord, aCoord, physicalZ,
      tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
      exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  let h := num.div den hden
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold densityCubeQuotient
    rfl⟩

private def typeFourAngleIncrementBar2PathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      typeFourAngleIncrementBar2 s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hA := aCoordPathJet q
  let hy := yCoordPathJet q
  let hd := one.add (hs.mul hy)
  have hd0 : hd.c₀ ≠ 0 := by
    rw [← hd.jet.value]
    simp [hd, one, hs, hy, yCoord, aCoord]
  let harg := (hs.sq.mul hz).div hd hd0
  have hargCont : ContinuousAt
      (fun s => s ^ 2 * physicalZ q s /
        (1 + s * yCoord s (physicalZ q s))) 0 := by
    simpa [harg, hd, one, hs, hz, hy] using harg.jet.continuousAt
  have hrem : ContinuousAt
      (fun s => atanQuotientSqRemainder
        (s ^ 2 * physicalZ q s /
          (1 + s * yCoord s (physicalZ q s)))) 0 :=
    continuous_atanQuotientSqRemainder.continuousAt.comp hargCont
  let G : ℝ → ℝ := fun s =>
    physicalZ q s ^ 2 /
      (1 + s * yCoord s (physicalZ q s)) ^ 2 *
      atanQuotientSqRemainder
        (s ^ 2 * physicalZ q s /
          (1 + s * yCoord s (physicalZ q s)))
  have hG : ContinuousAt G 0 := by
    let hbase := hz.sq.div hd.sq (pow_ne_zero 2 hd0)
    convert hbase.jet.continuousAt.mul hrem using 1
    funext s
    rfl
  have hremJet : HasTwoJet (fun s => s ^ 2 * G s) 0 0 (G 0) :=
    HasTwoJet.sq_mul_continuous hG
  have hremEq : (fun s =>
      s ^ 2 * physicalZ q s ^ 2 /
        (1 + s * yCoord s (physicalZ q s)) ^ 2 *
          atanQuotientSqRemainder
            (s ^ 2 * physicalZ q s /
              (1 + s * yCoord s (physicalZ q s)))) =ᶠ[𝓝 0]
      fun s => s ^ 2 * G s := by
    filter_upwards
    intro s
    dsimp only [G]
    ring
  let hremSome : SomeHasTwoJet (fun s =>
      s ^ 2 * physicalZ q s ^ 2 /
        (1 + s * yCoord s (physicalZ q s)) ^ 2 *
          atanQuotientSqRemainder
            (s ^ 2 * physicalZ q s /
              (1 + s * yCoord s (physicalZ q s)))) :=
    ⟨0, 0, G 0, hremJet.congr hremEq⟩
  let lead := (two.mul hz).div hd hd0
  let h := lead.mul (hremSome.sub hA)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeFourAngleIncrementBar2
    rfl⟩

private def typeFourAngleBar2PathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => typeFourAngleBar2 s (physicalZ q s)) := by
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hdensity := densityPathJet q
  let hcube := densityCubeQuotientPathJet q
  let hatan : SomeHasTwoJet (fun s => atanQuotient s) :=
    ⟨1, 0, -(1 : ℝ) ^ 2 / 3, atanQuotientJet HasTwoJet.id⟩
  let hinc := typeFourAngleIncrementBar2PathJet q
  let h := (((two.mul hcube).mul hatan).add (hdensity.mul hinc)).add
    (((two.mul hs).mul hz).mul hcube)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeFourAngleBar2
    rfl⟩

private def typeThreeAngleIncrementBar2PathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      typeThreeAngleIncrementBar2 s (physicalZ q s) (physicalA q s)
        (physicalB q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let he := eCoordPathJet q
  let hr := rCoordPathJet q
  let hw := wCoordPathJet q
  let hv := vCoordPathJet q
  let hd := one.add (hw.mul hv)
  have hd0 : hd.c₀ ≠ 0 := by
    rw [← hd.jet.value]
    simp [hd, one, hw, hv, wCoord, vCoord, rCoord, eCoord]
  let harg := (hs.sq.mul he).div hd hd0
  have hargCont : ContinuousAt (fun s =>
      s ^ 2 *
        eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) /
          (1 + wCoord s (physicalA q s) *
            vCoord s (physicalZ q s) (physicalA q s)
              (physicalB q s))) 0 := by
    simpa [harg, hd, one, hs, he, hw, hv] using harg.jet.continuousAt
  have hrem : ContinuousAt (fun s => atanQuotientSqRemainder
      (s ^ 2 *
        eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) /
          (1 + wCoord s (physicalA q s) *
            vCoord s (physicalZ q s) (physicalA q s)
              (physicalB q s)))) 0 :=
    continuous_atanQuotientSqRemainder.continuousAt.comp hargCont
  let G : ℝ → ℝ := fun s =>
    eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) ^ 2 /
      (1 + wCoord s (physicalA q s) *
        vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) ^ 2 *
      atanQuotientSqRemainder
        (s ^ 2 *
          eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) /
            (1 + wCoord s (physicalA q s) *
              vCoord s (physicalZ q s) (physicalA q s)
                (physicalB q s)))
  have hG : ContinuousAt G 0 := by
    let hbase := he.sq.div hd.sq (pow_ne_zero 2 hd0)
    convert hbase.jet.continuousAt.mul hrem using 1
    funext s
    rfl
  have hremJet : HasTwoJet (fun s => s ^ 2 * G s) 0 0 (G 0) :=
    HasTwoJet.sq_mul_continuous hG
  have hremEq : (fun s =>
      s ^ 2 *
        eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) ^ 2 /
          (1 + wCoord s (physicalA q s) *
            vCoord s (physicalZ q s) (physicalA q s)
              (physicalB q s)) ^ 2 *
          atanQuotientSqRemainder
            (s ^ 2 *
              eCoord s (physicalZ q s) (physicalA q s)
                (physicalB q s) /
                (1 + wCoord s (physicalA q s) *
                  vCoord s (physicalZ q s) (physicalA q s)
                    (physicalB q s)))) =ᶠ[𝓝 0]
      fun s => s ^ 2 * G s := by
    filter_upwards
    intro s
    dsimp only [G]
    ring
  let hremSome : SomeHasTwoJet (fun s =>
      s ^ 2 *
        eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) ^ 2 /
          (1 + wCoord s (physicalA q s) *
            vCoord s (physicalZ q s) (physicalA q s)
              (physicalB q s)) ^ 2 *
          atanQuotientSqRemainder
            (s ^ 2 *
              eCoord s (physicalZ q s) (physicalA q s)
                (physicalB q s) /
                (1 + wCoord s (physicalA q s) *
                  vCoord s (physicalZ q s) (physicalA q s)
                    (physicalB q s)))) :=
    ⟨0, 0, G 0, hremJet.congr hremEq⟩
  let lead := (two.mul he).div hd hd0
  let rr := hr.mul (hr.add (hs.mul he))
  let h := lead.mul (hremSome.sub rr)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeThreeAngleIncrementBar2
    rfl⟩

private def typeThreeAngleBar2PathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      typeThreeAngleBar2 s (physicalZ q s) (physicalA q s)
        (physicalB q s)) := by
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let he := eCoordPathJet q
  let hr := rCoordPathJet q
  let hw := wCoordPathJet q
  let hdensity := densityPathJet q
  let hcube := densityCubeQuotientPathJet q
  let hatan : SomeHasTwoJet
      (fun s => atanQuotient (wCoord s (physicalA q s))) :=
    ⟨1, 0, -(hw.c₁ ^ 2) / 3, atanQuotientJet (by
      have hw0 : hw.c₀ = 0 := by
        rw [← hw.jet.value]
        simp [hw, wCoord, rCoord]
      convert hw.jet using 1
      exact hw0.symm)⟩
  let hinc := typeThreeAngleIncrementBar2PathJet q
  let h := ((((two.mul hcube).mul hr).mul hatan).add
    (hdensity.mul hinc)).add (((two.mul hs).mul he).mul hcube)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeThreeAngleBar2
    rfl⟩

private def typeFourAngleIncrementPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      typeFourAngleIncrement s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hy := yCoordPathJet q
  let hd := one.add (hs.mul hy)
  have hd0 : hd.c₀ ≠ 0 := by
    rw [← hd.jet.value]
    simp [hd, one, hs, hy, yCoord, aCoord]
  let harg := (hs.sq.mul hz).div hd hd0
  have harg0 : harg.c₀ = 0 := by
    rw [← harg.jet.value]
    simp [harg, hs]
  let hargJet : HasTwoJet _ 0 harg.c₁ harg.c₂ := by
    convert harg.jet using 1
    exact harg0.symm
  let hatan : SomeHasTwoJet (fun s => atanQuotient
      (s ^ 2 * physicalZ q s /
        (1 + s * yCoord s (physicalZ q s)))) :=
    ⟨1, 0, -(harg.c₁ ^ 2) / 3, atanQuotientJet hargJet⟩
  let h := ((two.mul hz).div hd hd0).mul hatan
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeFourAngleIncrement
    rfl⟩

private def typeFourAngleBarPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => typeFourAngleBar s (physicalZ q s)) := by
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hcube := densityCubeQuotientPathJet q
  let hdensity := densityPathJet q
  let harctan : SomeHasTwoJet (fun s => Real.arctan s) :=
    ⟨0, 1, 0, arctanJet HasTwoJet.id⟩
  let hinc := typeFourAngleIncrementPathJet q
  let h := (((two.mul hs).mul hcube).mul harctan).add
    (hdensity.mul hinc)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeFourAngleBar
    rfl⟩

private def typeFourSineProductBarPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      typeFourSineProductBar s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let four := SomeHasTwoJet.const 4
  let hs := SomeHasTwoJet.id
  let hA := aCoordPathJet q
  let hy := yCoordPathJet q
  let hd := (one.add hs.sq).mul (one.add hy.sq)
  have hd0 : hd.c₀ ≠ 0 := by
    rw [← hd.jet.value]
    positivity
  let h := (four.mul hA).div hd hd0
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold typeFourSineProductBar
    rfl⟩

private def foldDenominatorPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => foldDenominator s (physicalZ q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hy := yCoordPathJet q
  let h := (two.mul (one.add hs.sq).sq).mul (one.add hy.sq)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold foldDenominator
    rfl⟩

private def areaDenominatorPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      areaDenominator s (physicalZ q s) (physicalA q s)
        (physicalB q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hw := wCoordPathJet q
  let hy := yCoordPathJet q
  let hv := vCoordPathJet q
  let h := (((two.mul (one.add hs.sq).sq).mul
    (one.add hw.sq).sq).mul (one.add hy.sq)).mul
      (one.add hv.sq)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold areaDenominator
    rfl⟩

private def KEvalPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      (NearOneNormalizedFlow.K (physicalA q s)).eval s) := by
  let two := SomeHasTwoJet.const 2
  let four := SomeHasTwoJet.const 4
  let hs := SomeHasTwoJet.id
  let ha := physicalASomeJet q
  let r := two.add (hs.mul ha)
  let r2 := r.sq
  let r4 := r2.sq
  let s2 := hs.sq
  let s4 := s2.sq
  let s6 := s4.mul s2
  let h := ((two.mul r2).sub four).add <|
    (s2.mul (r4.sub (four.mul r2))).add <|
    ((two.mul s4).mul (r2.sub r4)).add <|
    s6.mul r4
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    simp [NearOneNormalizedFlow.K, NearOneNormalizedFlow.R]
    ring⟩
private def areaPiWeightPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s => areaPiWeight s (physicalA q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let hs := SomeHasTwoJet.id
  let hw := wCoordPathJet q
  let hK := KEvalPathJet q
  let hd := (one.add hs.sq).sq.mul
    (one.add hw.sq).sq
  have hd0 : hd.c₀ ≠ 0 := by
    rw [← hd.jet.value]
    positivity
  let h := (two.mul hK).div hd hd0
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold areaPiWeight
    rfl⟩

private def foldAngleCorrectionBarPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      foldAngleCorrectionBar s (physicalZ q s)) := by
  let hden := foldDenominatorPathJet q
  let hsine := typeFourSineProductBarPathJet q
  let hangle := typeFourAngleBarPathJet q
  let h := (hden.neg.mul hsine).mul hangle
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold foldAngleCorrectionBar
    rfl⟩

private def areaAngleCorrectionBarPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      areaAngleCorrectionBar s (physicalZ q s) (physicalA q s)
        (physicalB q s)) := by
  let one := SomeHasTwoJet.const 1
  let two := SomeHasTwoJet.const 2
  let four := SomeHasTwoJet.const 4
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hw := wCoordPathJet q
  let hhalfS := halfCosJet hs
  let hhalfW := halfCosJet hw
  let hthree := typeThreeAngleBar2PathJet q
  let hfour := typeFourAngleBar2PathJet q
  let hpi := areaPiWeightPathJet q
  let hden := areaDenominatorPathJet q
  let term1 := (two.mul hhalfS.sq).mul hthree
  let term2 := (one.add hhalfW).sq.mul hfour
  let term3 := (four.mul hz).mul hpi
  let h := hden.mul ((term1.sub term2).add term3)
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold areaAngleCorrectionBar
    rfl⟩

private def regularizedThirdRowPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      regularizedThirdRow s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  let two := SomeHasTwoJet.const 2
  let three := SomeHasTwoJet.const 3
  let four := SomeHasTwoJet.const 4
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  let hpoly := H3hatPolynomialJet q
  let harea := areaAngleCorrectionBarPathJet q
  let hfold := foldAngleCorrectionBarPathJet q
  have hthree0 : three.c₀ ≠ 0 := by
    rw [← three.jet.value]
    norm_num
  unfold regularizedThirdRow
  exact (hpoly.add harea).add
    ((four.sub (((two.mul hz).mul hs).div three hthree0)).mul hfold)


private theorem polynomial_coeff_one (p : ℝ[X]) :
    p.coeff 1 = p.derivative.eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  norm_num

private theorem polynomial_coeff_two (p : ℝ[X]) :
    p.coeff 2 = p.derivative.derivative.eval 0 / 2 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative]
  norm_num

private theorem polynomial_coeff_three (p : ℝ[X]) :
    p.coeff 3 = p.derivative.derivative.derivative.eval 0 / 6 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative,
    coeff_derivative]
  norm_num
  ring

private theorem polynomial_coeff_four (p : ℝ[X]) :
    p.coeff 4 =
      p.derivative.derivative.derivative.derivative.eval 0 / 24 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative,
    coeff_derivative, coeff_derivative]
  norm_num
  ring

private def normalizedThirdRowCoeffZero (z a b pi : ℝ) : ℝ :=
  -(4 / 3) *
    (-576 * a ^ 3 + 42 * a ^ 2 * pi + 432 * a ^ 2 * z +
      36 * a * b - 28 * a * pi * z - 92 * a * z ^ 2 +
      4 * b * pi - 16 * b * z + pi * z ^ 2 - 48 * pi +
      6 * z ^ 3 + 180 * z)

private def normalizedThirdRowCoeffOne (z a b pi : ℝ) : ℝ :=
  (8 / 3) *
    (84 * a ^ 2 * b - 144 * a ^ 2 - 7 * a * b * pi -
      38 * a * b * z + 252 * a * pi - 120 * a * z -
      3 * b ^ 2 + 2 * b * pi * z + 4 * b * z ^ 2 -
      41 * pi * z + 14 * z ^ 2)

private def normalizedThirdRowCoeffTwo (z a b pi : ℝ) : ℝ :=
  -(4 / 3) *
    (-1116 * a ^ 3 - 1350 * a ^ 2 * pi + 2364 * a ^ 2 * z -
      12 * a * b ^ 2 + 120 * a * b + 480 * a * pi * z -
      1224 * a * z ^ 2 - 1008 * a + b ^ 2 * pi +
      2 * b ^ 2 * z - 48 * b * pi - 62 * pi * z ^ 2 +
      24 * pi + 202 * z ^ 3 + 852 * z)

private theorem normalizedThirdRow_coeff_zero (z a b pi : ℝ) :
    (normalizedThirdRow z a b pi).coeff 0 =
      normalizedThirdRowCoeffZero z a b pi := by
  simp only [normalizedThirdRow, coeff_divX]
  rw [polynomial_coeff_two]
  simp [thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A,
    normalizedThirdRowCoeffZero, derivative_pow]
  ring

private theorem normalizedThirdRow_coeff_one (z a b pi : ℝ) :
    (normalizedThirdRow z a b pi).coeff 1 =
      normalizedThirdRowCoeffOne z a b pi := by
  simp only [normalizedThirdRow, coeff_divX]
  rw [polynomial_coeff_three]
  simp [thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A,
    normalizedThirdRowCoeffOne, derivative_pow]
  ring

private theorem normalizedThirdRow_coeff_two (z a b pi : ℝ) :
    (normalizedThirdRow z a b pi).coeff 2 =
      normalizedThirdRowCoeffTwo z a b pi := by
  simp only [normalizedThirdRow, coeff_divX]
  rw [polynomial_coeff_four]
  simp [thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A,
    normalizedThirdRowCoeffTwo, derivative_pow]
  ring

private theorem polynomial_eval_eq_first_two_coeffs
    (P : ℝ[X]) (s : ℝ) :
    P.eval s = P.coeff 0 + s * P.coeff 1 +
      s ^ 2 * P.divX.divX.eval s := by
  have hfirst := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add P)
  have hsecond := congrArg (Polynomial.eval s)
    (Polynomial.X_mul_divX_add P.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C] at hfirst hsecond
  simp only [coeff_divX] at hsecond
  rw [← hfirst, ← hsecond]
  ring

private def normalizedThirdRowCoeffZeroPathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      normalizedThirdRowCoeffZero (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  let hz := physicalZSomeJet q
  let ha := physicalASomeJet q
  let hb := physicalBSomeJet q
  let inner :=
    (SomeHasTwoJet.smul (-576) ha.cube).add <|
    (SomeHasTwoJet.smul (42 * Real.pi) ha.sq).add <|
    (SomeHasTwoJet.smul 432 (ha.sq.mul hz)).add <|
    (SomeHasTwoJet.smul 36 (ha.mul hb)).add <|
    (SomeHasTwoJet.smul (-28 * Real.pi) (ha.mul hz)).add <|
    (SomeHasTwoJet.smul (-92) (ha.mul hz.sq)).add <|
    (SomeHasTwoJet.smul (4 * Real.pi) hb).add <|
    (SomeHasTwoJet.smul (-16) (hb.mul hz)).add <|
    (SomeHasTwoJet.smul Real.pi hz.sq).add <|
    (SomeHasTwoJet.const (-48 * Real.pi)).add <|
    (SomeHasTwoJet.smul 6 hz.cube).add <|
    SomeHasTwoJet.smul 180 hz
  let h := SomeHasTwoJet.smul (-(4 / 3)) inner
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold normalizedThirdRowCoeffZero
    ring⟩

private def normalizedThirdRowCoeffOnePathJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      normalizedThirdRowCoeffOne (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  let hz := physicalZSomeJet q
  let ha := physicalASomeJet q
  let hb := physicalBSomeJet q
  let inner :=
    (SomeHasTwoJet.smul 84 (ha.sq.mul hb)).add <|
    (SomeHasTwoJet.smul (-144) ha.sq).add <|
    (SomeHasTwoJet.smul (-7 * Real.pi) (ha.mul hb)).add <|
    (SomeHasTwoJet.smul (-38) ((ha.mul hb).mul hz)).add <|
    (SomeHasTwoJet.smul (252 * Real.pi) ha).add <|
    (SomeHasTwoJet.smul (-120) (ha.mul hz)).add <|
    (SomeHasTwoJet.smul (-3) hb.sq).add <|
    (SomeHasTwoJet.smul (2 * Real.pi) (hb.mul hz)).add <|
    (SomeHasTwoJet.smul 4 (hb.mul hz.sq)).add <|
    (SomeHasTwoJet.smul (-41 * Real.pi) hz).add <|
    SomeHasTwoJet.smul 14 hz.sq
  let h := SomeHasTwoJet.smul (8 / 3) inner
  exact ⟨h.c₀, h.c₁, h.c₂, h.jet.congr <| by
    filter_upwards with s
    unfold normalizedThirdRowCoeffOne
    ring⟩

private def normalizedThirdRowTailPath (q : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  (normalizedThirdRow (physicalZ q s) (physicalA q s)
    (physicalB q s) Real.pi).divX.divX.eval s

private theorem continuousAt_normalizedThirdRowTailPath
    (q : Fin 3 → ℝ) :
    ContinuousAt (normalizedThirdRowTailPath q) 0 := by
  let hp := normalizedThirdRowPolynomialJet q
  change ContinuousAt (fun s =>
    (normalizedThirdRow (physicalZ q s) (physicalA q s)
      (physicalB q s) Real.pi).divX.divX.eval s) 0
  simpa only [Function.id_def] using
    hp.jet.continuousPolynomialAt.divX.divX.continuousAt_eval continuousAt_id

private structure JointPolynomialAt {α : Type*} [TopologicalSpace α]
    (p : α → ℝ[X]) (x : α) where
  bound : ℕ
  continuousAt_coeff : ∀ n, ContinuousAt (fun y => (p y).coeff n) x
  coeff_eq_zero_of_bound_lt : ∀ y n, bound < n → (p y).coeff n = 0

namespace JointPolynomialAt

variable {α : Type*} [TopologicalSpace α] {p r : α → ℝ[X]} {x : α}

private theorem continuousAt_finset_sum'
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {F : α → ι → ℝ}
    (hF : ∀ i ∈ S, ContinuousAt (fun y => F y i) x) :
    ContinuousAt (fun y => ∑ i ∈ S, F y i) x := by
  induction S using Finset.induction_on with
  | empty => exact continuousAt_const
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i S)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
def const (P : ℝ[X]) : JointPolynomialAt (fun _ : α => P) x where

  bound := P.natDegree
  continuousAt_coeff := fun _ => continuousAt_const
  coeff_eq_zero_of_bound_lt := fun _ _ hn =>
    P.coeff_eq_zero_of_natDegree_lt hn

def C {f : α → ℝ} (hf : ContinuousAt f x) :
    JointPolynomialAt (fun y => Polynomial.C (f y)) x where
  bound := 0
  continuousAt_coeff := fun n => by
    simp only [coeff_C]
    split <;> fun_prop
  coeff_eq_zero_of_bound_lt := fun _ n hn => by
    simp only [coeff_C]
    split
    · omega
    · rfl

def add (hp : JointPolynomialAt p x) (hr : JointPolynomialAt r x) :
    JointPolynomialAt (fun y => p y + r y) x where
  bound := max hp.bound hr.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_add]
    exact (hp.continuousAt_coeff n).add (hr.continuousAt_coeff n)
  coeff_eq_zero_of_bound_lt := fun y n hn => by
    rw [coeff_add, hp.coeff_eq_zero_of_bound_lt y n
      (lt_of_le_of_lt (le_max_left _ _) hn),
      hr.coeff_eq_zero_of_bound_lt y n
        (lt_of_le_of_lt (le_max_right _ _) hn), add_zero]

def neg (hp : JointPolynomialAt p x) :
    JointPolynomialAt (fun y => -p y) x where
  bound := hp.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_neg]
    exact (hp.continuousAt_coeff n).neg
  coeff_eq_zero_of_bound_lt := fun y n hn => by
    rw [coeff_neg, hp.coeff_eq_zero_of_bound_lt y n hn, neg_zero]

def sub (hp : JointPolynomialAt p x) (hr : JointPolynomialAt r x) :
    JointPolynomialAt (fun y => p y - r y) x :=
  hp.add hr.neg

def mul (hp : JointPolynomialAt p x) (hr : JointPolynomialAt r x) :
    JointPolynomialAt (fun y => p y * r y) x where
  bound := hp.bound + hr.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_mul]
    apply continuousAt_finset_sum'
    intro ij hij
    exact (hp.continuousAt_coeff ij.1).mul
      (hr.continuousAt_coeff ij.2)
  coeff_eq_zero_of_bound_lt := fun y n hn => by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum : ij.1 + ij.2 = n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hi : hp.bound < ij.1
    · rw [hp.coeff_eq_zero_of_bound_lt y ij.1 hi, zero_mul]
    · have hj : hr.bound < ij.2 := by omega
      rw [hr.coeff_eq_zero_of_bound_lt y ij.2 hj, mul_zero]

def pow (hp : JointPolynomialAt p x) :
    ∀ n : ℕ, JointPolynomialAt (fun y => p y ^ n) x
  | 0 => by simpa using JointPolynomialAt.const (1 : ℝ[X])
  | n + 1 => by
      simpa [pow_succ] using (hp.pow n).mul hp

def divX (hp : JointPolynomialAt p x) :
    JointPolynomialAt (fun y => (p y).divX) x where
  bound := hp.bound
  continuousAt_coeff := fun n => by
    simp only [coeff_divX]
    exact hp.continuousAt_coeff (n + 1)
  coeff_eq_zero_of_bound_lt := fun y n hn => by
    simp only [coeff_divX]
    exact hp.coeff_eq_zero_of_bound_lt y (n + 1) (by omega)

theorem continuousAt_eval (hp : JointPolynomialAt p x)
    {z : α → ℝ} (hz : ContinuousAt z x) :
    ContinuousAt (fun y => (p y).eval (z y)) x := by
  let S := Finset.range (hp.bound + 1)
  have hsum : ContinuousAt
      (fun y => ∑ n ∈ S, (p y).coeff n * z y ^ n) x := by
    apply continuousAt_finset_sum'
    intro n hn
    exact (hp.continuousAt_coeff n).mul (hz.pow n)
  apply hsum.congr_of_eventuallyEq
  filter_upwards
  intro y
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset (s₁ := (p y).support) (s₂ := S) ?_ ?_
  · intro n hn
    rw [Finset.mem_range]
    by_contra hnot
    have hgt : hp.bound < n := by omega
    exact (Polynomial.mem_support_iff.mp hn)
      (hp.coeff_eq_zero_of_bound_lt y n hgt)
  · intro n hnS hnSupp
    have hz : (p y).coeff n = 0 := by
      simpa only [Polynomial.mem_support_iff, not_ne_iff] using hnSupp
    rw [hz, zero_mul]

end JointPolynomialAt

macro "joint_poly" : tactic =>
  `(tactic|
    repeat'
      first
      | apply JointPolynomialAt.add
      | apply JointPolynomialAt.sub
      | apply JointPolynomialAt.neg
      | apply JointPolynomialAt.divX
      | apply JointPolynomialAt.mul
      | apply JointPolynomialAt.pow
      | apply JointPolynomialAt.C
      | exact JointPolynomialAt.const _)

set_option maxHeartbeats 0 in
-- The coefficientwise polynomial proof exceeds the default elaboration budget.
/-- Evaluation of the normalized third-row polynomial is continuous under
continuous variation of all three physical coordinates. -/
theorem continuousAt_H3hatPolynomial_comp
    {α : Type*} [TopologicalSpace α] (s pi : ℝ)
    {Z Af Bf : α → ℝ} {x : α}
    (hZ : ContinuousAt Z x) (hA : ContinuousAt Af x)
    (hB : ContinuousAt Bf x) :
    ContinuousAt
      (fun y => H3hatPolynomial s (Z y) (Af y) (Bf y) pi) x := by
  let hp : JointPolynomialAt
      (fun y => normalizedThirdRow (Z y) (Af y) (Bf y) pi) x := by
    unfold normalizedThirdRow thirdRowNumerator areaNumerator areaL areaZ
      areaX W U K cosineNumerator foldNumerator qPrime B E R A
    joint_poly <;> (first | assumption | fun_prop (disch := assumption))
  unfold H3hatPolynomial
  exact hp.continuousAt_eval continuousAt_const

set_option maxHeartbeats 0 in
@[fun_prop] private theorem continuousAt_physicalZ_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      physicalZ p.2 p.1) (0, q) := by
  unfold physicalZ tangentCenteredPoint
  fun_prop

@[fun_prop] private theorem continuousAt_physicalA_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      physicalA p.2 p.1) (0, q) := by
  unfold physicalA tangentCenteredPoint
  fun_prop

@[fun_prop] private theorem continuousAt_physicalB_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      physicalB p.2 p.1) (0, q) := by
  unfold physicalB tangentCenteredPoint
  fun_prop

set_option maxHeartbeats 0 in
private theorem continuousAt_normalizedThirdRowTailPath_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      normalizedThirdRowTailPath p.2 p.1) (0, q) := by
  let hp : JointPolynomialAt (fun p : ℝ × (Fin 3 → ℝ) =>
      (normalizedThirdRow (physicalZ p.2 p.1) (physicalA p.2 p.1)
        (physicalB p.2 p.1) Real.pi).divX.divX) (0, q) := by
    unfold normalizedThirdRow thirdRowNumerator areaNumerator areaL areaZ
      areaX W U K cosineNumerator foldNumerator qPrime B E R A
    joint_poly <;> fun_prop
  exact hp.continuousAt_eval (by fun_prop)
private theorem normalizedThirdRowTailPath_zero (q : Fin 3 → ℝ) :
    normalizedThirdRowTailPath q 0 =
      normalizedThirdRowCoeffTwo Real.pi (5 * Real.pi / 12)
        (-44 + 19 * Real.pi ^ 2 / 24) Real.pi := by
  rw [normalizedThirdRowTailPath, ← coeff_zero_eq_eval_zero]
  simp only [coeff_divX]
  rw [normalizedThirdRow_coeff_two]
  simp [physicalZ, physicalA, physicalB, tangentCenteredPoint,
    exactCuspPoint, exactCuspTangent, exactCuspShear, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]

private def H3hatPolynomialFactoredJet (q : Fin 3 → ℝ) :
    SomeHasTwoJet (fun s =>
      H3hatPolynomial s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) := by
  let h₀ := normalizedThirdRowCoeffZeroPathJet q
  let h₁ := normalizedThirdRowCoeffOnePathJet q
  let htail : SomeHasTwoJet (fun s =>
      s ^ 2 * normalizedThirdRowTailPath q s) :=
    ⟨0, 0, normalizedThirdRowTailPath q 0,
      HasTwoJet.sq_mul_continuous
        (continuousAt_normalizedThirdRowTailPath q)⟩
  let h := (h₀.add (SomeHasTwoJet.id.mul h₁)).add htail
  refine ⟨h.c₀, h.c₁, h.c₂, h.jet.congr ?_⟩
  filter_upwards
  intro s
  rw [H3hatPolynomial, polynomial_eval_eq_first_two_coeffs,
    normalizedThirdRow_coeff_zero, normalizedThirdRow_coeff_one]
  rfl


private theorem hasDerivAt_zero_of_hasTwoJet
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ} (h : HasTwoJet f a₀ a₁ a₂) :
    HasDerivAt f a₁ 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hc : Tendsto (fun _ : ℝ => a₁)
      (𝓝[≠] (0 : ℝ)) (𝓝 a₁) := tendsto_const_nhds
  have hs : Tendsto (fun s : ℝ => s)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hr : Tendsto h.remainder
      (𝓝[≠] (0 : ℝ)) (𝓝 (h.remainder 0)) :=
    h.continuousAt_remainder.mono_left inf_le_left
  have ht : Tendsto (fun s => a₁ + s * h.remainder s)
      (𝓝[≠] (0 : ℝ)) (𝓝 a₁) := by
    simpa using hc.add (hs.mul hr)
  apply ht.congr'
  filter_upwards [h.eventually_eq_remainder.filter_mono inf_le_left,
    self_mem_nhdsWithin] with s hs hne
  have hsne : s ≠ 0 := by simpa using hne
  simp only [zero_add, h.value]
  rw [hs]
  change a₁ + s * h.remainder s =
    s⁻¹ * ((a₀ + s * a₁ + s ^ 2 * h.remainder s) - a₀)
  field_simp [hsne]
  ring
private theorem c₂_eq_of_hasTwoJet_same
    {f : ℝ → ℝ} {a₀ a₁ a₂ b₂ : ℝ}
    (h : HasTwoJet f a₀ a₁ a₂) (k : HasTwoJet f a₀ a₁ b₂) :
    a₂ = b₂ := by
  have heq : h.remainder =ᶠ[𝓝[>] (0 : ℝ)] k.remainder := by
    filter_upwards [
      h.eventually_eq_remainder.filter_mono nhdsWithin_le_nhds,
      k.eventually_eq_remainder.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with s hs hk hpos
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
    apply mul_left_cancel₀ hs2
    linarith
  have hh : Tendsto h.remainder (𝓝[>] (0 : ℝ))
      (𝓝 (h.remainder 0)) :=
    h.continuousAt_remainder.mono_left nhdsWithin_le_nhds
  have hk : Tendsto k.remainder (𝓝[>] (0 : ℝ))
      (𝓝 (k.remainder 0)) :=
    k.continuousAt_remainder.mono_left nhdsWithin_le_nhds
  have hz : h.remainder 0 = k.remainder 0 :=
    tendsto_nhds_unique hh (hk.congr' heq.symm)
  exact h.remainder_zero.symm.trans (hz.trans k.remainder_zero)

private structure JointJetData (f : (Fin 3 → ℝ) → ℝ → ℝ) where
  jet : ∀ q, SomeHasTwoJet (f q)
  continuousAt_function : ∀ q,
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => f p.2 p.1) (0, q)
  continuousAt_c₀ : ∀ q, ContinuousAt (fun r => (jet r).c₀) q
  continuousAt_c₁ : ∀ q, ContinuousAt (fun r => (jet r).c₁) q
  continuousAt_c₂ : ∀ q, ContinuousAt (fun r => (jet r).c₂) q
  continuousAt_remainder : ∀ q,
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      (jet p.2).jet.remainder p.1) (0, q)
  eventually_eq_joint : ∀ q, ∀ᶠ p : ℝ × (Fin 3 → ℝ) in 𝓝 (0, q),
    f p.2 p.1 = (jet p.2).c₀ + p.1 * (jet p.2).c₁ +
      p.1 ^ 2 * (jet p.2).jet.remainder p.1

namespace JointJetData

variable {f g : (Fin 3 → ℝ) → ℝ → ℝ}

def const (c : ℝ) : JointJetData (fun _ _ => c) where
  jet := fun _ => SomeHasTwoJet.const c
  continuousAt_function := fun _ => continuousAt_const
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun _ => continuousAt_const
  continuousAt_remainder := fun _ => continuousAt_const
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change c = c + p.1 * 0 + p.1 ^ 2 * 0
    ring

def id : JointJetData (fun _ s => s) where
  jet := fun _ => SomeHasTwoJet.id
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_function := fun _ => continuousAt_fst
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun _ => continuousAt_const
  continuousAt_remainder := fun _ => continuousAt_const
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change p.1 = 0 + p.1 * 1 + p.1 ^ 2 * 0
    ring

def add (hf : JointJetData f) (hg : JointJetData g) :
    JointJetData (fun q s => f q s + g q s) where
  jet := fun q => (hf.jet q).add (hg.jet q)
  continuousAt_function := fun q =>
    (hf.continuousAt_function q).add (hg.continuousAt_function q)
  continuousAt_c₀ := fun q =>
    (hf.continuousAt_c₀ q).add (hg.continuousAt_c₀ q)
  continuousAt_c₁ := fun q =>
    (hf.continuousAt_c₁ q).add (hg.continuousAt_c₁ q)
  continuousAt_c₂ := fun q =>
    (hf.continuousAt_c₂ q).add (hg.continuousAt_c₂ q)
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p =>
      (hf.jet p.2).jet.remainder p.1 +
        (hg.jet p.2).jet.remainder p.1) (0, q)
    exact (hf.continuousAt_remainder q).add
      (hg.continuousAt_remainder q)
  eventually_eq_joint := fun q => by
    filter_upwards [hf.eventually_eq_joint q, hg.eventually_eq_joint q]
      with p hfp hgp
    change f p.2 p.1 + g p.2 p.1 =
      (hf.jet p.2).c₀ + (hg.jet p.2).c₀ +
      p.1 * ((hf.jet p.2).c₁ + (hg.jet p.2).c₁) +
      p.1 ^ 2 * ((hf.jet p.2).jet.remainder p.1 +
        (hg.jet p.2).jet.remainder p.1)
    rw [hfp, hgp]
    ring

def neg (hf : JointJetData f) :
    JointJetData (fun q s => -f q s) where
  jet := fun q => (hf.jet q).neg
  continuousAt_function := fun q => (hf.continuousAt_function q).neg
  continuousAt_c₀ := fun q => (hf.continuousAt_c₀ q).neg
  continuousAt_c₁ := fun q => (hf.continuousAt_c₁ q).neg
  continuousAt_c₂ := fun q => (hf.continuousAt_c₂ q).neg
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p =>
      -(hf.jet p.2).jet.remainder p.1) (0, q)
    exact (hf.continuousAt_remainder q).neg
  eventually_eq_joint := fun q => by
    filter_upwards [hf.eventually_eq_joint q] with p hp
    change -f p.2 p.1 = -(hf.jet p.2).c₀ +
      p.1 * (-(hf.jet p.2).c₁) +
      p.1 ^ 2 * (-(hf.jet p.2).jet.remainder p.1)
    rw [hp]
    ring

def sub (hf : JointJetData f) (hg : JointJetData g) :
    JointJetData (fun q s => f q s - g q s) :=
  hf.add hg.neg

def mul (hf : JointJetData f) (hg : JointJetData g) :
    JointJetData (fun q s => f q s * g q s) where
  jet := fun q => (hf.jet q).mul (hg.jet q)
  continuousAt_function := fun q =>
    (hf.continuousAt_function q).mul (hg.continuousAt_function q)
  continuousAt_c₀ := fun q =>
    (hf.continuousAt_c₀ q).mul (hg.continuousAt_c₀ q)
  continuousAt_c₁ := fun q =>
    ((hf.continuousAt_c₀ q).mul (hg.continuousAt_c₁ q)).add
      ((hf.continuousAt_c₁ q).mul (hg.continuousAt_c₀ q))
  continuousAt_c₂ := fun q =>
    (((hf.continuousAt_c₀ q).mul (hg.continuousAt_c₂ q)).add
      ((hf.continuousAt_c₁ q).mul (hg.continuousAt_c₁ q))).add
        ((hf.continuousAt_c₂ q).mul (hg.continuousAt_c₀ q))
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p =>
      (hf.jet p.2).c₀ * (hg.jet p.2).jet.remainder p.1 +
      (hf.jet p.2).c₁ * (hg.jet p.2).c₁ +
      p.1 * (hf.jet p.2).c₁ * (hg.jet p.2).jet.remainder p.1 +
      (hg.jet p.2).c₀ * (hf.jet p.2).jet.remainder p.1 +
      p.1 * (hg.jet p.2).c₁ * (hf.jet p.2).jet.remainder p.1 +
      p.1 ^ 2 * (hf.jet p.2).jet.remainder p.1 *
        (hg.jet p.2).jet.remainder p.1) (0, q)
    have hf0 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hf.jet p.2).c₀) (0, q) :=
      (hf.continuousAt_c₀ q).snd' (x := (0 : ℝ))
    have hf1 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hf.jet p.2).c₁) (0, q) :=
      (hf.continuousAt_c₁ q).snd' (x := (0 : ℝ))
    have hg0 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hg.jet p.2).c₀) (0, q) :=
      (hg.continuousAt_c₀ q).snd' (x := (0 : ℝ))
    have hg1 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hg.jet p.2).c₁) (0, q) :=
      (hg.continuousAt_c₁ q).snd' (x := (0 : ℝ))
    have hfr := hf.continuousAt_remainder q
    have hgr := hg.continuousAt_remainder q
    exact (((((hf0.mul hgr).add (hf1.mul hg1)).add
      ((continuousAt_fst.mul hf1).mul hgr)).add
        (hg0.mul hfr)).add
          ((continuousAt_fst.mul hg1).mul hfr)).add
            (((continuousAt_fst.pow 2).mul hfr).mul hgr)

  eventually_eq_joint := fun q => by
    filter_upwards [hf.eventually_eq_joint q, hg.eventually_eq_joint q]
      with p hfp hgp
    change f p.2 p.1 * g p.2 p.1 =
      (hf.jet p.2).c₀ * (hg.jet p.2).c₀ +
      p.1 * ((hf.jet p.2).c₀ * (hg.jet p.2).c₁ +
        (hf.jet p.2).c₁ * (hg.jet p.2).c₀) +
      p.1 ^ 2 *
        ((hf.jet p.2).c₀ * (hg.jet p.2).jet.remainder p.1 +
        (hf.jet p.2).c₁ * (hg.jet p.2).c₁ +
        p.1 * (hf.jet p.2).c₁ * (hg.jet p.2).jet.remainder p.1 +
        (hg.jet p.2).c₀ * (hf.jet p.2).jet.remainder p.1 +
        p.1 * (hg.jet p.2).c₁ * (hf.jet p.2).jet.remainder p.1 +
        p.1 ^ 2 * (hf.jet p.2).jet.remainder p.1 *
          (hg.jet p.2).jet.remainder p.1)
    rw [hfp, hgp]
    ring
def congr (hf : JointJetData f)
    (hfg : ∀ q s, g q s = f q s) : JointJetData g where
  jet := fun q => ⟨(hf.jet q).c₀, (hf.jet q).c₁, (hf.jet q).c₂,
    (hf.jet q).jet.congr <| by
      filter_upwards
      intro s
      exact hfg q s⟩
  continuousAt_function := fun q => by
    rw [show (fun p : ℝ × (Fin 3 → ℝ) => g p.2 p.1) =
      fun p => f p.2 p.1 by funext p; exact hfg p.2 p.1]
    exact hf.continuousAt_function q
  continuousAt_c₀ := hf.continuousAt_c₀
  continuousAt_c₁ := hf.continuousAt_c₁
  continuousAt_c₂ := hf.continuousAt_c₂
  continuousAt_remainder := hf.continuousAt_remainder
  eventually_eq_joint := fun q => by
    filter_upwards [hf.eventually_eq_joint q] with p hp
    change g p.2 p.1 = (hf.jet p.2).c₀ +
      p.1 * (hf.jet p.2).c₁ +
      p.1 ^ 2 * (hf.jet p.2).jet.remainder p.1
    rw [hfg p.2 p.1, hp]
def sq (hf : JointJetData f) :
    JointJetData (fun q s => f q s ^ 2) :=
  (hf.mul hf).congr (by intro q s; rw [pow_two])

def cube (hf : JointJetData f) :
    JointJetData (fun q s => f q s ^ 3) :=
  (hf.mul (hf.mul hf)).congr (by intro q s; rw [pow_three])
def smul (c : ℝ) (hf : JointJetData f) :
    JointJetData (fun q s => c * f q s) :=
  (JointJetData.const c).mul hf

def inv (hf : JointJetData f) (h₀ : ∀ q, (hf.jet q).c₀ ≠ 0) :
    JointJetData (fun q s => (f q s)⁻¹) where
  jet := fun q => (hf.jet q).inv (h₀ q)
  continuousAt_function := fun q =>
    (hf.continuousAt_function q).inv₀ (by
      rw [(hf.jet q).jet.value]
      exact h₀ q)
  continuousAt_c₀ := fun q => (hf.continuousAt_c₀ q).inv₀ (h₀ q)
  continuousAt_c₁ := fun q =>
    ((hf.continuousAt_c₁ q).neg.div
      ((hf.continuousAt_c₀ q).pow 2) (pow_ne_zero 2 (h₀ q)))
  continuousAt_c₂ := fun q =>
    (((hf.continuousAt_c₁ q).pow 2).div
      ((hf.continuousAt_c₀ q).pow 3) (pow_ne_zero 3 (h₀ q))).sub
        ((hf.continuousAt_c₂ q).div ((hf.continuousAt_c₀ q).pow 2)
          (pow_ne_zero 2 (h₀ q)))
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p =>
      (((hf.jet p.2).c₁ ^ 2 / (hf.jet p.2).c₀ ^ 2 -
        (hf.jet p.2).jet.remainder p.1 / (hf.jet p.2).c₀ +
        p.1 * (hf.jet p.2).c₁ * (hf.jet p.2).jet.remainder p.1 /
          (hf.jet p.2).c₀ ^ 2) / f p.2 p.1)) (0, q)
    have hc0 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hf.jet p.2).c₀) (0, q) :=
      (hf.continuousAt_c₀ q).snd' (x := (0 : ℝ))
    have hc1 : ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
        (hf.jet p.2).c₁) (0, q) :=
      (hf.continuousAt_c₁ q).snd' (x := (0 : ℝ))
    have hr := hf.continuousAt_remainder q
    have hnum := (((hc1.pow 2).div (hc0.pow 2)
      (pow_ne_zero 2 (h₀ q))).sub (hr.div hc0 (h₀ q))).add
        (((continuousAt_fst.mul hc1).mul hr).div
          (hc0.pow 2) (pow_ne_zero 2 (h₀ q)))
    apply hnum.div (hf.continuousAt_function q)
    rw [(hf.jet q).jet.value]
    exact h₀ q
  eventually_eq_joint := fun q => by
    have hfn : f q 0 ≠ 0 := by
      rw [(hf.jet q).jet.value]
      exact h₀ q
    filter_upwards [hf.eventually_eq_joint q,
      (hf.continuousAt_function q).eventually_ne hfn] with p hfp hpne
    change (f p.2 p.1)⁻¹ =
      ((hf.jet p.2).c₀)⁻¹ +
      p.1 * (-(hf.jet p.2).c₁ / (hf.jet p.2).c₀ ^ 2) +
      p.1 ^ 2 *
        (((hf.jet p.2).c₁ ^ 2 / (hf.jet p.2).c₀ ^ 2 -
          (hf.jet p.2).jet.remainder p.1 / (hf.jet p.2).c₀ +
          p.1 * (hf.jet p.2).c₁ *
            (hf.jet p.2).jet.remainder p.1 /
              (hf.jet p.2).c₀ ^ 2) / f p.2 p.1)
    have hexp : (hf.jet p.2).c₀ + p.1 * (hf.jet p.2).c₁ +
        p.1 ^ 2 * (hf.jet p.2).jet.remainder p.1 ≠ 0 := by
      rw [← hfp]
      exact hpne
    rw [hfp]
    field_simp [h₀ p.2, hexp]
    ring
def div (hf : JointJetData f) (hg : JointJetData g)
    (h₀ : ∀ q, (hg.jet q).c₀ ≠ 0) :
    JointJetData (fun q s => f q s / g q s) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv h₀)


def sqMulContinuous {g : (Fin 3 → ℝ) → ℝ → ℝ}
    (hg : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => g p.2 p.1) (0, q)) :
    JointJetData (fun q s => s ^ 2 * g q s) where
  jet := fun q => ⟨0, 0, g q 0, HasTwoJet.sq_mul_continuous <| by
    have h := hg q
    have hmap : ContinuousAt (fun s : ℝ => (s, q)) 0 :=
      continuousAt_id.prodMk continuousAt_const
    exact h.comp_of_eq hmap rfl⟩
  continuousAt_function := fun q =>
    (continuousAt_fst.pow 2).mul (hg q)
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun q => by
    have h := hg q
    have hmap : ContinuousAt
        (fun r : Fin 3 → ℝ => ((0 : ℝ), r)) q :=
      continuousAt_const.prodMk continuousAt_id
    change ContinuousAt ((fun p : ℝ × (Fin 3 → ℝ) =>
      g p.2 p.1) ∘ fun r : Fin 3 → ℝ => ((0 : ℝ), r)) q
    exact h.comp hmap
  continuousAt_remainder := hg
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change p.1 ^ 2 * g p.2 p.1 =
      0 + p.1 * 0 + p.1 ^ 2 * g p.2 p.1
    ring

def mulContinuousOrderTwo (hf : JointJetData f)
    (hf0 : ∀ q, (hf.jet q).c₀ = 0)
    (hf1 : ∀ q, (hf.jet q).c₁ = 0)
    {g : (Fin 3 → ℝ) → ℝ → ℝ}
    (hg : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => g p.2 p.1) (0, q)) :
    JointJetData (fun q s => f q s * g q s) where
  jet := fun q => by
    have hgq : ContinuousAt (g q) 0 := by
      have hmap : ContinuousAt (fun s : ℝ => (s, q)) 0 :=
        continuousAt_id.prodMk continuousAt_const
      exact (hg q).comp_of_eq hmap rfl
    refine ⟨0, 0, (hf.jet q).c₂ * g q 0, ?_⟩
    refine ⟨fun s => (hf.jet q).jet.remainder s * g q s,
      (hf.jet q).jet.continuousAt_remainder.mul hgq, by simp, ?_⟩
    filter_upwards [(hf.jet q).jet.eventually_eq_remainder] with s hs
    rw [hs]
    simp only [hf0 q, hf1 q, zero_add, mul_zero]
    ring
  continuousAt_function := fun q =>
    (hf.continuousAt_function q).mul (hg q)
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun q => by
    have hg0 : ContinuousAt (fun r => g r 0) q := by
      have hmap : ContinuousAt
          (fun r : Fin 3 → ℝ => ((0 : ℝ), r)) q :=
        continuousAt_const.prodMk continuousAt_id
      change ContinuousAt ((fun p : ℝ × (Fin 3 → ℝ) =>
        g p.2 p.1) ∘ fun r : Fin 3 → ℝ => ((0 : ℝ), r)) q
      exact (hg q).comp hmap
    exact (hf.continuousAt_c₂ q).mul hg0
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      (hf.jet p.2).jet.remainder p.1 * g p.2 p.1) (0, q)
    exact (hf.continuousAt_remainder q).mul (hg q)
  eventually_eq_joint := fun q => by
    filter_upwards [hf.eventually_eq_joint q] with p hp
    change f p.2 p.1 * g p.2 p.1 =
      0 + p.1 * 0 +
        p.1 ^ 2 * ((hf.jet p.2).jet.remainder p.1 * g p.2 p.1)
    rw [hp]
    simp only [hf0 p.2, hf1 p.2, zero_add, mul_zero]
    ring

def atanQuotient (hf : JointJetData f)
    (hf0 : ∀ q, (hf.jet q).c₀ = 0) :
    JointJetData (fun q s => NearOneAnalyticSystem.atanQuotient (f q s)) := by
  let R : (Fin 3 → ℝ) → ℝ → ℝ := fun q s =>
    atanQuotientSqRemainder (f q s)
  have hR : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => R p.2 p.1) (0, q) := by
    intro q
    exact continuous_atanQuotientSqRemainder.continuousAt.comp
      (hf.continuousAt_function q)
  let hsq := hf.sq
  have hsq0 : ∀ q, (hsq.jet q).c₀ = 0 := by
    intro q
    change ((hf.mul hf).jet q).c₀ = 0
    change (hf.jet q).c₀ * (hf.jet q).c₀ = 0
    rw [hf0 q, zero_mul]
  have hsq1 : ∀ q, (hsq.jet q).c₁ = 0 := by
    intro q
    change ((hf.mul hf).jet q).c₁ = 0
    change (hf.jet q).c₀ * (hf.jet q).c₁ +
      (hf.jet q).c₁ * (hf.jet q).c₀ = 0
    rw [hf0 q]
    ring
  let h := (JointJetData.const 1).add
    (hsq.mulContinuousOrderTwo hsq0 hsq1 hR)
  exact h.congr (by
    intro q s
    exact atanQuotient_eq_one_add_sq_mul (f q s))

def arctan (hf : JointJetData f)
    (hf0 : ∀ q, (hf.jet q).c₀ = 0) :
    JointJetData (fun q s => Real.arctan (f q s)) := by
  let h := hf.mul (JointJetData.atanQuotient hf hf0)
  exact h.congr (by intro q s; exact (mul_atanQuotient (f q s)).symm)

def physicalZData : JointJetData physicalZ where
  jet := physicalZSomeJet
  continuousAt_function := continuousAt_physicalZ_joint
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun _ => by
    change ContinuousAt (fun r : Fin 3 → ℝ => r 0) _
    exact (continuous_apply 0).continuousAt
  continuousAt_remainder := fun q => by
    change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) => p.2 0) (0, q)
    fun_prop
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change physicalZ p.2 p.1 =
      Real.pi + p.1 * Real.pi ^ 2 + p.1 ^ 2 * p.2 0
    exact physicalZ_eq p.2 p.1

def physicalAData : JointJetData physicalA where
  jet := physicalASomeJet
  continuousAt_function := continuousAt_physicalA_joint
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun _ => by
    simp [physicalASomeJet]
    fun_prop
  continuousAt_remainder := fun _ => by
    change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      5 * p.2 0 / 12 + p.2 1) _
    fun_prop
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change physicalA p.2 p.1 = 5 * Real.pi / 12 +
      p.1 * ((43 * Real.pi ^ 2 + 1056) / 144) +
      p.1 ^ 2 * (5 * p.2 0 / 12 + p.2 1)
    exact physicalA_eq p.2 p.1

def physicalBData : JointJetData physicalB where
  jet := physicalBSomeJet
  continuousAt_function := continuousAt_physicalB_joint
  continuousAt_c₀ := fun _ => continuousAt_const
  continuousAt_c₁ := fun _ => continuousAt_const
  continuousAt_c₂ := fun _ => by
    simp [physicalBSomeJet]
    fun_prop
  continuousAt_remainder := fun _ => by
    change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * p.2 0 +
        (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * p.2 1 + p.2 2) _
    fun_prop
  eventually_eq_joint := fun _ => by
    filter_upwards
    intro p
    change physicalB p.2 p.1 = -44 + 19 * Real.pi ^ 2 / 24 +
      p.1 * (Real.pi * (295 * Real.pi ^ 2 - 14256) / 216) +
      p.1 ^ 2 * ((109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * p.2 0 +
        (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * p.2 1 + p.2 2)
    exact physicalB_eq p.2 p.1

def aCoordData : JointJetData (fun q s => aCoord s (physicalZ q s)) := by
  let h := (JointJetData.const 1).add (JointJetData.id.mul physicalZData)
  exact h.congr (by intro q s; unfold aCoord; rfl)

def rCoordData : JointJetData (fun q s => rCoord s (physicalA q s)) := by
  let h := (JointJetData.const 2).add (JointJetData.id.mul physicalAData)
  exact h.congr (by intro q s; unfold rCoord; rfl)

def eCoordData : JointJetData (fun q s =>
    eCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) := by
  let h := (JointJetData.const 6).mul physicalAData |>.sub
    ((JointJetData.const 2).mul physicalZData) |>.add
    (JointJetData.id.mul physicalBData)
  exact h.congr (by intro q s; unfold eCoord; rfl)

def yCoordData : JointJetData (fun q s => yCoord s (physicalZ q s)) := by
  let h := JointJetData.id.mul aCoordData
  exact h.congr (by intro q s; unfold yCoord; rfl)

def wCoordData : JointJetData (fun q s => wCoord s (physicalA q s)) := by
  let h := JointJetData.id.mul rCoordData
  exact h.congr (by intro q s; unfold wCoord; rfl)

def vCoordData : JointJetData (fun q s =>
    vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) := by
  let h := JointJetData.id.mul
    (rCoordData.add (JointJetData.id.mul eCoordData))
  exact h.congr (by intro q s; unfold vCoord; rfl)

end JointJetData
namespace JointJetData
private def halfCosData {f : (Fin 3 → ℝ) → ℝ → ℝ}
    (hx : JointJetData f) :
    JointJetData (fun q s => halfCos (f q s)) := by
  let one := JointJetData.const 1
  let xx := hx.sq
  have hden : ∀ q, ((one.add xx).jet q).c₀ ≠ 0 := by
    intro q
    rw [← ((one.add xx).jet q).jet.value]
    change 1 + f q 0 ^ 2 ≠ 0
    positivity
  let h := (one.sub xx).div (one.add xx) hden
  exact h.congr (by intro q s; unfold halfCos; rfl)

def densityData : JointJetData (fun q s => density s (physicalZ q s)) := by
  let hs := halfCosData JointJetData.id
  let hy := halfCosData yCoordData
  have hy0 : ∀ q, (hy.jet q).c₀ ≠ 0 := by
    intro q
    rw [← (hy.jet q).jet.value]
    simp [halfCos, yCoord, aCoord, physicalZ, tangentCenteredPoint,
      exactCuspPoint, exactCuspTangent, exactCuspShear, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  exact (hs.div hy hy0).congr (by intro q s; unfold density; rfl)

def densityCubeQuotientData :
    JointJetData (fun q s => densityCubeQuotient s (physicalZ q s)) := by
  let one := JointJetData.const 1
  let two := JointJetData.const 2
  let num := (two.mul physicalZData).mul
    (two.add (JointJetData.id.mul physicalZData))
  let den := (one.add JointJetData.id.sq).mul (one.sub yCoordData.sq)
  have hden : ∀ q, (den.jet q).c₀ ≠ 0 := by
    intro q
    rw [← (den.jet q).jet.value]
    simp [den, one, yCoord, aCoord, physicalZ, tangentCenteredPoint,
      exactCuspPoint, exactCuspTangent, exactCuspShear, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  exact (num.div den hden).congr
    (by intro q s; unfold densityCubeQuotient; rfl)

def typeFourSineProductBarData :
    JointJetData (fun q s => typeFourSineProductBar s (physicalZ q s)) := by
  let one := JointJetData.const 1
  let den := (one.add JointJetData.id.sq).mul (one.add yCoordData.sq)
  have hden : ∀ q, (den.jet q).c₀ ≠ 0 := by
    intro q
    rw [← (den.jet q).jet.value]
    positivity
  let h := ((JointJetData.const 4).mul aCoordData).div den hden
  exact h.congr (by intro q s; unfold typeFourSineProductBar; rfl)

def foldDenominatorData :
    JointJetData (fun q s => foldDenominator s (physicalZ q s)) := by
  let one := JointJetData.const 1
  let h := ((JointJetData.const 2).mul
    (one.add JointJetData.id.sq).sq).mul (one.add yCoordData.sq)
  exact h.congr (by intro q s; unfold foldDenominator; rfl)

def areaDenominatorData : JointJetData (fun q s =>
    areaDenominator s (physicalZ q s) (physicalA q s)
      (physicalB q s)) := by
  let one := JointJetData.const 1
  let h := (((((JointJetData.const 2).mul
    (one.add JointJetData.id.sq).sq).mul
      (one.add wCoordData.sq).sq).mul (one.add yCoordData.sq)).mul
        (one.add vCoordData.sq))
  exact h.congr (by intro q s; unfold areaDenominator; rfl)


private def fourAngleDenData :
    JointJetData (fun q s => 1 + s * yCoord s (physicalZ q s)) :=
  (JointJetData.const 1).add (JointJetData.id.mul yCoordData)

private theorem fourAngleDenData_ne (q : Fin 3 → ℝ) :
    (fourAngleDenData.jet q).c₀ ≠ 0 := by
  rw [← (fourAngleDenData.jet q).jet.value]
  simp

private def typeFourAngleIncrementBar2Data : JointJetData (fun q s =>
    typeFourAngleIncrementBar2 s (physicalZ q s)) := by
  let den := fourAngleDenData
  let harg := (JointJetData.id.sq.mul physicalZData).div den
    fourAngleDenData_ne
  let R : (Fin 3 → ℝ) → ℝ → ℝ := fun q s =>
    atanQuotientSqRemainder
      (s ^ 2 * physicalZ q s /
        (1 + s * yCoord s (physicalZ q s)))
  have hR : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => R p.2 p.1) (0, q) := by
    intro q
    exact continuous_atanQuotientSqRemainder.continuousAt.comp
      (harg.continuousAt_function q)
  let G : (Fin 3 → ℝ) → ℝ → ℝ := fun q s =>
    physicalZ q s ^ 2 /
      (1 + s * yCoord s (physicalZ q s)) ^ 2 * R q s
  have hG : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => G p.2 p.1) (0, q) := by
    intro q
    exact ((physicalZData.continuousAt_function q).pow 2 |>.div
      ((den.continuousAt_function q).pow 2) (by norm_num)).mul (hR q)
  let hrem := JointJetData.sqMulContinuous hG
  let lead := ((JointJetData.const 2).mul physicalZData).div den
    fourAngleDenData_ne
  let h := lead.mul (hrem.sub aCoordData)
  exact h.congr (by
    intro q s
    unfold typeFourAngleIncrementBar2
    dsimp [G, R]
    ring)

private def typeFourAngleBar2Data : JointJetData (fun q s =>
    typeFourAngleBar2 s (physicalZ q s)) := by
  let hatan := JointJetData.atanQuotient JointJetData.id (by
    intro q
    rfl)
  let h := ((((JointJetData.const 2).mul densityCubeQuotientData).mul
    hatan).add (densityData.mul typeFourAngleIncrementBar2Data)).add
      ((((JointJetData.const 2).mul JointJetData.id).mul
        physicalZData).mul densityCubeQuotientData)
  exact h.congr (by intro q s; unfold typeFourAngleBar2; rfl)

private def threeAngleDenData : JointJetData (fun q s =>
    1 + wCoord s (physicalA q s) *
      vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) :=
  (JointJetData.const 1).add (wCoordData.mul vCoordData)

private theorem threeAngleDenData_ne (q : Fin 3 → ℝ) :
    (threeAngleDenData.jet q).c₀ ≠ 0 := by
  rw [← (threeAngleDenData.jet q).jet.value]
  simp [wCoord, vCoord]

private def typeThreeAngleIncrementBar2Data : JointJetData (fun q s =>
    typeThreeAngleIncrementBar2 s (physicalZ q s) (physicalA q s)
      (physicalB q s)) := by
  let den := threeAngleDenData
  let harg := (JointJetData.id.sq.mul eCoordData).div den
    threeAngleDenData_ne
  let R : (Fin 3 → ℝ) → ℝ → ℝ := fun q s =>
    atanQuotientSqRemainder
      (s ^ 2 *
        eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) /
          (1 + wCoord s (physicalA q s) *
            vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)))
  have hR : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => R p.2 p.1) (0, q) := by
    intro q
    exact continuous_atanQuotientSqRemainder.continuousAt.comp
      (harg.continuousAt_function q)
  let G : (Fin 3 → ℝ) → ℝ → ℝ := fun q s =>
    eCoord s (physicalZ q s) (physicalA q s) (physicalB q s) ^ 2 /
      (1 + wCoord s (physicalA q s) *
        vCoord s (physicalZ q s) (physicalA q s) (physicalB q s)) ^ 2 *
      R q s
  have hG : ∀ q, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => G p.2 p.1) (0, q) := by
    intro q
    exact ((eCoordData.continuousAt_function q).pow 2 |>.div
      ((den.continuousAt_function q).pow 2)
        (by simp [wCoord, vCoord])).mul (hR q)
  let hrem := JointJetData.sqMulContinuous hG
  let lead := ((JointJetData.const 2).mul eCoordData).div den
    threeAngleDenData_ne
  let rr := rCoordData.mul
    (rCoordData.add (JointJetData.id.mul eCoordData))
  let h := lead.mul (hrem.sub rr)
  exact h.congr (by
    intro q s
    unfold typeThreeAngleIncrementBar2
    dsimp [G, R]
    ring)

private def typeThreeAngleBar2Data : JointJetData (fun q s =>
    typeThreeAngleBar2 s (physicalZ q s) (physicalA q s)
      (physicalB q s)) := by
  have hw0 : ∀ q, (wCoordData.jet q).c₀ = 0 := by
    intro q
    rw [← (wCoordData.jet q).jet.value]
    simp [wCoord]
  let hatan := JointJetData.atanQuotient wCoordData hw0
  let h := (((((JointJetData.const 2).mul densityCubeQuotientData).mul
    rCoordData).mul hatan).add
      (densityData.mul typeThreeAngleIncrementBar2Data)).add
        ((((JointJetData.const 2).mul JointJetData.id).mul
          eCoordData).mul densityCubeQuotientData)
  exact h.congr (by intro q s; unfold typeThreeAngleBar2; rfl)

private def typeFourAngleIncrementData : JointJetData (fun q s =>
    typeFourAngleIncrement s (physicalZ q s)) := by
  let den := fourAngleDenData
  let harg := (JointJetData.id.sq.mul physicalZData).div den
    fourAngleDenData_ne
  have harg0 : ∀ q, (harg.jet q).c₀ = 0 := by
    intro q
    rw [← (harg.jet q).jet.value]
    simp
  let hatan := JointJetData.atanQuotient harg harg0
  let h := (((JointJetData.const 2).mul physicalZData).div den
    fourAngleDenData_ne).mul hatan
  exact h.congr (by intro q s; unfold typeFourAngleIncrement; rfl)

private def typeFourAngleBarData : JointJetData (fun q s =>
    typeFourAngleBar s (physicalZ q s)) := by
  let harctan := JointJetData.arctan JointJetData.id (by intro q; rfl)
  let h := (((((JointJetData.const 2).mul JointJetData.id).mul
    densityCubeQuotientData).mul harctan).add
      (densityData.mul typeFourAngleIncrementData))
  exact h.congr (by intro q s; unfold typeFourAngleBar; rfl)

private def normalizedThirdRowCoeffZeroData : JointJetData (fun q s =>
    normalizedThirdRowCoeffZero (physicalZ q s) (physicalA q s)
      (physicalB q s) Real.pi) := by
  let hz := physicalZData
  let ha := physicalAData
  let hb := physicalBData
  let inner :=
    (ha.cube.smul (-576)).add <|
    (ha.sq.smul (42 * Real.pi)).add <|
    ((ha.sq.mul hz).smul 432).add <|
    ((ha.mul hb).smul 36).add <|
    ((ha.mul hz).smul (-28 * Real.pi)).add <|
    ((ha.mul hz.sq).smul (-92)).add <|
    (hb.smul (4 * Real.pi)).add <|
    ((hb.mul hz).smul (-16)).add <|
    (hz.sq.smul Real.pi).add <|
    (JointJetData.const (-48 * Real.pi)).add <|
    (hz.cube.smul 6).add <|
    hz.smul 180
  exact (inner.smul (-(4 / 3))).congr (by
    intro q s
    unfold normalizedThirdRowCoeffZero
    ring)

private def normalizedThirdRowCoeffOneData : JointJetData (fun q s =>
    normalizedThirdRowCoeffOne (physicalZ q s) (physicalA q s)
      (physicalB q s) Real.pi) := by
  let hz := physicalZData
  let ha := physicalAData
  let hb := physicalBData
  let inner :=
    ((ha.sq.mul hb).smul 84).add <|
    (ha.sq.smul (-144)).add <|
    ((ha.mul hb).smul (-7 * Real.pi)).add <|
    (((ha.mul hb).mul hz).smul (-38)).add <|
    (ha.smul (252 * Real.pi)).add <|
    ((ha.mul hz).smul (-120)).add <|
    (hb.sq.smul (-3)).add <|
    ((hb.mul hz).smul (2 * Real.pi)).add <|
    ((hb.mul hz.sq).smul 4).add <|
    (hz.smul (-41 * Real.pi)).add <|
    hz.sq.smul 14
  exact (inner.smul (8 / 3)).congr (by
    intro q s
    unfold normalizedThirdRowCoeffOne
    ring)

private def normalizedThirdRowData : JointJetData (fun q s =>
    H3hatPolynomial s (physicalZ q s) (physicalA q s)
      (physicalB q s) Real.pi) := by
  let htail := JointJetData.sqMulContinuous
    continuousAt_normalizedThirdRowTailPath_joint
  let h := (normalizedThirdRowCoeffZeroData.add
    (JointJetData.id.mul normalizedThirdRowCoeffOneData)).add htail
  exact h.congr (by
    intro q s
    rw [H3hatPolynomial, polynomial_eval_eq_first_two_coeffs,
      normalizedThirdRow_coeff_zero, normalizedThirdRow_coeff_one]
    rfl)

private def foldAngleCorrectionBarData : JointJetData (fun q s =>
    foldAngleCorrectionBar s (physicalZ q s)) := by
  let h := (foldDenominatorData.neg.mul typeFourSineProductBarData).mul
    typeFourAngleBarData
  exact h.congr (by intro q s; unfold foldAngleCorrectionBar; rfl)
private def KEvalData : JointJetData (fun q s =>
    (NearOneNormalizedFlow.K (physicalA q s)).eval s) := by
  let two := JointJetData.const 2
  let four := JointJetData.const 4
  let r := two.add (JointJetData.id.mul physicalAData)
  let r2 := r.sq
  let r4 := r2.sq
  let s2 := JointJetData.id.sq
  let s4 := s2.sq
  let s6 := s4.mul s2
  let h := ((two.mul r2).sub four).add <|
    (s2.mul (r4.sub (four.mul r2))).add <|
    ((two.mul s4).mul (r2.sub r4)).add <|
    s6.mul r4
  exact h.congr (by
    intro q s
    simp [NearOneNormalizedFlow.K, NearOneNormalizedFlow.R]
    ring)

private def areaPiWeightData : JointJetData (fun q s =>
    areaPiWeight s (physicalA q s)) := by
  let one := JointJetData.const 1
  let den := (one.add JointJetData.id.sq).sq.mul
    (one.add wCoordData.sq).sq
  have hden : ∀ q, (den.jet q).c₀ ≠ 0 := by
    intro q
    rw [← (den.jet q).jet.value]
    positivity
  let h := ((JointJetData.const 2).mul KEvalData).div den hden
  exact h.congr (by intro q s; unfold areaPiWeight; rfl)


private def areaAngleCorrectionBarData : JointJetData (fun q s =>
    areaAngleCorrectionBar s (physicalZ q s) (physicalA q s)
      (physicalB q s)) := by
  let one := JointJetData.const 1
  let hs := JointJetData.halfCosData JointJetData.id
  let hw := JointJetData.halfCosData wCoordData
  let term1 := (((JointJetData.const 2).mul hs.sq).mul
    typeThreeAngleBar2Data)
  let term2 := (one.add hw).sq.mul typeFourAngleBar2Data
  let term3 := ((JointJetData.const 4).mul physicalZData).mul
    areaPiWeightData
  let h := areaDenominatorData.mul ((term1.sub term2).add term3)
  exact h.congr (by intro q s; unfold areaAngleCorrectionBar; rfl)

private def regularizedThirdRowData : JointJetData (fun q s =>
    regularizedThirdRow s (physicalZ q s) (physicalA q s)
      (physicalB q s) Real.pi) := by
  let foldFactor := (JointJetData.const 4).sub
    ((((JointJetData.const 2).mul physicalZData).mul JointJetData.id).smul
      (1 / 3))
  let fold := foldFactor.mul foldAngleCorrectionBarData
  let h := (normalizedThirdRowData.add areaAngleCorrectionBarData).add fold
  exact h.congr (by
    intro q s
    unfold regularizedThirdRow
    ring)


end JointJetData

macro "hpoly_path_coeff" : tactic =>
  `(tactic|
    simp [H3hatPolynomialFactoredJet,
      normalizedThirdRowCoeffZeroPathJet,
      normalizedThirdRowCoeffOnePathJet,
      normalizedThirdRowTailPath_zero,
      physicalZSomeJet, physicalASomeJet, physicalBSomeJet,
      SomeHasTwoJet.const, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.sub, SomeHasTwoJet.neg, SomeHasTwoJet.mul,
      SomeHasTwoJet.smul, SomeHasTwoJet.div, SomeHasTwoJet.sq,
      SomeHasTwoJet.cube, SomeHasTwoJet.pow, id_eq] <;>
    norm_num [normalizedThirdRowCoeffTwo] <;>
    (try field_simp [Real.pi_ne_zero]) <;>
    ring)

private opaque H3hatPolynomialFactoredJet_c₀ (q : Fin 3 → ℝ) :
    (H3hatPolynomialFactoredJet q).c₀ = 0 := by
  hpoly_path_coeff

private opaque H3hatPolynomialFactoredJet_c₁ (q : Fin 3 → ℝ) :
    (H3hatPolynomialFactoredJet q).c₁ = 32 * Real.pi ^ 2 := by
  hpoly_path_coeff

private opaque H3hatPolynomialFactoredJet_c₂ (q : Fin 3 → ℝ) :
    (H3hatPolynomialFactoredJet q).c₂ =
      (1193 * Real.pi ^ 5 + 3656952 * Real.pi ^ 3 -
        31104 * Real.pi * q 2 - 172606464 * Real.pi +
        1492992 * q 1) / 7776 := by
  hpoly_path_coeff

private opaque H3hatPolynomial_physical_twoJet (q : Fin 3 → ℝ) :
    HasTwoJet (fun s =>
      H3hatPolynomial s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi)
      0 (32 * Real.pi ^ 2)
      ((1193 * Real.pi ^ 5 + 3656952 * Real.pi ^ 3 -
        31104 * Real.pi * q 2 - 172606464 * Real.pi +
        1492992 * q 1) / 7776) := by
  let h := H3hatPolynomialFactoredJet q
  have hj := h.jet
  convert hj using 1
  · exact (H3hatPolynomialFactoredJet_c₀ q).symm
  · exact (H3hatPolynomialFactoredJet_c₁ q).symm
  · exact (H3hatPolynomialFactoredJet_c₂ q).symm
macro "a_coord_path_coeff" : tactic =>
  `(tactic|
    simp [aCoordPathJet, physicalZSomeJet, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul] <;>
    ring)

private opaque aCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (aCoordPathJet q).c₀ = 1 := by
  a_coord_path_coeff

private opaque aCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (aCoordPathJet q).c₁ = Real.pi := by
  a_coord_path_coeff

private opaque aCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (aCoordPathJet q).c₂ = Real.pi ^ 2 := by
  a_coord_path_coeff

macro "y_coord_path_coeff" : tactic =>
  `(tactic|
    simp [yCoordPathJet, aCoordPathJet_c₀, aCoordPathJet_c₁,
      aCoordPathJet_c₂, SomeHasTwoJet.id, SomeHasTwoJet.mul] <;>
    ring)

private opaque yCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (yCoordPathJet q).c₀ = 0 := by
  y_coord_path_coeff

private opaque yCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (yCoordPathJet q).c₁ = 1 := by
  y_coord_path_coeff

private opaque yCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (yCoordPathJet q).c₂ = Real.pi := by
  y_coord_path_coeff

macro "density_path_coeff" : tactic =>
  `(tactic|
    simp [densityPathJet, halfCosJet, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.sub, SomeHasTwoJet.add,
      SomeHasTwoJet.div, SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque densityPathJet_c₀ (q : Fin 3 → ℝ) :
    (densityPathJet q).c₀ = 1 := by
  density_path_coeff

private opaque densityPathJet_c₁ (q : Fin 3 → ℝ) :
    (densityPathJet q).c₁ = 0 := by
  density_path_coeff

private opaque densityPathJet_c₂ (q : Fin 3 → ℝ) :
    (densityPathJet q).c₂ = 0 := by
  density_path_coeff

macro "density_cube_path_coeff" : tactic =>
  `(tactic|
    simp [densityCubeQuotientPathJet, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, physicalZSomeJet,
      SomeHasTwoJet.const, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.sub, SomeHasTwoJet.mul, SomeHasTwoJet.div,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque densityCubeQuotientPathJet_c₀ (q : Fin 3 → ℝ) :
    (densityCubeQuotientPathJet q).c₀ = 4 * Real.pi := by
  density_cube_path_coeff

private opaque densityCubeQuotientPathJet_c₁ (q : Fin 3 → ℝ) :
    (densityCubeQuotientPathJet q).c₁ = 6 * Real.pi ^ 2 := by
  density_cube_path_coeff

private opaque densityCubeQuotientPathJet_c₂ (q : Fin 3 → ℝ) :
    (densityCubeQuotientPathJet q).c₂ =
      4 * (Real.pi ^ 3 + q 0) := by
  density_cube_path_coeff

macro "four_increment_path_coeff" : tactic =>
  `(tactic|
    simp [typeFourAngleIncrementPathJet, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, physicalZSomeJet,
      SomeHasTwoJet.const, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.mul, SomeHasTwoJet.div, SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque typeFourAngleIncrementPathJet_c₀ (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementPathJet q).c₀ = 2 * Real.pi := by
  four_increment_path_coeff

private opaque typeFourAngleIncrementPathJet_c₁ (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementPathJet q).c₁ = 2 * Real.pi ^ 2 := by
  four_increment_path_coeff

private opaque typeFourAngleIncrementPathJet_c₂ (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementPathJet q).c₂ =
      -2 * (Real.pi - q 0) := by
  four_increment_path_coeff

macro "four_angle_path_coeff" : tactic =>
  `(tactic|
    simp [typeFourAngleBarPathJet, densityCubeQuotientPathJet_c₀,
      densityCubeQuotientPathJet_c₁, densityCubeQuotientPathJet_c₂,
      densityPathJet_c₀, densityPathJet_c₁, densityPathJet_c₂,
      typeFourAngleIncrementPathJet_c₀,
      typeFourAngleIncrementPathJet_c₁,
      typeFourAngleIncrementPathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul] <;>
    norm_num <;>
    ring)

private opaque typeFourAngleBarPathJet_c₀ (q : Fin 3 → ℝ) :
    (typeFourAngleBarPathJet q).c₀ = 2 * Real.pi := by
  four_angle_path_coeff

private opaque typeFourAngleBarPathJet_c₁ (q : Fin 3 → ℝ) :
    (typeFourAngleBarPathJet q).c₁ = 2 * Real.pi ^ 2 := by
  four_angle_path_coeff

private opaque typeFourAngleBarPathJet_c₂ (q : Fin 3 → ℝ) :
    (typeFourAngleBarPathJet q).c₂ =
      2 * (3 * Real.pi + q 0) := by
  four_angle_path_coeff

macro "four_sine_path_coeff" : tactic =>
  `(tactic|
    simp [typeFourSineProductBarPathJet, aCoordPathJet_c₀,
      aCoordPathJet_c₁, aCoordPathJet_c₂, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul,
      SomeHasTwoJet.div, SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque typeFourSineProductBarPathJet_c₀ (q : Fin 3 → ℝ) :
    (typeFourSineProductBarPathJet q).c₀ = 4 := by
  four_sine_path_coeff

private opaque typeFourSineProductBarPathJet_c₁ (q : Fin 3 → ℝ) :
    (typeFourSineProductBarPathJet q).c₁ = 4 * Real.pi := by
  four_sine_path_coeff

private opaque typeFourSineProductBarPathJet_c₂ (q : Fin 3 → ℝ) :
    (typeFourSineProductBarPathJet q).c₂ =
      4 * (Real.pi ^ 2 - 2) := by
  four_sine_path_coeff

macro "fold_denominator_path_coeff" : tactic =>
  `(tactic|
    simp [foldDenominatorPathJet, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque foldDenominatorPathJet_c₀ (q : Fin 3 → ℝ) :
    (foldDenominatorPathJet q).c₀ = 2 := by
  fold_denominator_path_coeff

private opaque foldDenominatorPathJet_c₁ (q : Fin 3 → ℝ) :
    (foldDenominatorPathJet q).c₁ = 0 := by
  fold_denominator_path_coeff

private opaque foldDenominatorPathJet_c₂ (q : Fin 3 → ℝ) :
    (foldDenominatorPathJet q).c₂ = 6 := by
  fold_denominator_path_coeff


macro "fold_path_coeff" : tactic =>
  `(tactic|
    simp [foldAngleCorrectionBarPathJet, foldDenominatorPathJet_c₀,
      foldDenominatorPathJet_c₁, foldDenominatorPathJet_c₂,
      typeFourSineProductBarPathJet_c₀,
      typeFourSineProductBarPathJet_c₁,
      typeFourSineProductBarPathJet_c₂, typeFourAngleBarPathJet_c₀,
      typeFourAngleBarPathJet_c₁, typeFourAngleBarPathJet_c₂,
      SomeHasTwoJet.neg, SomeHasTwoJet.mul] <;>
    ring)

private opaque foldAngleCorrectionBarPathJet_c₀ (q : Fin 3 → ℝ) :
    (foldAngleCorrectionBarPathJet q).c₀ = -16 * Real.pi := by
  fold_path_coeff

private opaque foldAngleCorrectionBarPathJet_c₁ (q : Fin 3 → ℝ) :
    (foldAngleCorrectionBarPathJet q).c₁ = -32 * Real.pi ^ 2 := by
  fold_path_coeff

private opaque foldAngleCorrectionBarPathJet_c₂ (q : Fin 3 → ℝ) :
    (foldAngleCorrectionBarPathJet q).c₂ =
      -16 * (2 * Real.pi ^ 3 + 4 * Real.pi + q 0) := by
  fold_path_coeff

private opaque foldAngleCorrectionBar_physical_twoJet (q : Fin 3 → ℝ) :
    HasTwoJet (fun s =>
      foldAngleCorrectionBar s (physicalZ q s))
      (-16 * Real.pi) (-32 * Real.pi ^ 2)
      (-16 * (2 * Real.pi ^ 3 + 4 * Real.pi + q 0)) := by
  let h := foldAngleCorrectionBarPathJet q
  have hj := h.jet
  convert hj using 1
  · exact (foldAngleCorrectionBarPathJet_c₀ q).symm
  · exact (foldAngleCorrectionBarPathJet_c₁ q).symm
  · exact (foldAngleCorrectionBarPathJet_c₂ q).symm

macro "r_coord_path_coeff" : tactic =>
  `(tactic|
    simp [rCoordPathJet, physicalASomeJet, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul] <;>
    ring)

private opaque rCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (rCoordPathJet q).c₀ = 2 := by
  r_coord_path_coeff

private opaque rCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (rCoordPathJet q).c₁ = 5 * Real.pi / 12 := by
  r_coord_path_coeff

private opaque rCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (rCoordPathJet q).c₂ =
      (43 * Real.pi ^ 2 + 1056) / 144 := by
  r_coord_path_coeff

macro "e_coord_path_coeff" : tactic =>
  `(tactic|
    simp [eCoordPathJet, physicalZSomeJet, physicalASomeJet,
      physicalBSomeJet, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul] <;>
    (try field_simp [Real.pi_ne_zero]) <;>
    ring)

private opaque eCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (eCoordPathJet q).c₀ = Real.pi / 2 := by
  e_coord_path_coeff

private opaque eCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (eCoordPathJet q).c₁ = 7 * Real.pi ^ 2 / 12 := by
  e_coord_path_coeff

private opaque eCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (eCoordPathJet q).c₂ =
      (295 * Real.pi ^ 3 - 14256 * Real.pi + 108 * q 0 +
        1296 * q 1) / 216 := by
  e_coord_path_coeff

macro "w_coord_path_coeff" : tactic =>
  `(tactic|
    simp [wCoordPathJet, rCoordPathJet_c₀, rCoordPathJet_c₁,
      rCoordPathJet_c₂, SomeHasTwoJet.id, SomeHasTwoJet.mul] <;>
    ring)

private opaque wCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (wCoordPathJet q).c₀ = 0 := by
  w_coord_path_coeff

private opaque wCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (wCoordPathJet q).c₁ = 2 := by
  w_coord_path_coeff

private opaque wCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (wCoordPathJet q).c₂ = 5 * Real.pi / 12 := by
  w_coord_path_coeff

macro "v_coord_path_coeff" : tactic =>
  `(tactic|
    simp [vCoordPathJet, rCoordPathJet_c₀, rCoordPathJet_c₁,
      rCoordPathJet_c₂, eCoordPathJet_c₀, eCoordPathJet_c₁,
      eCoordPathJet_c₂, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.mul] <;>
    ring)

private opaque vCoordPathJet_c₀ (q : Fin 3 → ℝ) :
    (vCoordPathJet q).c₀ = 0 := by
  v_coord_path_coeff

private opaque vCoordPathJet_c₁ (q : Fin 3 → ℝ) :
    (vCoordPathJet q).c₁ = 2 := by
  v_coord_path_coeff

private opaque vCoordPathJet_c₂ (q : Fin 3 → ℝ) :
    (vCoordPathJet q).c₂ = 11 * Real.pi / 12 := by
  v_coord_path_coeff

macro "four_increment_bar2_path_coeff" : tactic =>
  `(tactic|
    simp [typeFourAngleIncrementBar2PathJet, aCoordPathJet_c₀,
      aCoordPathJet_c₁, aCoordPathJet_c₂, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, physicalZSomeJet,
      physicalZ_eq, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul,
      SomeHasTwoJet.div, SomeHasTwoJet.sq,
      atanQuotientSqRemainder_zero] <;>
    norm_num <;>
    ring)

private opaque typeFourAngleIncrementBar2PathJet_c₀
    (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementBar2PathJet q).c₀ = -2 * Real.pi := by
  four_increment_bar2_path_coeff

private opaque typeFourAngleIncrementBar2PathJet_c₁
    (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementBar2PathJet q).c₁ =
      -4 * Real.pi ^ 2 := by
  four_increment_bar2_path_coeff

private opaque typeFourAngleIncrementBar2PathJet_c₂
    (q : Fin 3 → ℝ) :
    (typeFourAngleIncrementBar2PathJet q).c₂ =
      -2 * (7 * Real.pi ^ 3 - 3 * Real.pi + 3 * q 0) / 3 := by
  four_increment_bar2_path_coeff

macro "four_angle_bar2_path_coeff" : tactic =>
  `(tactic|
    simp [typeFourAngleBar2PathJet, densityCubeQuotientPathJet_c₀,
      densityCubeQuotientPathJet_c₁,
      densityCubeQuotientPathJet_c₂, densityPathJet_c₀,
      densityPathJet_c₁, densityPathJet_c₂,
      typeFourAngleIncrementBar2PathJet_c₀,
      typeFourAngleIncrementBar2PathJet_c₁,
      typeFourAngleIncrementBar2PathJet_c₂, physicalZSomeJet,
      SomeHasTwoJet.const, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.mul] <;>
    norm_num <;>
    ring)

private opaque typeFourAngleBar2PathJet_c₀ (q : Fin 3 → ℝ) :
    (typeFourAngleBar2PathJet q).c₀ = 6 * Real.pi := by
  four_angle_bar2_path_coeff

private opaque typeFourAngleBar2PathJet_c₁ (q : Fin 3 → ℝ) :
    (typeFourAngleBar2PathJet q).c₁ = 16 * Real.pi ^ 2 := by
  four_angle_bar2_path_coeff

private opaque typeFourAngleBar2PathJet_c₂ (q : Fin 3 → ℝ) :
    (typeFourAngleBar2PathJet q).c₂ =
      2 * (35 * Real.pi ^ 3 - Real.pi + 9 * q 0) / 3 := by
  four_angle_bar2_path_coeff

macro "three_increment_bar2_path_coeff" : tactic =>
  `(tactic|
    simp [typeThreeAngleIncrementBar2PathJet, rCoordPathJet_c₀,
      rCoordPathJet_c₁, rCoordPathJet_c₂, eCoordPathJet_c₀,
      eCoordPathJet_c₁, eCoordPathJet_c₂, wCoordPathJet_c₀,
      wCoordPathJet_c₁, wCoordPathJet_c₂, vCoordPathJet_c₀,
      vCoordPathJet_c₁, vCoordPathJet_c₂, physicalZ_eq,
      physicalA_eq, physicalB_eq, eCoord, wCoord, vCoord, rCoord,
      SomeHasTwoJet.const, SomeHasTwoJet.id, SomeHasTwoJet.add,
      SomeHasTwoJet.sub, SomeHasTwoJet.mul, SomeHasTwoJet.div,
      SomeHasTwoJet.sq,
      atanQuotientSqRemainder_zero] <;>
    norm_num <;>
    ring)

private opaque typeThreeAngleIncrementBar2PathJet_c₀
    (q : Fin 3 → ℝ) :
    (typeThreeAngleIncrementBar2PathJet q).c₀ = -4 * Real.pi := by
  three_increment_bar2_path_coeff

private opaque typeThreeAngleIncrementBar2PathJet_c₁
    (q : Fin 3 → ℝ) :
    (typeThreeAngleIncrementBar2PathJet q).c₁ =
      -22 * Real.pi ^ 2 / 3 := by
  three_increment_bar2_path_coeff

private opaque typeThreeAngleIncrementBar2PathJet_c₂
    (q : Fin 3 → ℝ) :
    (typeThreeAngleIncrementBar2PathJet q).c₂ =
      -(7285 * Real.pi ^ 3 - 222336 * Real.pi + 1728 * q 0 +
        20736 * q 1) / 432 := by
  three_increment_bar2_path_coeff

macro "three_angle_bar2_path_coeff" : tactic =>
  `(tactic|
    simp [typeThreeAngleBar2PathJet, densityCubeQuotientPathJet_c₀,
      densityCubeQuotientPathJet_c₁,
      densityCubeQuotientPathJet_c₂, densityPathJet_c₀,
      densityPathJet_c₁, densityPathJet_c₂, rCoordPathJet_c₀,
      rCoordPathJet_c₁, rCoordPathJet_c₂, eCoordPathJet_c₀,
      eCoordPathJet_c₁, eCoordPathJet_c₂, wCoordPathJet_c₀,
      wCoordPathJet_c₁, wCoordPathJet_c₂,
      typeThreeAngleIncrementBar2PathJet_c₀,
      typeThreeAngleIncrementBar2PathJet_c₁,
      typeThreeAngleIncrementBar2PathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul] <;>
    norm_num <;>
    ring)

private opaque typeThreeAngleBar2PathJet_c₀ (q : Fin 3 → ℝ) :
    (typeThreeAngleBar2PathJet q).c₀ = 12 * Real.pi := by
  three_angle_bar2_path_coeff

private opaque typeThreeAngleBar2PathJet_c₁ (q : Fin 3 → ℝ) :
    (typeThreeAngleBar2PathJet q).c₁ = 24 * Real.pi ^ 2 := by
  three_angle_bar2_path_coeff

private opaque typeThreeAngleBar2PathJet_c₂ (q : Fin 3 → ℝ) :
    (typeThreeAngleBar2PathJet q).c₂ =
      (7427 * Real.pi ^ 3 + 238464 * Real.pi + 5184 * q 0 -
        20736 * q 1) / 432 := by
  three_angle_bar2_path_coeff

macro "area_denominator_path_coeff" : tactic =>
  `(tactic|
    simp [areaDenominatorPathJet, yCoordPathJet_c₀,
      yCoordPathJet_c₁, yCoordPathJet_c₂, wCoordPathJet_c₀,
      wCoordPathJet_c₁, wCoordPathJet_c₂, vCoordPathJet_c₀,
      vCoordPathJet_c₁, vCoordPathJet_c₂, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.mul,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque areaDenominatorPathJet_c₀ (q : Fin 3 → ℝ) :
    (areaDenominatorPathJet q).c₀ = 2 := by
  area_denominator_path_coeff

private opaque areaDenominatorPathJet_c₁ (q : Fin 3 → ℝ) :
    (areaDenominatorPathJet q).c₁ = 0 := by
  area_denominator_path_coeff

private opaque areaDenominatorPathJet_c₂ (q : Fin 3 → ℝ) :
    (areaDenominatorPathJet q).c₂ = 30 := by
  area_denominator_path_coeff

macro "k_eval_path_coeff" : tactic =>
  `(tactic|
    simp [KEvalPathJet, physicalASomeJet, SomeHasTwoJet.const,
      SomeHasTwoJet.id, SomeHasTwoJet.add, SomeHasTwoJet.sub,
      SomeHasTwoJet.mul, SomeHasTwoJet.sq, id_eq] <;>
    norm_num <;>
    ring)

private opaque KEvalPathJet_c₀ (q : Fin 3 → ℝ) :
    (KEvalPathJet q).c₀ = 4 := by
  k_eval_path_coeff

private opaque KEvalPathJet_c₁ (q : Fin 3 → ℝ) :
    (KEvalPathJet q).c₁ = 10 * Real.pi / 3 := by
  k_eval_path_coeff

private opaque KEvalPathJet_c₂ (q : Fin 3 → ℝ) :
    (KEvalPathJet q).c₂ =
      (197 * Real.pi ^ 2 + 4224) / 72 := by
  k_eval_path_coeff

macro "area_pi_weight_path_coeff" : tactic =>
  `(tactic|
    simp [areaPiWeightPathJet, KEvalPathJet_c₀, KEvalPathJet_c₁,
      KEvalPathJet_c₂, wCoordPathJet_c₀, wCoordPathJet_c₁,
      wCoordPathJet_c₂, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.mul, SomeHasTwoJet.div,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque areaPiWeightPathJet_c₀ (q : Fin 3 → ℝ) :
    (areaPiWeightPathJet q).c₀ = 8 := by
  area_pi_weight_path_coeff

private opaque areaPiWeightPathJet_c₁ (q : Fin 3 → ℝ) :
    (areaPiWeightPathJet q).c₁ = 20 * Real.pi / 3 := by
  area_pi_weight_path_coeff

private opaque areaPiWeightPathJet_c₂ (q : Fin 3 → ℝ) :
    (areaPiWeightPathJet q).c₂ =
      (197 * Real.pi ^ 2 + 1344) / 36 := by
  area_pi_weight_path_coeff

macro "half_cos_endpoint_coeff" : tactic =>
  `(tactic|
    simp [halfCosJet, wCoordPathJet_c₀, wCoordPathJet_c₁,
      wCoordPathJet_c₂, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.div,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque halfCosIdJet_c₀ :
    (halfCosJet SomeHasTwoJet.id).c₀ = 1 := by
  half_cos_endpoint_coeff

private opaque halfCosIdJet_c₁ :
    (halfCosJet SomeHasTwoJet.id).c₁ = 0 := by
  half_cos_endpoint_coeff

private opaque halfCosIdJet_c₂ :
    (halfCosJet SomeHasTwoJet.id).c₂ = -2 := by
  half_cos_endpoint_coeff

private opaque halfCosWPathJet_c₀ (q : Fin 3 → ℝ) :
    (halfCosJet (wCoordPathJet q)).c₀ = 1 := by
  half_cos_endpoint_coeff

private opaque halfCosWPathJet_c₁ (q : Fin 3 → ℝ) :
    (halfCosJet (wCoordPathJet q)).c₁ = 0 := by
  half_cos_endpoint_coeff

private opaque halfCosWPathJet_c₂ (q : Fin 3 → ℝ) :
    (halfCosJet (wCoordPathJet q)).c₂ = -8 := by
  half_cos_endpoint_coeff

macro "area_path_coeff" : tactic =>
  `(tactic|
    simp [areaAngleCorrectionBarPathJet, areaDenominatorPathJet_c₀,
      areaDenominatorPathJet_c₁, areaDenominatorPathJet_c₂,
      halfCosIdJet_c₀, halfCosIdJet_c₁, halfCosIdJet_c₂,
      halfCosWPathJet_c₀, halfCosWPathJet_c₁,
      halfCosWPathJet_c₂, typeThreeAngleBar2PathJet_c₀,
      typeThreeAngleBar2PathJet_c₁, typeThreeAngleBar2PathJet_c₂,
      typeFourAngleBar2PathJet_c₀, typeFourAngleBar2PathJet_c₁,
      typeFourAngleBar2PathJet_c₂, areaPiWeightPathJet_c₀,
      areaPiWeightPathJet_c₁, areaPiWeightPathJet_c₂,
      physicalZSomeJet, SomeHasTwoJet.const,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul,
      SomeHasTwoJet.sq] <;>
    norm_num <;>
    ring)

private opaque areaAngleCorrectionBarPathJet_c₀ (q : Fin 3 → ℝ) :
    (areaAngleCorrectionBarPathJet q).c₀ = 64 * Real.pi := by
  area_path_coeff

private opaque areaAngleCorrectionBarPathJet_c₁ (q : Fin 3 → ℝ) :
    (areaAngleCorrectionBarPathJet q).c₁ =
      256 * Real.pi ^ 2 / 3 := by
  area_path_coeff

private opaque areaAngleCorrectionBarPathJet_c₂ (q : Fin 3 → ℝ) :
    (areaAngleCorrectionBarPathJet q).c₂ =
      -(2245 * Real.pi ^ 3 - 395712 * Real.pi -
        6912 * q 0 + 20736 * q 1) / 108 := by
  area_path_coeff

private opaque areaAngleCorrectionBar_physical_twoJet (q : Fin 3 → ℝ) :
    HasTwoJet (fun s =>
      areaAngleCorrectionBar s (physicalZ q s) (physicalA q s)
        (physicalB q s))
      (64 * Real.pi) (256 * Real.pi ^ 2 / 3)
      (-(2245 * Real.pi ^ 3 - 395712 * Real.pi -
        6912 * q 0 + 20736 * q 1) / 108) := by
  let h := areaAngleCorrectionBarPathJet q
  have hj := h.jet
  convert hj using 1
  · exact (areaAngleCorrectionBarPathJet_c₀ q).symm
  · exact (areaAngleCorrectionBarPathJet_c₁ q).symm
  · exact (areaAngleCorrectionBarPathJet_c₂ q).symm

/-- Along the physical quadratically rescaled tangent-centered path, the
regularized third row has a genuine exact two-jet. -/
opaque regularizedThirdRow_physical_twoJet (q : Fin 3 → ℝ) :
    HasTwoJet (fun s =>
      regularizedThirdRow s
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2) Real.pi)
      0 0
      (Real.pi * (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
        31104 * q 2 - 146105856) / 7776) := by
  let hpoly : SomeHasTwoJet (fun s =>
      H3hatPolynomial s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) :=
    ⟨0, 32 * Real.pi ^ 2,
      (1193 * Real.pi ^ 5 + 3656952 * Real.pi ^ 3 -
        31104 * Real.pi * q 2 - 172606464 * Real.pi +
        1492992 * q 1) / 7776,
      H3hatPolynomial_physical_twoJet q⟩
  let harea : SomeHasTwoJet (fun s =>
      areaAngleCorrectionBar s (physicalZ q s) (physicalA q s)
        (physicalB q s)) :=
    ⟨64 * Real.pi, 256 * Real.pi ^ 2 / 3,
      -(2245 * Real.pi ^ 3 - 395712 * Real.pi -
        6912 * q 0 + 20736 * q 1) / 108,
      areaAngleCorrectionBar_physical_twoJet q⟩
  let hfold : SomeHasTwoJet (fun s =>
      foldAngleCorrectionBar s (physicalZ q s)) :=
    ⟨-16 * Real.pi, -32 * Real.pi ^ 2,
      -16 * (2 * Real.pi ^ 3 + 4 * Real.pi + q 0),
      foldAngleCorrectionBar_physical_twoJet q⟩
  let two := SomeHasTwoJet.const 2
  let three := SomeHasTwoJet.const 3
  let four := SomeHasTwoJet.const 4
  let hs := SomeHasTwoJet.id
  let hz := physicalZSomeJet q
  have hthree0 : three.c₀ ≠ 0 := by
    rw [← three.jet.value]
    norm_num
  let h := (hpoly.add harea).add
    ((four.sub (((two.mul hz).mul hs).div three hthree0)).mul hfold)
  have hj := h.jet
  change HasTwoJet (fun s =>
    regularizedThirdRow s (physicalZ q s) (physicalA q s) (physicalB q s)
      Real.pi) _ _ _ at hj
  convert hj using 1
  · rfl
  · simp [h, hpoly, harea, hfold, two, three, four, hs, hz,
      physicalZSomeJet, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul,
      SomeHasTwoJet.div]
    ring
  · simp [h, hpoly, harea, hfold, two, three, four, hs, hz,
      physicalZSomeJet, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul,
      SomeHasTwoJet.div]
    ring
  · simp [h, hpoly, harea, hfold, two, three, four, hs, hz,
      physicalZSomeJet, SomeHasTwoJet.const, SomeHasTwoJet.id,
      SomeHasTwoJet.add, SomeHasTwoJet.sub, SomeHasTwoJet.mul,
      SomeHasTwoJet.div]
    ring

private theorem regularizedThirdRowData_c₀ (q : Fin 3 → ℝ) :
    (JointJetData.regularizedThirdRowData.jet q).c₀ = 0 := by
  rw [← (JointJetData.regularizedThirdRowData.jet q).jet.value]
  simpa only [physicalZ, physicalA, physicalB] using
    (regularizedThirdRow_physical_twoJet q).value

private theorem regularizedThirdRowData_c₁ (q : Fin 3 → ℝ) :
    (JointJetData.regularizedThirdRowData.jet q).c₁ = 0 := by
  have hj := hasDerivAt_zero_of_hasTwoJet
    (JointJetData.regularizedThirdRowData.jet q).jet
  have hk := hasDerivAt_zero_of_hasTwoJet
    (regularizedThirdRow_physical_twoJet q)
  simpa only [physicalZ, physicalA, physicalB] using hj.unique hk

private theorem regularizedThirdRowData_c₂ (q : Fin 3 → ℝ) :
    (JointJetData.regularizedThirdRowData.jet q).c₂ =
      Real.pi * (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
        31104 * q 2 - 146105856) / 7776 := by
  have hj : HasTwoJet (fun s =>
      regularizedThirdRow s (physicalZ q s) (physicalA q s)
        (physicalB q s) Real.pi) 0 0
      (JointJetData.regularizedThirdRowData.jet q).c₂ := by
    convert (JointJetData.regularizedThirdRowData.jet q).jet using 1
    · exact (regularizedThirdRowData_c₀ q).symm
    · exact (regularizedThirdRowData_c₁ q).symm
  have hj' : HasTwoJet (fun s =>
      regularizedThirdRow s
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2) Real.pi)
      0 0 (JointJetData.regularizedThirdRowData.jet q).c₂ := by
    simpa only [physicalZ, physicalA, physicalB] using hj
  exact c₂_eq_of_hasTwoJet_same hj'
    (regularizedThirdRow_physical_twoJet q)

/-- The totalized third-row quotient is jointly continuous in the scale and
rescaled coordinates at every cusp endpoint. -/
theorem continuousAt_regularizedThirdRow_physical_div_sq_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      if p.1 = 0 then
        Real.pi * (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
          31104 * p.2 2 - 146105856) / 7776
      else
        regularizedThirdRow p.1
          (tangentCenteredPoint p.1 (fun j => p.1 ^ 2 * p.2 j) 0)
          (tangentCenteredPoint p.1 (fun j => p.1 ^ 2 * p.2 j) 1)
          (tangentCenteredPoint p.1 (fun j => p.1 ^ 2 * p.2 j) 2)
          Real.pi / p.1 ^ 2) (0, q) := by
  apply (JointJetData.regularizedThirdRowData.continuousAt_remainder q).congr_of_eventuallyEq
  filter_upwards [JointJetData.regularizedThirdRowData.eventually_eq_joint q]
    with p hp
  by_cases hs : p.1 = 0
  · rw [hs]
    simp only [if_pos]
    simp only [regularizedThirdRowData_c₂ p.2,
      (JointJetData.regularizedThirdRowData.jet p.2).jet.remainder_zero]
  · simp only [hs, if_false]
    change regularizedThirdRow p.1 (physicalZ p.2 p.1)
        (physicalA p.2 p.1) (physicalB p.2 p.1) Real.pi /
      p.1 ^ 2 =
        (JointJetData.regularizedThirdRowData.jet p.2).jet.remainder p.1
    rw [hp]
    simp only [regularizedThirdRowData_c₀ p.2,
      regularizedThirdRowData_c₁ p.2, zero_add, mul_zero]
    field_simp

end

end NearOneRegularizedThirdRow
