/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRegularizedThirdRow
/-!
# Exact tangent data at the near-one cusp

This module computes the parameter derivative of the complete normalized
near-one root map at the exact cusp and verifies the resulting tangent equation.
It establishes only the formal tangent data; it does not assert existence of a
solution branch through the cusp.
-/


namespace NearOneRegularizedThirdRow
open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real
open Filter Asymptotics
set_option maxRecDepth 10000

private lemma hasDerivAt_sq_mul_of_continuousAt
    {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    HasDerivAt (fun s : ℝ => s ^ 2 * g s) 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
    sub_zero, smul_zero]
  simpa only [mul_one] using
    (isLittleO_pow_id (by norm_num : 1 < (2 : ℕ))).mul_isBigO hg.isBigO

private theorem hA (z : ℝ) : HasDerivAt (fun s => aCoord s z) z 0 := by
  unfold aCoord
  convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).mul_const z) using 1 <;> (try rfl)
  simp

private theorem hR (a : ℝ) : HasDerivAt (fun s => rCoord s a) a 0 := by
  unfold rCoord
  convert (hasDerivAt_const (x := 0) (c := (2 : ℝ))).add
    ((hasDerivAt_id 0).mul_const a) using 1 <;> (try rfl)
  simp

private theorem hE (z a b : ℝ) : HasDerivAt (fun s => eCoord s z a b) b 0 := by
  unfold eCoord
  convert (hasDerivAt_const (x := 0) (c := 6*a-2*z)).add
    ((hasDerivAt_id 0).mul_const b) using 1 <;> (try rfl)
  simp

private theorem hY (z : ℝ) : HasDerivAt (fun s => yCoord s z) 1 0 := by
  unfold yCoord
  convert (hasDerivAt_id 0).mul (hA z) using 1 <;> (try rfl)
  simp [aCoord]

private theorem hW (a : ℝ) : HasDerivAt (fun s => wCoord s a) 2 0 := by
  unfold wCoord
  convert (hasDerivAt_id 0).mul (hR a) using 1 <;> (try rfl)
  simp [rCoord]

private theorem hV (z a b : ℝ) : HasDerivAt (fun s => vCoord s z a b) 2 0 := by
  unfold vCoord
  convert (hasDerivAt_id 0).mul
    ((hR a).add ((hasDerivAt_id 0).mul (hE z a b))) using 1 <;>
    (try rfl)
  simp [rCoord, eCoord]

private theorem hD4 (z : ℝ) :
    HasDerivAt (fun s => 1 + s * yCoord s z) 0 0 := by
  convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).mul (hY z)) using 1 <;> (try rfl)
  simp [aCoord, yCoord]

private theorem hD3 (z a b : ℝ) :
    HasDerivAt (fun s => 1 + wCoord s a * vCoord s z a b) 0 0 := by
  convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hW a).mul (hV z a b)) using 1 <;> (try rfl)
  simp [rCoord, eCoord, wCoord, vCoord]

private theorem hDensityCube (z : ℝ) :
    HasDerivAt (fun s => densityCubeQuotient s z) (2*z^2) 0 := by
  unfold densityCubeQuotient
  have hn := (hasDerivAt_const (x := 0) (c := 2*z)).mul
    ((hasDerivAt_const (x := 0) (c := (2 : ℝ))).add ((hasDerivAt_id 0).mul_const z))
  have hd := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hasDerivAt_id 0).pow 2)).mul
    ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub ((hY z).pow 2))
  convert hn.div hd (by norm_num [yCoord, aCoord]) using 1 <;> (try rfl)
  simp [aCoord, yCoord]
  ring_nf

private theorem hHalfCosZero : HasDerivAt halfCos 0 0 := by
  unfold halfCos
  convert ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub
    ((hasDerivAt_id 0).pow 2)).div
    ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
      ((hasDerivAt_id 0).pow 2)) (by norm_num) using 1 <;> (try rfl)
  simp

private theorem hDensity (z : ℝ) : HasDerivAt (fun s => density s z) 0 0 := by
  have hout : HasDerivAt halfCos 0 (yCoord 0 z) := by
    simpa [yCoord, aCoord] using hHalfCosZero
  have hycos : HasDerivAt (fun s => halfCos (yCoord s z)) 0 0 := by
    convert hout.comp 0 (hY z) using 1 <;> (try rfl)
    simp
  unfold density
  convert hHalfCosZero.div hycos
    (by simp [halfCos, yCoord, aCoord]) using 1 <;> (try rfl)
  simp [halfCos, yCoord, aCoord]

private theorem hAtanQuotient : HasDerivAt atanQuotient 0 0 := by
  rw [show atanQuotient = fun x : ℝ => 1 + x^2 * atanQuotientSqRemainder x by
    funext x; exact atanQuotient_eq_one_add_sq_mul x]
  convert (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    (hasDerivAt_sq_mul_of_continuousAt
      continuous_atanQuotientSqRemainder.continuousAt) using 1 <;> (try rfl)
  simp


private theorem hFourIncBar2 (z : ℝ) :
    HasDerivAt (fun s => typeFourAngleIncrementBar2 s z) (-2*z^2) 0 := by
  let q : ℝ → ℝ := fun s => s^2*z/(1+s*yCoord s z)
  let g : ℝ → ℝ := fun s =>
    (2*z/(1+s*yCoord s z)) * (z^2/(1+s*yCoord s z)^2) *
      atanQuotientSqRemainder (q s)
  have hq : ContinuousAt q 0 := by
    dsimp [q, yCoord, aCoord]
    fun_prop (disch := norm_num)
  have hg : ContinuousAt g 0 := by
    dsimp [g, yCoord, aCoord]
    fun_prop (disch := first | exact hq | norm_num)
  have hn := hasDerivAt_sq_mul_of_continuousAt hg
  have hb : HasDerivAt
      (fun s => -(2*z/(1+s*yCoord s z) * aCoord s z)) (-2*z^2) 0 := by
    convert (((hasDerivAt_const (x := 0) (c := 2*z)).div (hD4 z)
      (by norm_num [yCoord, aCoord])).mul (hA z)).neg using 1 <;> (try rfl)
    simp [aCoord, yCoord]
    ring_nf
  rw [show (fun s => typeFourAngleIncrementBar2 s z) =
      fun s => -(2*z/(1+s*yCoord s z) * aCoord s z) + s^2*g s by
    funext s
    simp only [typeFourAngleIncrementBar2, q, g]
    simp [div_eq_mul_inv]
    ring]
  convert hb.add hn using 1 <;> (try rfl)
  simp

private theorem hThreeIncBar2 (z a b : ℝ) :
    HasDerivAt (fun s => typeThreeAngleIncrementBar2 s z a b)
      (-8*(24*a^2 - 14*a*z + b + 2*z^2)) 0 := by
  let q : ℝ → ℝ := fun s =>
    s^2 * eCoord s z a b / (1+wCoord s a*vCoord s z a b)
  let g : ℝ → ℝ := fun s =>
    (2*eCoord s z a b/(1+wCoord s a*vCoord s z a b)) *
      (eCoord s z a b^2/(1+wCoord s a*vCoord s z a b)^2) *
        atanQuotientSqRemainder (q s)
  have hq : ContinuousAt q 0 := by
    dsimp [q, eCoord, wCoord, vCoord, rCoord]
    fun_prop (disch := norm_num)
  have hg : ContinuousAt g 0 := by
    dsimp [g, eCoord, wCoord, vCoord, rCoord]
    fun_prop (disch := first | exact hq | norm_num)
  have hn := hasDerivAt_sq_mul_of_continuousAt hg
  have hrse : HasDerivAt
      (fun s => rCoord s a + s*eCoord s z a b) (7*a-2*z) 0 := by
    convert (hR a).add ((hasDerivAt_id 0).mul (hE z a b)) using 1 <;>
      (try rfl)
    simp [eCoord]
    ring_nf
  have hb : HasDerivAt
      (fun s => -(2*eCoord s z a b/(1+wCoord s a*vCoord s z a b) *
        rCoord s a * (rCoord s a+s*eCoord s z a b)))
      (-8*(24*a^2 - 14*a*z + b + 2*z^2)) 0 := by
    convert (((((hE z a b).const_mul 2).div (hD3 z a b)
      (by norm_num [wCoord, vCoord, rCoord])).mul (hR a)).mul hrse).neg
      using 1 <;> (try rfl)
    simp [rCoord, eCoord, wCoord, vCoord]
    ring_nf
  rw [show (fun s => typeThreeAngleIncrementBar2 s z a b) =
      fun s => -(2*eCoord s z a b/(1+wCoord s a*vCoord s z a b) *
        rCoord s a * (rCoord s a+s*eCoord s z a b)) + s^2*g s by
    funext s
    simp only [typeThreeAngleIncrementBar2, q, g]
    simp [div_eq_mul_inv]
    ring]
  convert hb.add hn using 1 <;> (try rfl)
  simp


private theorem hFourBar2 (z : ℝ) :
    HasDerivAt (fun s => typeFourAngleBar2 s z) (10*z^2) 0 := by
  unfold typeFourAngleBar2
  convert ((((hDensityCube z).mul hAtanQuotient).const_mul 2).add
    ((hDensity z).mul (hFourIncBar2 z))).add
      ((((hasDerivAt_id 0).mul_const z).mul (hDensityCube z)).const_mul 2)
    using 1 <;> (try rfl)
  case e'_8 =>
    ext s
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    ring
  case e'_9 =>
    simp [densityCubeQuotient, density, halfCos, yCoord, aCoord,
      atanQuotient]
    ring_nf

private theorem hThreeBar2 (z a b : ℝ) :
    HasDerivAt (fun s => typeThreeAngleBar2 s z a b)
      (-8*(24*a^2-21*a*z+b+3*z^2)) 0 := by
  have hqw : HasDerivAt (fun s => atanQuotient (wCoord s a)) 0 0 := by
    have hout : HasDerivAt atanQuotient 0 (wCoord 0 a) := by
      simpa [wCoord, rCoord] using hAtanQuotient
    convert hout.comp 0 (hW a) using 1 <;> (try rfl)
    simp
  unfold typeThreeAngleBar2
  convert (((((hDensityCube z).mul (hR a)).mul hqw).const_mul 2).add
    ((hDensity z).mul (hThreeIncBar2 z a b))).add
      (((((hasDerivAt_id 0).mul (hE z a b)).mul (hDensityCube z))).const_mul 2)
    using 1 <;> (try rfl)
  case e'_8 =>
    ext s
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    ring
  case e'_9 =>
    simp [densityCubeQuotient, density, halfCos, yCoord, aCoord,
      rCoord, eCoord, wCoord, atanQuotient]
    ring_nf


private theorem hFourInc (z : ℝ) :
    HasDerivAt (fun s => typeFourAngleIncrement s z) 0 0 := by
  have hq : HasDerivAt
      (fun s => s^2*z/(1+s*yCoord s z)) 0 0 := by
    convert ((((hasDerivAt_id 0).pow 2).mul_const z).div (hD4 z)
      (by norm_num [yCoord, aCoord])) using 1 <;> (try rfl)
    simp
  have haq : HasDerivAt
      (fun s => atanQuotient (s^2*z/(1+s*yCoord s z))) 0 0 := by
    have hout : HasDerivAt atanQuotient 0
        (0^2*z/(1+0*yCoord 0 z)) := by
      simpa [yCoord, aCoord] using hAtanQuotient
    convert hout.comp 0 hq using 1 <;> (try rfl)
    simp
  unfold typeFourAngleIncrement
  convert (((hasDerivAt_const (x := 0) (c := 2*z)).div (hD4 z)
    (by norm_num [yCoord, aCoord])).mul haq) using 1 <;> (try rfl)
  simp [yCoord, aCoord, atanQuotient]

private theorem hFourAngleBar (z : ℝ) :
    HasDerivAt (fun s => typeFourAngleBar s z) 0 0 := by
  unfold typeFourAngleBar
  convert (((((hasDerivAt_id 0).mul (hDensityCube z)).mul
    (Real.hasDerivAt_arctan 0)).const_mul 2).add
      ((hDensity z).mul (hFourInc z))) using 1 <;> (try rfl)
  case e'_8 =>
    ext s
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    ring
  case e'_9 =>
    simp [densityCubeQuotient, density, halfCos, yCoord, aCoord]

private theorem hFoldDen (z : ℝ) :
    HasDerivAt (fun s => foldDenominator s z) 0 0 := by
  unfold foldDenominator
  convert (((hasDerivAt_const (x := 0) (c := (2 : ℝ))).mul
    (((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
      ((hasDerivAt_id 0).pow 2)).pow 2)).mul
        ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hY z).pow 2)))
    using 1 <;> (try rfl)
  simp [yCoord, aCoord]

private theorem hFourSineProduct (z : ℝ) :
    HasDerivAt (fun s => typeFourSineProductBar s z) (4*z) 0 := by
  unfold typeFourSineProductBar
  have hd := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).pow 2)).mul
      ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hY z).pow 2))
  convert ((hA z).const_mul 4).div hd
    (by norm_num [yCoord, aCoord]) using 1 <;> (try rfl)
  simp [yCoord, aCoord]

private theorem hFoldCorrection (z : ℝ) :
    HasDerivAt (fun s => foldAngleCorrectionBar s z) (-16*z^2) 0 := by
  unfold foldAngleCorrectionBar
  convert (((hFoldDen z).mul (hFourSineProduct z)).mul (hFourAngleBar z)).neg
    using 1 <;> (try rfl)
  case e'_8 =>
    ext s
    simp only [Pi.mul_apply, Pi.neg_apply]
    ring
  case e'_9 =>
    simp [foldDenominator, typeFourSineProductBar, typeFourAngleBar,
      typeFourAngleIncrement, densityCubeQuotient, density, halfCos,
      yCoord, aCoord, atanQuotient]
    ring_nf


private theorem hAreaPiWeight (a : ℝ) :
    HasDerivAt (fun s => areaPiWeight s a) (16*a) 0 := by
  have hk : HasDerivAt (fun s => (NearOneNormalizedFlow.K a).eval s) (8*a) 0 := by
    convert (NearOneNormalizedFlow.K a).hasDerivAt 0 using 1 <;> (try rfl)
    simp [NearOneNormalizedFlow.K, NearOneNormalizedFlow.R,
      derivative_pow]
    ring_nf
  have hd := (((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).pow 2)).pow 2).mul
      (((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hW a).pow 2)).pow 2)
  unfold areaPiWeight
  convert (hk.const_mul 2).div hd
    (by norm_num [wCoord, rCoord]) using 1 <;> (try rfl)
  simp [wCoord, rCoord, NearOneNormalizedFlow.K,
    NearOneNormalizedFlow.R]
  ring_nf

private theorem hAreaDen (z a b : ℝ) :
    HasDerivAt (fun s => areaDenominator s z a b) 0 0 := by
  let h1 := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).pow 2)).pow 2
  let hw := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hW a).pow 2)).pow 2
  let hy := (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hY z).pow 2)
  let hv := (hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hV z a b).pow 2)
  unfold areaDenominator
  convert (((((hasDerivAt_const (x := 0) (c := (2 : ℝ))).mul h1).mul
    hw).mul hy).mul hv) using 1 <;> (try rfl)
  simp [wCoord, vCoord, yCoord, rCoord, aCoord, eCoord]

private theorem hAreaCorrection (z a b : ℝ) :
    HasDerivAt (fun s => areaAngleCorrectionBar s z a b)
      (-16*(48*a^2-50*a*z+2*b+11*z^2)) 0 := by
  have hwcos : HasDerivAt (fun s => halfCos (wCoord s a)) 0 0 := by
    have hout : HasDerivAt halfCos 0 (wCoord 0 a) := by
      simpa [wCoord, rCoord] using hHalfCosZero
    convert hout.comp 0 (hW a) using 1 <;> (try rfl)
    simp
  have htwo : HasDerivAt
      (fun s => 2*halfCos s^2*typeThreeAngleBar2 s z a b)
      (-16*(24*a^2-21*a*z+b+3*z^2)) 0 := by
    convert (((hHalfCosZero.pow 2).mul (hThreeBar2 z a b)).const_mul 2)
      using 1 <;> (try rfl)
    case e'_8 =>
      ext s
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
    case e'_9 =>
      simp [halfCos, typeThreeAngleBar2, densityCubeQuotient, density,
        typeThreeAngleIncrementBar2, yCoord, aCoord, rCoord, eCoord,
        wCoord, vCoord, atanQuotient]
      ring_nf
  have hfour : HasDerivAt
      (fun s => (1+halfCos (wCoord s a))^2*typeFourAngleBar2 s z)
      (40*z^2) 0 := by
    convert (((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add hwcos).pow 2).mul
      (hFourBar2 z) using 1 <;> (try rfl)
    simp [halfCos, typeFourAngleBar2, densityCubeQuotient, density,
      typeFourAngleIncrementBar2, yCoord, aCoord, wCoord, rCoord,
      atanQuotient]
    ring_nf
  have hinner : HasDerivAt
      (fun s => 2*halfCos s^2*typeThreeAngleBar2 s z a b -
        (1+halfCos (wCoord s a))^2*typeFourAngleBar2 s z +
        4*z*areaPiWeight s a)
      (-8*(48*a^2-50*a*z+2*b+11*z^2)) 0 := by
    convert (htwo.sub hfour).add
      ((hAreaPiWeight a).const_mul (4*z)) using 1 <;> (try rfl)
    simp
    ring_nf
  unfold areaAngleCorrectionBar
  convert (hAreaDen z a b).mul hinner using 1 <;> (try rfl)
  simp [areaDenominator, halfCos, wCoord, vCoord, yCoord,
    rCoord, eCoord, aCoord]
  ring_nf


private theorem hPolynomialCusp :
    HasDerivAt
      (fun s => NearOneNormalizedFlow.H3hatPolynomial s Real.pi
        (5*Real.pi/12) (-44+19*Real.pi^2/24) Real.pi)
      (-(247*Real.pi^4-75648*Real.pi^2+3345408)/216) 0 := by
  let p := NearOneNormalizedFlow.thirdRowNumerator Real.pi
    (5*Real.pi/12) (-44+19*Real.pi^2/24) Real.pi
  let q := NearOneNormalizedFlow.normalizedThirdRow Real.pi
    (5*Real.pi/12) (-44+19*Real.pi^2/24) Real.pi
  have hthird : p.derivative.derivative.derivative.eval 0 =
      6 * (-(247*Real.pi^4-75648*Real.pi^2+3345408)/216) := by
    dsimp [p]
    simp [NearOneNormalizedFlow.thirdRowNumerator,
      NearOneNormalizedFlow.areaNumerator,
      NearOneNormalizedFlow.cosineNumerator,
      NearOneNormalizedFlow.foldNumerator,
      NearOneNormalizedFlow.qPrime, NearOneNormalizedFlow.areaL,
      NearOneNormalizedFlow.areaZ, NearOneNormalizedFlow.areaX,
      NearOneNormalizedFlow.W, NearOneNormalizedFlow.U,
      NearOneNormalizedFlow.K, NearOneNormalizedFlow.B,
      NearOneNormalizedFlow.E, NearOneNormalizedFlow.R,
      NearOneNormalizedFlow.A, derivative_pow]
    ring
  have hcoeff : p.derivative.derivative.derivative.coeff 0 =
      6 * p.coeff 3 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    norm_num
    ring
  rw [← Polynomial.coeff_zero_eq_eval_zero, hcoeff] at hthird
  have hpcoeff : p.coeff 3 =
      -(247*Real.pi^4-75648*Real.pi^2+3345408)/216 := by
    linarith
  have hqder : q.derivative.eval 0 = p.coeff 3 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    norm_num
    simp [q, p, NearOneNormalizedFlow.normalizedThirdRow, coeff_divX]
  change HasDerivAt (fun s => q.eval s) _ 0
  convert q.hasDerivAt 0 using 1 <;> (try rfl)
  rw [hqder, hpcoeff]


private theorem hFourSineBar (z : ℝ) :
    HasDerivAt (fun s => typeFourSineBar s z) 0 0 := by
  unfold typeFourSineBar
  have hn := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub
    ((hasDerivAt_id 0).mul (hY z))).const_mul (2*z)
  have hd := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
    ((hasDerivAt_id 0).pow 2)).mul
      ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add ((hY z).pow 2))
  convert hn.div hd
    (by norm_num [yCoord, aCoord]) using 1 <;> (try rfl)
  simp [yCoord, aCoord]

theorem foldRow_hasDerivAt_cusp :
    HasDerivAt (fun s => foldRow s Real.pi Real.pi) (-2*Real.pi^2) 0 := by
  unfold foldRow
  have hsquare : HasDerivAt
      (fun s => s^2*typeFourAngleBar s Real.pi) 0 0 := by
    convert ((hasDerivAt_id 0).pow 2).mul
      (hFourAngleBar Real.pi) using 1 <;> (try rfl)
    simp [typeFourAngleBar, typeFourAngleIncrement, densityCubeQuotient,
      density, halfCos, yCoord, aCoord, atanQuotient]
  convert (hHalfCosZero.mul (hFourSineBar Real.pi)).sub
    ((hFourSineProduct Real.pi).mul
      ((hasDerivAt_const (x := 0) (c := Real.pi/2)).add hsquare)) using 1 <;>
    (try rfl)
  simp [halfCos, typeFourSineBar, typeFourSineProductBar,
    typeFourAngleBar, typeFourAngleIncrement, densityCubeQuotient,
    density, yCoord, aCoord, atanQuotient]
  ring_nf

theorem cosineRow_hasDerivAt_cusp :
    HasDerivAt
      (fun s => (NearOneNormalizedFlow.H2 Real.pi (5*Real.pi/12)
        (-44+19*Real.pi^2/24)).eval s)
      (2*(17*Real.pi^2-1056)/3) 0 := by
  let q := NearOneNormalizedFlow.H2 Real.pi (5*Real.pi/12)
    (-44+19*Real.pi^2/24)
  change HasDerivAt (fun s => q.eval s) _ 0
  convert q.hasDerivAt 0 using 1 <;> (try rfl)
  simp [q, NearOneNormalizedFlow.H2,
    NearOneNormalizedFlow.cosineNumerator,
    NearOneNormalizedFlow.E, NearOneNormalizedFlow.R,
    derivative_pow]
  ring_nf

theorem regularizedThirdRow_hasDerivAt_cusp :
    HasDerivAt
      (fun s => regularizedThirdRow s Real.pi (5*Real.pi/12)
        (-44+19*Real.pi^2/24) Real.pi)
      (-(247*Real.pi^4-63840*Real.pi^2+3041280)/216) 0 := by
  have hfactor : HasDerivAt
      (fun s : ℝ => 4-2*Real.pi*s/3) (-2*Real.pi/3) 0 := by
    convert (hasDerivAt_const (x := 0) (c := (4 : ℝ))).sub
      ((((hasDerivAt_id 0).mul_const Real.pi).const_mul 2).div_const 3)
      using 1 <;> (try rfl)
    case e'_8 =>
      ext s
      simp only [Pi.sub_apply, id_eq]
      ring
    case e'_9 => ring_nf
  unfold regularizedThirdRow
  convert (hPolynomialCusp.add
    (hAreaCorrection Real.pi (5*Real.pi/12)
      (-44+19*Real.pi^2/24))).add
    (hfactor.mul (hFoldCorrection Real.pi)) using 1 <;> (try rfl)
  simp [foldAngleCorrectionBar, foldDenominator,
    typeFourSineProductBar, typeFourAngleBar, typeFourAngleIncrement,
    densityCubeQuotient, density, halfCos, yCoord, aCoord,
    atanQuotient]
  ring_nf

theorem regularizedThirdRow_deriv_cusp :
    deriv
      (fun s => regularizedThirdRow s Real.pi (5*Real.pi/12)
        (-44+19*Real.pi^2/24) Real.pi) 0 =
      -(247*Real.pi^4-63840*Real.pi^2+3041280)/216 :=
  regularizedThirdRow_hasDerivAt_cusp.deriv

noncomputable section

/-- Coordinatewise derivative with respect to the near-one parameter `s` at
`s = 0`, with `pi` and the branch coordinates held fixed. -/
def nearOneParameterDerivative (pi : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => deriv (fun s => nearOneRootMap s pi x i) 0

/-- Exact parameter derivative of the three normalized rows at the cusp. -/
def exactCuspParameterDerivative : Fin 3 → ℝ :=
  ![-2 * Real.pi ^ 2,
    2 * (17 * Real.pi ^ 2 - 1056) / 3,
    -(247 * Real.pi ^ 4 - 63840 * Real.pi ^ 2 + 3041280) / 216]

/-- The actual coordinatewise parameter derivative agrees with its explicit
cusp value. -/
theorem nearOneParameterDerivative_exactCusp :
    nearOneParameterDerivative Real.pi exactCuspPoint =
      exactCuspParameterDerivative := by
  ext i
  fin_cases i
  · simpa [nearOneParameterDerivative, nearOneRootMap, exactCuspPoint,
      exactCuspParameterDerivative] using foldRow_hasDerivAt_cusp.deriv
  · simpa [nearOneParameterDerivative, nearOneRootMap, exactCuspPoint,
      exactCuspParameterDerivative] using cosineRow_hasDerivAt_cusp.deriv
  · simpa [nearOneParameterDerivative, nearOneRootMap, exactCuspPoint,
      exactCuspParameterDerivative] using
        regularizedThirdRow_hasDerivAt_cusp.deriv

/-- Explicit tangent vector forced by the differentiated cusp equations. -/
def exactCuspTangent : Fin 3 → ℝ :=
  ![Real.pi ^ 2,
    (43 * Real.pi ^ 2 + 1056) / 144,
    Real.pi * (295 * Real.pi ^ 2 - 14256) / 216]

/-- The explicit tangent solves the linearized exact cusp equations. -/
theorem exactCuspJacobian_mulVec_exactCuspTangent :
    exactCuspJacobian.mulVec exactCuspTangent +
      exactCuspParameterDerivative = 0 := by
  ext i
  fin_cases i <;>
    simp [exactCuspJacobian, exactCuspTangent,
      exactCuspParameterDerivative] <;>
    ring

/-- The explicit tangent also solves the linearized equations for the actual
near-one Jacobian at the cusp. -/
theorem nearOneJacobian_mulVec_exactCuspTangent :
    (nearOneJacobian 0 Real.pi exactCuspPoint).mulVec exactCuspTangent +
      nearOneParameterDerivative Real.pi exactCuspPoint = 0 := by
  rw [nearOneJacobian_exactCusp, nearOneParameterDerivative_exactCusp]
  exact exactCuspJacobian_mulVec_exactCuspTangent

/-- The exact cusp tangent is the unique solution of the linearized exact cusp
equations. -/
theorem exactCuspTangent_unique
    (v : Fin 3 → ℝ)
    (h : exactCuspJacobian.mulVec v + exactCuspParameterDerivative = 0) :
    v = exactCuspTangent := by
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  simp only [exactCuspJacobian, neg_mul, Matrix.cons_mulVec, dotProduct,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_mul, add_zero, Matrix.cons_val,
    Matrix.empty_mulVec, exactCuspParameterDerivative, neg_add_rev,
    neg_sub, Pi.add_apply, Pi.zero_apply] at h0 h1 h2
  have hv0 : v 0 = Real.pi ^ 2 := by linarith
  have hv1 : v 1 = (43 * Real.pi ^ 2 + 1056) / 144 := by
    rw [hv0] at h1
    linarith
  have hv2 : v 2 =
      Real.pi * (295 * Real.pi ^ 2 - 14256) / 216 := by
    rw [hv0, hv1] at h2
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hpv2 : Real.pi * v 2 =
        Real.pi ^ 2 * (295 * Real.pi ^ 2 - 14256) / 216 := by
      ring_nf at h2 ⊢
      linarith
    apply (mul_left_cancel₀ hpi)
    rw [hpv2]
    ring
  funext i
  fin_cases i
  · simpa [exactCuspTangent] using hv0
  · simpa [exactCuspTangent] using hv1
  · simpa [exactCuspTangent] using hv2

end

end NearOneRegularizedThirdRow
