/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalFourRemainder
import NearOneLocalPredictor

/-!
# Scalar remainder and source-guard gate for two scale-local cells

This module checks the four actual `R₃` arguments and their retained
one-variable twenty-term remainder intervals on the seam and remote stress
cells.  Analytic terms are not substituted into a multivariate polynomial.
-/

namespace NearOneLocalRemainderGate

open NearOneAnalyticSystem NearOneRegularizedThirdRow
open NearOneLocalCoordinates NearOneLocalFourRemainder NearOneLocalThirdSource
open NearOneLocalPredictor
set_option maxRecDepth 10000
noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

private abbrev point (q : ℚ) : QInterval := LeanSuffixReflective.QInterval.point q
private abbrev mul (i j : QInterval) : QInterval :=
  ScalarSuffixCertificate.QInterval.mul i j
private abbrev scale (q : ℚ) (i : QInterval) : QInterval := scaledEnclosure q i

private theorem point_sound (q : ℚ) : (point q).RealContains (q : ℝ) :=
  (LeanSuffixReflective.QInterval.realContains_point q (q : ℝ)).2 rfl

/-- Recenter any rational interval as an explicit midpoint-error budget. -/
theorem realContains_midpoint_error_le {i : QInterval} {x : ℝ}
    (hx : i.RealContains x) :
    |x - ((((i.lo + i.hi) / 2 : ℚ) : ℝ))| ≤
      (((i.hi - i.lo) / 2 : ℚ) : ℝ) := by
  have hvalid : (i.lo : ℝ) ≤ (i.hi : ℝ) := by
    exact_mod_cast i.ordered
  rw [abs_le]
  constructor <;> push_cast <;> linarith [hx.1, hx.2]
private theorem mul_sound {i j : QInterval} {x y : ℝ}
    (hx : i.RealContains x) (hy : j.RealContains y) :
    (mul i j).RealContains (x * y) :=
  ScalarSuffixCertificate.QInterval.realContains_mul hx hy

private theorem scale_sound (q : ℚ) {i : QInterval} {x : ℝ}
    (hx : i.RealContains x) : (scale q i).RealContains ((q : ℝ) * x) :=
  scaledEnclosure_sound q i hx

/-! ## Cell-independent source interval DAG -/

private def physicalZInterval (s u : QInterval) : QInterval :=
  NearOneLocalInterval.piInterval.add
    ((mul (mul NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval) s).add
      (mul (mul s s) u))

private theorem physicalZInterval_sound {sI uI : QInterval} {s u : ℝ}
    (hs : sI.RealContains s) (hu : uI.RealContains u) :
    (physicalZInterval sI uI).RealContains (physicalZ s Real.pi u) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := mul_sound hpi hpi
  have hsSq := mul_sound hs hs
  have h := LeanSuffixReflective.QInterval.realContains_add hpi
    (LeanSuffixReflective.QInterval.realContains_add
      (mul_sound hpiSq hs) (mul_sound hsSq hu))
  convert h using 1
  · rfl
  · norm_num [physicalZ, pow_two]
    ring

private def physicalAInterval (s v : QInterval) : QInterval :=
  (scale (5 / 12) NearOneLocalInterval.piInterval).add
    ((mul s (scale (1 / 144)
      ((scale 43 (mul NearOneLocalInterval.piInterval
        NearOneLocalInterval.piInterval)).add (point 1056)))).add
      (mul (mul s s) v))

private theorem physicalAInterval_sound {sI vI : QInterval} {s v : ℝ}
    (hs : sI.RealContains s) (hv : vI.RealContains v) :
    (physicalAInterval sI vI).RealContains (physicalA s Real.pi v) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := mul_sound hpi hpi
  have hsSq := mul_sound hs hs
  have hcoefficient := scale_sound (1 / 144)
    (LeanSuffixReflective.QInterval.realContains_add
      (scale_sound 43 hpiSq) (point_sound 1056))
  have h := LeanSuffixReflective.QInterval.realContains_add
    (scale_sound (5 / 12) hpi)
    (LeanSuffixReflective.QInterval.realContains_add
      (mul_sound hs hcoefficient) (mul_sound hsSq hv))
  convert h using 1
  · rfl
  · norm_num [physicalA, pow_two]
    ring

private def physicalBInterval (s w : QInterval) : QInterval :=
  ((point (-44)).add
    (scale (19 / 24) (mul NearOneLocalInterval.piInterval
      NearOneLocalInterval.piInterval))).add
    ((mul s (scale (1 / 216)
      (mul NearOneLocalInterval.piInterval
        ((scale 295 (mul NearOneLocalInterval.piInterval
          NearOneLocalInterval.piInterval)).add (point (-14256)))))).add
      (mul (mul s s) w))

private theorem physicalBInterval_sound {sI wI : QInterval} {s w : ℝ}
    (hs : sI.RealContains s) (hw : wI.RealContains w) :
    (physicalBInterval sI wI).RealContains (physicalB s Real.pi w) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := mul_sound hpi hpi
  have hsSq := mul_sound hs hs
  have hbase := LeanSuffixReflective.QInterval.realContains_add
    (point_sound (-44)) (scale_sound (19 / 24) hpiSq)
  have hcoefficient := scale_sound (1 / 216)
    (mul_sound hpi (LeanSuffixReflective.QInterval.realContains_add
      (scale_sound 295 hpiSq) (point_sound (-14256))))
  have h := LeanSuffixReflective.QInterval.realContains_add hbase
    (LeanSuffixReflective.QInterval.realContains_add
      (mul_sound hs hcoefficient) (mul_sound hsSq hw))
  convert h using 1
  · rfl
  · norm_num [physicalB, pow_two]
    ring

private def eInterval (s z a b : QInterval) : QInterval :=
  ((scale 6 a).add (scale (-2) z)).add (mul s b)

private theorem eInterval_sound {sI zI aI bI : QInterval} {s z a b : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z)
    (ha : aI.RealContains a) (hb : bI.RealContains b) :
    (eInterval sI zI aI bI).RealContains (eCoord s z a b) := by
  have h := LeanSuffixReflective.QInterval.realContains_add
    (LeanSuffixReflective.QInterval.realContains_add
      (scale_sound 6 ha) (scale_sound (-2) hz)) (mul_sound hs hb)
  convert h using 1
  · rfl
  · norm_num [eCoord]
    ring

private def yInterval (s z : QInterval) : QInterval :=
  mul s ((point 1).add (mul s z))

private theorem yInterval_sound {sI zI : QInterval} {s z : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z) :
    (yInterval sI zI).RealContains (yCoord s z) := by
  have hA := LeanSuffixReflective.QInterval.realContains_add
    (point_sound 1) (mul_sound hs hz)
  have h := mul_sound hs hA
  convert h using 1
  · rfl
  · norm_num [yCoord, aCoord]

private def wInterval (s a : QInterval) : QInterval :=
  mul s ((point 2).add (mul s a))

private theorem wInterval_sound {sI aI : QInterval} {s a : ℝ}
    (hs : sI.RealContains s) (ha : aI.RealContains a) :
    (wInterval sI aI).RealContains (wCoord s a) := by
  have hR := LeanSuffixReflective.QInterval.realContains_add
    (point_sound 2) (mul_sound hs ha)
  have h := mul_sound hs hR
  convert h using 1
  · rfl
  · norm_num [wCoord, rCoord]

private def vInterval (s z a b : QInterval) : QInterval :=
  let r := (point 2).add (mul s a)
  let e := eInterval s z a b
  mul s (r.add (mul s e))

private theorem vInterval_sound {sI zI aI bI : QInterval} {s z a b : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z)
    (ha : aI.RealContains a) (hb : bI.RealContains b) :
    (vInterval sI zI aI bI).RealContains (vCoord s z a b) := by
  have hR := LeanSuffixReflective.QInterval.realContains_add
    (point_sound 2) (mul_sound hs ha)
  have hE := eInterval_sound hs hz ha hb
  have h := mul_sound hs (LeanSuffixReflective.QInterval.realContains_add
    hR (mul_sound hs hE))
  convert h using 1
  · rfl
  · norm_num [vCoord, rCoord]

private def densityDenInterval (s z : QInterval) : QInterval :=
  let y := yInterval s z
  (point 1).sub (mul y y)

private theorem densityDenInterval_sound {sI zI : QInterval} {s z : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z) :
    (densityDenInterval sI zI).RealContains (1 - yCoord s z ^ 2) := by
  have hy := yInterval_sound hs hz
  have h := LeanSuffixReflective.QInterval.realContains_sub
    (point_sound 1) (mul_sound hy hy)
  convert h using 1
  · rfl
  · norm_num [pow_two]

private def fourDenInterval (s z : QInterval) : QInterval :=
  (point 1).add (mul s (yInterval s z))

private theorem fourDenInterval_sound {sI zI : QInterval} {s z : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z) :
    (fourDenInterval sI zI).RealContains (1 + s * yCoord s z) := by
  have hone : (point 1).RealContains (1 : ℝ) := by
    simpa using point_sound 1
  exact LeanSuffixReflective.QInterval.realContains_add
    hone (mul_sound hs (yInterval_sound hs hz))

private def threeDenInterval (s z a b : QInterval) : QInterval :=
  (point 1).add (mul (wInterval s a) (vInterval s z a b))

private theorem threeDenInterval_sound
    {sI zI aI bI : QInterval} {s z a b : ℝ}
    (hs : sI.RealContains s) (hz : zI.RealContains z)
    (ha : aI.RealContains a) (hb : bI.RealContains b) :
    (threeDenInterval sI zI aI bI).RealContains
      (1 + wCoord s a * vCoord s z a b) := by
  have hone : (point 1).RealContains (1 : ℝ) := by
    simpa using point_sound 1
  exact LeanSuffixReflective.QInterval.realContains_add hone
    (mul_sound (wInterval_sound hs ha) (vInterval_sound hs hz ha hb))

private def fourArgumentInterval (s z : QInterval)
    (hden : 0 < (fourDenInterval s z).lo) : QInterval :=
  ScalarSuffixCertificate.QInterval.divPos (mul (mul s s) z)
    (fourDenInterval s z) hden

private theorem fourArgumentInterval_sound
    {sI zI : QInterval} {s z : ℝ}
    (hden : 0 < (fourDenInterval sI zI).lo)
    (hs : sI.RealContains s) (hz : zI.RealContains z) :
    (fourArgumentInterval sI zI hden).RealContains
      (fourIncrementArgument s z) := by
  have hsSq := mul_sound hs hs
  have hnum := mul_sound hsSq hz
  have hq := ScalarSuffixCertificate.QInterval.realContains_divPos hden hnum
    (fourDenInterval_sound hs hz)
  simpa only [fourArgumentInterval, fourIncrementArgument, pow_two] using hq

private def threeArgumentInterval (s z a b : QInterval)
    (hden : 0 < (threeDenInterval s z a b).lo) : QInterval :=
  ScalarSuffixCertificate.QInterval.divPos
    (mul (mul s s) (eInterval s z a b))
    (threeDenInterval s z a b) hden

private theorem threeArgumentInterval_sound
    {sI zI aI bI : QInterval} {s z a b : ℝ}
    (hden : 0 < (threeDenInterval sI zI aI bI).lo)
    (hs : sI.RealContains s) (hz : zI.RealContains z)
    (ha : aI.RealContains a) (hb : bI.RealContains b) :
    (threeArgumentInterval sI zI aI bI hden).RealContains
      (threeIncrementArgument s z a b) := by
  have hsSq := mul_sound hs hs
  have he := eInterval_sound hs hz ha hb
  have hnum := mul_sound hsSq he
  have hq := ScalarSuffixCertificate.QInterval.realContains_divPos hden hnum
    (threeDenInterval_sound hs hz ha hb)
  simpa only [threeArgumentInterval, threeIncrementArgument, pow_two] using hq

/-! ## Fixed cell data -/

private def seamS (mu dTau : ℝ) : ℝ :=
  (firstScale : ℝ) *
    ((firstTauCenter : ℝ) +
      (firstTauSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dTau)
private def seamU (mu du : ℝ) : ℝ :=
  (firstUCenter : ℝ) + (firstUSlope : ℝ) * (mu - (firstMuMid : ℝ)) + du
private def seamV (mu dv : ℝ) : ℝ :=
  (firstVCenter : ℝ) + (firstVSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dv
private def seamW (mu dw : ℝ) : ℝ :=
  (firstBCorrectionCenter : ℝ) +
    (firstBCorrectionSlope : ℝ) * (mu - (firstMuMid : ℝ)) + dw

def remoteMuInterval : QInterval := ⟨125 / 8, 8125 / 512, by norm_num⟩
def remoteMuMid : ℚ := 16125 / 1024
def remoteTauCenter : ℚ :=
  317515407095291403822851222479 / 316912650057057350374175801344
def remoteTauSlope : ℚ :=
  24751920299240995174106000085 / 1267650600228229401496703205376
def remoteTauDisplacement : QInterval :=
  ⟨-(25763226626837054463995493 / 1267650600228229401496703205376),
    25763226626837054463995493 / 1267650600228229401496703205376, by norm_num⟩
def remoteUCenter : ℚ :=
  85953222462807588192949795654767 / 1267650600228229401496703205376
def remoteUSlope : ℚ :=
  476420667179077890970779282973 / 1267650600228229401496703205376
def remoteUDisplacement : QInterval :=
  ⟨-(245989155428728922187446505 / 633825300114114700748351602688),
    245989155428728922187446505 / 633825300114114700748351602688, by norm_num⟩
def remoteVCenter : ℚ :=
  78600373933819089149710919716517 / 1267650600228229401496703205376
def remoteVSlope : ℚ :=
  402648976783680371887966015231 / 1267650600228229401496703205376
def remoteVDisplacement : QInterval :=
  ⟨-(437510429822173346460018889 / 316912650057057350374175801344),
    437510429822173346460018889 / 316912650057057350374175801344, by norm_num⟩
def remoteWCenter : ℚ :=
  -612488676960321022429414009321045 / 633825300114114700748351602688
def remoteWSlope : ℚ :=
  -874328376986386943276816613793 / 158456325028528675187087900672
def remoteWDisplacement : QInterval :=
  ⟨-(4505814968588207646541966665 / 39614081257132168796771975168),
    4505814968588207646541966665 / 39614081257132168796771975168, by norm_num⟩
def remoteScale : ℚ := 1 / 25

def remoteTauRaw : QInterval := affineEnclosure remoteMuInterval
  remoteTauDisplacement remoteMuMid remoteTauCenter remoteTauSlope
def remoteSRaw : QInterval := scale remoteScale remoteTauRaw
def remoteURaw : QInterval := affineEnclosure remoteMuInterval
  remoteUDisplacement remoteMuMid remoteUCenter remoteUSlope
def remoteVRaw : QInterval := affineEnclosure remoteMuInterval
  remoteVDisplacement remoteMuMid remoteVCenter remoteVSlope
def remoteWRaw : QInterval := affineEnclosure remoteMuInterval
  remoteWDisplacement remoteMuMid remoteWCenter remoteWSlope

def remoteS (mu dTau : ℝ) : ℝ :=
  (remoteScale : ℝ) * ((remoteTauCenter : ℝ) +
    (remoteTauSlope : ℝ) * (mu - (remoteMuMid : ℝ)) + dTau)
def remoteU (mu du : ℝ) : ℝ :=
  (remoteUCenter : ℝ) + (remoteUSlope : ℝ) * (mu - (remoteMuMid : ℝ)) + du
def remoteV (mu dv : ℝ) : ℝ :=
  (remoteVCenter : ℝ) + (remoteVSlope : ℝ) * (mu - (remoteMuMid : ℝ)) + dv
def remoteW (mu dw : ℝ) : ℝ :=
  (remoteWCenter : ℝ) + (remoteWSlope : ℝ) * (mu - (remoteMuMid : ℝ)) + dw

private theorem remote_input_enclosures {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    remoteSRaw.RealContains (remoteS mu dTau) ∧
      remoteURaw.RealContains (remoteU mu du) ∧
      remoteVRaw.RealContains (remoteV mu dv) ∧
      remoteWRaw.RealContains (remoteW mu dw) := by
  exact ⟨scaledEnclosure_sound remoteScale _
      (affineEnclosure_sound remoteMuInterval remoteTauDisplacement
        remoteMuMid remoteTauCenter remoteTauSlope hmu hdTau),
    affineEnclosure_sound remoteMuInterval remoteUDisplacement
      remoteMuMid remoteUCenter remoteUSlope hmu hdu,
    affineEnclosure_sound remoteMuInterval remoteVDisplacement
      remoteMuMid remoteVCenter remoteVSlope hmu hdv,
    affineEnclosure_sound remoteMuInterval remoteWDisplacement
      remoteMuMid remoteWCenter remoteWSlope hmu hdw⟩

/-! ## Source guards -/

theorem remote_source_guards {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    remoteS mu dTau ≠ 0 ∧
    1 - yCoord (remoteS mu dTau)
      (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du)) ^ 2 ≠ 0 ∧
    1 + remoteS mu dTau * yCoord (remoteS mu dTau)
      (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du)) ≠ 0 ∧
    1 + wCoord (remoteS mu dTau)
        (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv)) *
      vCoord (remoteS mu dTau)
        (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))
        (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))
        (physicalB (remoteS mu dTau) Real.pi (remoteW mu dw)) ≠ 0 := by
  rcases remote_input_enclosures hmu hdTau hdu hdv hdw with ⟨hs, hu, hv, hw⟩
  let z := physicalZ (remoteS mu dTau) Real.pi (remoteU mu du)
  let a := physicalA (remoteS mu dTau) Real.pi (remoteV mu dv)
  let b := physicalB (remoteS mu dTau) Real.pi (remoteW mu dw)
  have hz : (physicalZInterval remoteSRaw remoteURaw).RealContains z :=
    physicalZInterval_sound hs hu
  have ha : (physicalAInterval remoteSRaw remoteVRaw).RealContains a :=
    physicalAInterval_sound hs hv
  have hb : (physicalBInterval remoteSRaw remoteWRaw).RealContains b :=
    physicalBInterval_sound hs hw
  have hspos : 0 < remoteS mu dTau :=
    ScalarSuffixCertificate.QInterval.positive_of_realContains hs (by
      norm_num [remoteSRaw, remoteTauRaw, scale, scaledEnclosure,
        affineEnclosure, remoteMuInterval, remoteTauDisplacement, remoteMuMid,
        remoteTauCenter, remoteTauSlope, remoteScale,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
  have hdensity : 0 < 1 - yCoord (remoteS mu dTau) z ^ 2 :=
    ScalarSuffixCertificate.QInterval.positive_of_realContains
      (densityDenInterval_sound hs hz) (by
        norm_num [densityDenInterval, yInterval, physicalZInterval,
          remoteSRaw, remoteTauRaw, remoteURaw, scale, mul, scaledEnclosure,
          affineEnclosure, remoteMuInterval, remoteTauDisplacement,
          remoteUDisplacement, remoteMuMid, remoteTauCenter, remoteTauSlope,
          remoteUCenter, remoteUSlope, remoteScale, NearOneLocalInterval.piInterval,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
          LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
  have hfour : 0 < 1 + remoteS mu dTau * yCoord (remoteS mu dTau) z :=
    ScalarSuffixCertificate.QInterval.positive_of_realContains
      (fourDenInterval_sound hs hz) (by
        norm_num [fourDenInterval, yInterval, physicalZInterval,
          remoteSRaw, remoteTauRaw, remoteURaw, scale, mul, scaledEnclosure,
          affineEnclosure, remoteMuInterval, remoteTauDisplacement,
          remoteUDisplacement, remoteMuMid, remoteTauCenter, remoteTauSlope,
          remoteUCenter, remoteUSlope, remoteScale, NearOneLocalInterval.piInterval,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
          LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
  have hthree : 0 < 1 + wCoord (remoteS mu dTau) a *
      vCoord (remoteS mu dTau) z a b :=
    ScalarSuffixCertificate.QInterval.positive_of_realContains
      (threeDenInterval_sound hs hz ha hb) (by
        norm_num [threeDenInterval, wInterval, vInterval, eInterval,
          physicalZInterval, physicalAInterval, physicalBInterval,
          remoteSRaw, remoteTauRaw, remoteURaw, remoteVRaw, remoteWRaw,
          scale, mul, scaledEnclosure, affineEnclosure, remoteMuInterval,
          remoteTauDisplacement, remoteUDisplacement, remoteVDisplacement,
          remoteWDisplacement, remoteMuMid, remoteTauCenter, remoteTauSlope,
          remoteUCenter, remoteUSlope, remoteVCenter, remoteVSlope,
          remoteWCenter, remoteWSlope, remoteScale, NearOneLocalInterval.piInterval,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
          LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
  exact ⟨ne_of_gt hspos, ne_of_gt hdensity, ne_of_gt hfour, ne_of_gt hthree⟩

/-- The actual grouped source is connected to the complete third numerator on
all points of the remote stress cell. -/
theorem remote_sourceGroupedThird_div_sq_eq_complete_div_four
    {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    sourceGroupedThird (remoteS mu dTau) Real.pi
        (remoteU mu du) (remoteV mu dv) (remoteW mu dw) /
        remoteS mu dTau ^ 2 =
      completeThirdRowNumerator (remoteS mu dTau)
        (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))
        (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))
        (physicalB (remoteS mu dTau) Real.pi (remoteW mu dw)) Real.pi /
        remoteS mu dTau ^ 4 := by
  rcases remote_source_guards hmu hdTau hdu hdv hdw with
    ⟨hs, hy, hfour, hthree⟩
  exact NearOneLocalThirdSource.sourceGroupedThird_div_sq_eq_complete_div_four
    _ _ _ _ _ hs hy hfour hthree

/-! ## Actual argument and twenty-term remainder intervals -/

def seamArgumentInterval : QInterval := ⟨0, 1 / 50000, by norm_num⟩
def remoteScaleArgumentInterval : QInterval := ⟨0, 1 / 20, by norm_num⟩
def remoteLowerArgumentInterval : QInterval := ⟨0, 1 / 10, by norm_num⟩
def remoteIncrementArgumentInterval : QInterval := ⟨0, 1 / 100, by norm_num⟩

def seamRemainderInterval : QInterval :=
  ⟨-1 / 7 - 1 / 10000000000000000000000000000000000000000,
    -1 / 7 + 1 / 10000000000, by norm_num⟩
def remoteScaleRemainderInterval : QInterval :=
  ⟨-1 / 7 - 1 / 10000000000000000000000000000000000000000,
    -1 / 7 + 1 / 3000, by norm_num⟩
def remoteLowerRemainderInterval : QInterval :=
  ⟨-1 / 7 - 1 / 10000000000000000000000000000000000000000,
    -1 / 7 + 1 / 800, by norm_num⟩
def remoteIncrementRemainderInterval : QInterval :=
  ⟨-1 / 7 - 1 / 10000000000000000000000000000000000000000,
    -1 / 7 + 1 / 80000, by norm_num⟩

def seamRemainderMidpoint : ℚ :=
  (seamRemainderInterval.lo + seamRemainderInterval.hi) / 2
def seamRemainderRadius : ℚ :=
  (seamRemainderInterval.hi - seamRemainderInterval.lo) / 2
def remoteScaleRemainderMidpoint : ℚ :=
  (remoteScaleRemainderInterval.lo + remoteScaleRemainderInterval.hi) / 2
def remoteScaleRemainderRadius : ℚ :=
  (remoteScaleRemainderInterval.hi - remoteScaleRemainderInterval.lo) / 2
def remoteLowerRemainderMidpoint : ℚ :=
  (remoteLowerRemainderInterval.lo + remoteLowerRemainderInterval.hi) / 2
def remoteLowerRemainderRadius : ℚ :=
  (remoteLowerRemainderInterval.hi - remoteLowerRemainderInterval.lo) / 2
def remoteIncrementRemainderMidpoint : ℚ :=
  (remoteIncrementRemainderInterval.lo + remoteIncrementRemainderInterval.hi) / 2
def remoteIncrementRemainderRadius : ℚ :=
  (remoteIncrementRemainderInterval.hi - remoteIncrementRemainderInterval.lo) / 2

private theorem seam_remainder_of_argument {x : ℝ}
    (hx : seamArgumentInterval.RealContains x) :
    seamRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 x) := by
  apply NearOneLocalInterval.atanRemainder_three_interval_sound
    seamArgumentInterval seamRemainderInterval (1 / 50000) hx
  all_goals norm_num [seamArgumentInterval, seamRemainderInterval,
    NearOneLocalInterval.atanRemainderThreeSeries20Interval,
    NearOneLocalInterval.intervalHorner,
    NearOneLocalInterval.atanRemainderThreeCoefficients20,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add]

private theorem remote_scale_remainder_of_argument {x : ℝ}
    (hx : remoteScaleArgumentInterval.RealContains x) :
    remoteScaleRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 x) := by
  apply NearOneLocalInterval.atanRemainder_three_interval_sound
    remoteScaleArgumentInterval remoteScaleRemainderInterval (1 / 20) hx
  all_goals norm_num [remoteScaleArgumentInterval, remoteScaleRemainderInterval,
    NearOneLocalInterval.atanRemainderThreeSeries20Interval,
    NearOneLocalInterval.intervalHorner,
    NearOneLocalInterval.atanRemainderThreeCoefficients20,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add]

private theorem remote_lower_remainder_of_argument {x : ℝ}
    (hx : remoteLowerArgumentInterval.RealContains x) :
    remoteLowerRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 x) := by
  apply NearOneLocalInterval.atanRemainder_three_interval_sound
    remoteLowerArgumentInterval remoteLowerRemainderInterval (1 / 10) hx
  all_goals norm_num [remoteLowerArgumentInterval, remoteLowerRemainderInterval,
    NearOneLocalInterval.atanRemainderThreeSeries20Interval,
    NearOneLocalInterval.intervalHorner,
    NearOneLocalInterval.atanRemainderThreeCoefficients20,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add]

private theorem remote_increment_remainder_of_argument {x : ℝ}
    (hx : remoteIncrementArgumentInterval.RealContains x) :
    remoteIncrementRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 x) := by
  apply NearOneLocalInterval.atanRemainder_three_interval_sound
    remoteIncrementArgumentInterval remoteIncrementRemainderInterval (1 / 100) hx
  all_goals norm_num [remoteIncrementArgumentInterval,
    remoteIncrementRemainderInterval,
    NearOneLocalInterval.atanRemainderThreeSeries20Interval,
    NearOneLocalInterval.intervalHorner,
    NearOneLocalInterval.atanRemainderThreeCoefficients20,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add]

theorem seam_argument_enclosures {mu dTau du dv dw : ℝ}
    (hmu : firstMuInterval.RealContains mu)
    (hdTau : firstTauDisplacement.RealContains dTau)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    seamArgumentInterval.RealContains (seamS mu dTau) ∧
    seamArgumentInterval.RealContains
      (wCoord (seamS mu dTau)
        (physicalA (seamS mu dTau) Real.pi (seamV mu dv))) ∧
    seamArgumentInterval.RealContains
      (fourIncrementArgument (seamS mu dTau)
        (physicalZ (seamS mu dTau) Real.pi (seamU mu du))) ∧
    seamArgumentInterval.RealContains
      (threeIncrementArgument (seamS mu dTau)
        (physicalZ (seamS mu dTau) Real.pi (seamU mu du))
        (physicalA (seamS mu dTau) Real.pi (seamV mu dv))
        (physicalB (seamS mu dTau) Real.pi (seamW mu dw))) := by
  have hs : firstSRawEnclosure.RealContains (seamS mu dTau) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hmu hdTau)
  have hu := affineEnclosure_sound firstMuInterval firstUDisplacement
    firstMuMid firstUCenter firstUSlope hmu hdu
  have hv := affineEnclosure_sound firstMuInterval firstVDisplacement
    firstMuMid firstVCenter firstVSlope hmu hdv
  have hw := affineEnclosure_sound firstMuInterval firstBCorrectionDisplacement
    firstMuMid firstBCorrectionCenter firstBCorrectionSlope hmu hdw
  have hz := physicalZInterval_sound hs hu
  have ha := physicalAInterval_sound hs hv
  have hb := physicalBInterval_sound hs hw
  have hd4pos : 0 < (fourDenInterval firstSRawEnclosure
      (physicalZInterval firstSRawEnclosure firstURawEnclosure)).lo := by
    norm_num [fourDenInterval, yInterval, physicalZInterval, firstSRawEnclosure,
      firstURawEnclosure, scale, mul, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstUDisplacement, firstMuMid,
      firstTauCenter, firstTauSlope, firstUCenter, firstUSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have hd3pos : 0 < (threeDenInterval firstSRawEnclosure
      (physicalZInterval firstSRawEnclosure firstURawEnclosure)
      (physicalAInterval firstSRawEnclosure firstVRawEnclosure)
      (physicalBInterval firstSRawEnclosure firstBCorrectionRawEnclosure)).lo := by
    norm_num [threeDenInterval, wInterval, vInterval, eInterval,
      physicalZInterval, physicalAInterval, physicalBInterval,
      firstSRawEnclosure, firstURawEnclosure, firstVRawEnclosure,
      firstBCorrectionRawEnclosure, scale, mul, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstUDisplacement,
      firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
      firstTauCenter, firstTauSlope, firstUCenter, firstUSlope, firstVCenter,
      firstVSlope, firstBCorrectionCenter, firstBCorrectionSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  refine ⟨NearOneLocalInterval.realContains_of_subset ?_ ?_ hs,
    NearOneLocalInterval.realContains_of_subset ?_ ?_ (wInterval_sound hs ha),
    NearOneLocalInterval.realContains_of_subset ?_ ?_
      (fourArgumentInterval_sound hd4pos hs hz),
    NearOneLocalInterval.realContains_of_subset ?_ ?_
      (threeArgumentInterval_sound hd3pos hs hz ha hb)⟩
  all_goals norm_num [seamArgumentInterval, fourArgumentInterval,
    threeArgumentInterval, fourDenInterval, threeDenInterval, yInterval,
    wInterval, vInterval, eInterval, physicalZInterval, physicalAInterval,
    physicalBInterval, firstSRawEnclosure, firstURawEnclosure,
    firstVRawEnclosure, firstBCorrectionRawEnclosure, scale, mul,
    scaledEnclosure, affineEnclosure, firstMuInterval, firstTauDisplacement,
    firstUDisplacement, firstVDisplacement, firstBCorrectionDisplacement,
    firstMuMid, firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
    firstVCenter, firstVSlope, firstBCorrectionCenter, firstBCorrectionSlope,
    firstScale, NearOneLocalInterval.piInterval,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.neg]

/-- All four actual seam-cell `R₃` calls lie in the same checked narrow range. -/
theorem seam_remainder_enclosures {mu dTau du dv dw : ℝ}
    (hmu : firstMuInterval.RealContains mu)
    (hdTau : firstTauDisplacement.RealContains dTau)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    seamRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 (seamS mu dTau)) ∧
    seamRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (wCoord (seamS mu dTau)
          (physicalA (seamS mu dTau) Real.pi (seamV mu dv)))) ∧
    seamRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (fourIncrementArgument (seamS mu dTau)
          (physicalZ (seamS mu dTau) Real.pi (seamU mu du)))) ∧
    seamRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (threeIncrementArgument (seamS mu dTau)
          (physicalZ (seamS mu dTau) Real.pi (seamU mu du))
          (physicalA (seamS mu dTau) Real.pi (seamV mu dv))
          (physicalB (seamS mu dTau) Real.pi (seamW mu dw)))) := by
  rcases seam_argument_enclosures hmu hdTau hdu hdv hdw with
    ⟨hs, hW, hq4, hq3⟩
  exact ⟨seam_remainder_of_argument hs, seam_remainder_of_argument hW,
    seam_remainder_of_argument hq4, seam_remainder_of_argument hq3⟩

theorem remote_argument_enclosures {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    remoteScaleArgumentInterval.RealContains (remoteS mu dTau) ∧
    remoteLowerArgumentInterval.RealContains
      (wCoord (remoteS mu dTau)
        (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))) ∧
    remoteIncrementArgumentInterval.RealContains
      (fourIncrementArgument (remoteS mu dTau)
        (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))) ∧
    remoteIncrementArgumentInterval.RealContains
      (threeIncrementArgument (remoteS mu dTau)
        (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))
        (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))
        (physicalB (remoteS mu dTau) Real.pi (remoteW mu dw))) := by
  rcases remote_input_enclosures hmu hdTau hdu hdv hdw with ⟨hs, hu, hv, hw⟩
  have hz := physicalZInterval_sound hs hu
  have ha := physicalAInterval_sound hs hv
  have hb := physicalBInterval_sound hs hw
  have hd4pos : 0 < (fourDenInterval remoteSRaw
      (physicalZInterval remoteSRaw remoteURaw)).lo := by
    norm_num [fourDenInterval, yInterval, physicalZInterval, remoteSRaw,
      remoteTauRaw, remoteURaw, scale, mul, scaledEnclosure, affineEnclosure,
      remoteMuInterval, remoteTauDisplacement, remoteUDisplacement, remoteMuMid,
      remoteTauCenter, remoteTauSlope, remoteUCenter, remoteUSlope, remoteScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have hd3pos : 0 < (threeDenInterval remoteSRaw
      (physicalZInterval remoteSRaw remoteURaw)
      (physicalAInterval remoteSRaw remoteVRaw)
      (physicalBInterval remoteSRaw remoteWRaw)).lo := by
    norm_num [threeDenInterval, wInterval, vInterval, eInterval,
      physicalZInterval, physicalAInterval, physicalBInterval,
      remoteSRaw, remoteTauRaw, remoteURaw, remoteVRaw, remoteWRaw,
      scale, mul, scaledEnclosure, affineEnclosure, remoteMuInterval,
      remoteTauDisplacement, remoteUDisplacement, remoteVDisplacement,
      remoteWDisplacement, remoteMuMid, remoteTauCenter, remoteTauSlope,
      remoteUCenter, remoteUSlope, remoteVCenter, remoteVSlope,
      remoteWCenter, remoteWSlope, remoteScale, NearOneLocalInterval.piInterval,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  refine ⟨NearOneLocalInterval.realContains_of_subset ?_ ?_ hs,
    NearOneLocalInterval.realContains_of_subset ?_ ?_ (wInterval_sound hs ha),
    NearOneLocalInterval.realContains_of_subset ?_ ?_
      (fourArgumentInterval_sound hd4pos hs hz),
    NearOneLocalInterval.realContains_of_subset ?_ ?_
      (threeArgumentInterval_sound hd3pos hs hz ha hb)⟩
  all_goals norm_num [remoteScaleArgumentInterval, remoteLowerArgumentInterval,
    remoteIncrementArgumentInterval, fourArgumentInterval,
    threeArgumentInterval, fourDenInterval, threeDenInterval, yInterval,
    wInterval, vInterval, eInterval, physicalZInterval, physicalAInterval,
    physicalBInterval, remoteSRaw, remoteTauRaw, remoteURaw, remoteVRaw,
    remoteWRaw, scale, mul, scaledEnclosure, affineEnclosure, remoteMuInterval,
    remoteTauDisplacement, remoteUDisplacement, remoteVDisplacement,
    remoteWDisplacement, remoteMuMid, remoteTauCenter, remoteTauSlope,
    remoteUCenter, remoteUSlope, remoteVCenter, remoteVSlope,
    remoteWCenter, remoteWSlope, remoteScale, NearOneLocalInterval.piInterval,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.neg]

/-- The four actual remote-cell `R₃` calls have independently checked
one-variable twenty-term enclosures. -/
theorem remote_remainder_enclosures {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    remoteScaleRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3 (remoteS mu dTau)) ∧
    remoteLowerRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (wCoord (remoteS mu dTau)
          (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv)))) ∧
    remoteIncrementRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (fourIncrementArgument (remoteS mu dTau)
          (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du)))) ∧
    remoteIncrementRemainderInterval.RealContains
      (NearOneAtanRemainder.atanRemainder 3
        (threeIncrementArgument (remoteS mu dTau)
          (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))
          (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))
          (physicalB (remoteS mu dTau) Real.pi (remoteW mu dw)))) := by
  rcases remote_argument_enclosures hmu hdTau hdu hdv hdw with
    ⟨hs, hW, hq4, hq3⟩
  exact ⟨remote_scale_remainder_of_argument hs,
    remote_lower_remainder_of_argument hW,
    remote_increment_remainder_of_argument hq4,
    remote_increment_remainder_of_argument hq3⟩

/-- The seam-cell remainders satisfy the four independent midpoint budgets
used by the source-affine error estimate. -/
theorem seam_remainder_error_budgets {mu dTau du dv dw : ℝ}
    (hmu : firstMuInterval.RealContains mu)
    (hdTau : firstTauDisplacement.RealContains dTau)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    |NearOneAtanRemainder.atanRemainder 3 (seamS mu dTau) -
        (seamRemainderMidpoint : ℝ)| ≤ (seamRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (wCoord (seamS mu dTau)
            (physicalA (seamS mu dTau) Real.pi (seamV mu dv))) -
        (seamRemainderMidpoint : ℝ)| ≤ (seamRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (fourIncrementArgument (seamS mu dTau)
            (physicalZ (seamS mu dTau) Real.pi (seamU mu du))) -
        (seamRemainderMidpoint : ℝ)| ≤ (seamRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (threeIncrementArgument (seamS mu dTau)
            (physicalZ (seamS mu dTau) Real.pi (seamU mu du))
            (physicalA (seamS mu dTau) Real.pi (seamV mu dv))
            (physicalB (seamS mu dTau) Real.pi (seamW mu dw))) -
        (seamRemainderMidpoint : ℝ)| ≤ (seamRemainderRadius : ℝ) := by
  rcases seam_remainder_enclosures hmu hdTau hdu hdv hdw with
    ⟨hs, hW, hq4, hq3⟩
  simpa only [seamRemainderMidpoint, seamRemainderRadius] using
    And.intro (realContains_midpoint_error_le hs)
      (And.intro (realContains_midpoint_error_le hW)
        (And.intro (realContains_midpoint_error_le hq4)
          (realContains_midpoint_error_le hq3)))

/-- The remote-cell remainders satisfy the four independent midpoint budgets
used by the source-affine error estimate. -/
theorem remote_remainder_error_budgets {mu dTau du dv dw : ℝ}
    (hmu : remoteMuInterval.RealContains mu)
    (hdTau : remoteTauDisplacement.RealContains dTau)
    (hdu : remoteUDisplacement.RealContains du)
    (hdv : remoteVDisplacement.RealContains dv)
    (hdw : remoteWDisplacement.RealContains dw) :
    |NearOneAtanRemainder.atanRemainder 3 (remoteS mu dTau) -
        (remoteScaleRemainderMidpoint : ℝ)| ≤
          (remoteScaleRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (wCoord (remoteS mu dTau)
            (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))) -
        (remoteLowerRemainderMidpoint : ℝ)| ≤
          (remoteLowerRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (fourIncrementArgument (remoteS mu dTau)
            (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))) -
        (remoteIncrementRemainderMidpoint : ℝ)| ≤
          (remoteIncrementRemainderRadius : ℝ) ∧
    |NearOneAtanRemainder.atanRemainder 3
          (threeIncrementArgument (remoteS mu dTau)
            (physicalZ (remoteS mu dTau) Real.pi (remoteU mu du))
            (physicalA (remoteS mu dTau) Real.pi (remoteV mu dv))
            (physicalB (remoteS mu dTau) Real.pi (remoteW mu dw))) -
        (remoteIncrementRemainderMidpoint : ℝ)| ≤
          (remoteIncrementRemainderRadius : ℝ) := by
  rcases remote_remainder_enclosures hmu hdTau hdu hdv hdw with
    ⟨hs, hW, hq4, hq3⟩
  simpa only [remoteScaleRemainderMidpoint, remoteScaleRemainderRadius,
    remoteLowerRemainderMidpoint, remoteLowerRemainderRadius,
    remoteIncrementRemainderMidpoint, remoteIncrementRemainderRadius] using
    And.intro (realContains_midpoint_error_le hs)
      (And.intro (realContains_midpoint_error_le hW)
        (And.intro (realContains_midpoint_error_le hq4)
          (realContains_midpoint_error_le hq3)))

end
end NearOneLocalRemainderGate
