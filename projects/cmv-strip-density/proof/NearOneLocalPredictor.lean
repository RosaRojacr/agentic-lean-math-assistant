/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalInterval
import NearOneLocalHeightOrder

/-!
# Scale-local affine predictor certificates

Reusable exact-rational soundness for the affine coordinate predictors used by
`scale_local_atlas`, followed by the first seventeen guard replays for the
subslab adjoining the current prescribed-density seam.
-/

namespace NearOneLocalPredictor

abbrev QInterval := LeanSuffixReflective.QInterval

/-- Exact range evaluation for one affine predictor coordinate. -/
def affineEnclosure (parameter displacement : QInterval)
    (mid center slope : ℚ) : QInterval :=
  (LeanSuffixReflective.QInterval.point center).add
    ((ScalarSuffixCertificate.QInterval.mul
      (LeanSuffixReflective.QInterval.point slope)
      (parameter.sub (LeanSuffixReflective.QInterval.point mid))).add displacement)

/-- The affine interval evaluator denotes the corresponding real coordinate. -/
theorem affineEnclosure_sound
    (parameter displacement : QInterval) (mid center slope : ℚ) {μ d : ℝ}
    (hμ : parameter.RealContains μ) (hd : displacement.RealContains d) :
    (affineEnclosure parameter displacement mid center slope).RealContains
      ((center : ℝ) + (slope : ℝ) * (μ - (mid : ℝ)) + d) := by
  have hmid := (LeanSuffixReflective.QInterval.realContains_point mid (mid : ℝ)).2 rfl
  have hslope :=
    (LeanSuffixReflective.QInterval.realContains_point slope (slope : ℝ)).2 rfl
  have hcenter :=
    (LeanSuffixReflective.QInterval.realContains_point center (center : ℝ)).2 rfl
  have hscaled := ScalarSuffixCertificate.QInterval.realContains_mul hslope
    (LeanSuffixReflective.QInterval.realContains_sub hμ hmid)
  have hresult := LeanSuffixReflective.QInterval.realContains_add hcenter
    (LeanSuffixReflective.QInterval.realContains_add hscaled hd)
  simpa [affineEnclosure, add_assoc] using hresult

/-- Exact range evaluation after a rational change of scale. -/
def scaledEnclosure (scale : ℚ) (i : QInterval) : QInterval :=
  ScalarSuffixCertificate.QInterval.mul
    (LeanSuffixReflective.QInterval.point scale) i

/-- Rational scaling preserves the real interpretation of an interval. -/
theorem scaledEnclosure_sound (scale : ℚ) (i : QInterval) {x : ℝ}
    (hx : i.RealContains x) :
    (scaledEnclosure scale i).RealContains ((scale : ℝ) * x) :=
  ScalarSuffixCertificate.QInterval.realContains_mul
    ((LeanSuffixReflective.QInterval.realContains_point scale (scale : ℝ)).2 rfl) hx

/-- Polynomial margin equivalent to the strict source height order. -/
def heightOrderMargin (s a : ℝ) : ℝ :=
  (1 - s ^ 2) * (2 + s * a) ^ 2 - 2

private theorem heightOrderMargin_mono_coordinate {s a₁ a₂ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 ≤ a₁) (ha : a₁ ≤ a₂) :
    heightOrderMargin s a₁ ≤ heightOrderMargin s a₂ := by
  have hfactor : 0 ≤ 1 - s ^ 2 := by
    nlinarith [sq_nonneg s, (sq_le_sq₀ hs0 (by norm_num : (0 : ℝ) ≤ 1)).2 hs1]
  have hr0 : 0 ≤ 2 + s * a₁ := by positivity
  have hrle : 2 + s * a₁ ≤ 2 + s * a₂ := by
    nlinarith [mul_le_mul_of_nonneg_left ha hs0]
  have hrsq : (2 + s * a₁) ^ 2 ≤ (2 + s * a₂) ^ 2 :=
    (sq_le_sq₀ hr0 (hr0.trans hrle)).2 hrle
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hrsq hfactor) 2

private theorem heightOrderMargin_mono_scale {a s t : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 2)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1 / 100) :
    heightOrderMargin s a ≤ heightOrderMargin t a := by
  have hmono : StrictMonoOn (fun x : ℝ => heightOrderMargin x a)
      (Set.Icc 0 (1 / 100)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / 100))
    · unfold heightOrderMargin
      fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      have hxSq : x ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
        (sq_le_sq₀ hx.1.le (by norm_num)).2 hx.2.le
      have haxSq : a * x ^ 2 ≤ 2 * (1 / 100 : ℝ) ^ 2 := by
        calc
          a * x ^ 2 ≤ 2 * x ^ 2 :=
            mul_le_mul_of_nonneg_right ha1 (sq_nonneg x)
          _ ≤ 2 * (1 / 100 : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hxSq (by norm_num)
      have hsecond : 0 < a - 2 * x - 2 * a * x ^ 2 := by
        nlinarith
      have hxa : 0 ≤ x * a :=
        mul_nonneg hx.1.le (le_trans (by norm_num) ha0)
      have hr : 0 < 2 + x * a := by linarith
      have hderiv : HasDerivAt (fun y : ℝ => heightOrderMargin y a)
          (-(2 * x * (2 + x * a) ^ 2) +
            (1 - x ^ 2) * (2 * (2 + x * a) * a)) x := by
        convert (((hasDerivAt_const x (1 : ℝ)).sub
            ((hasDerivAt_id x).pow 2)).mul
          (((hasDerivAt_const x (2 : ℝ)).add
            ((hasDerivAt_id x).mul_const a)).pow 2)).sub_const 2 using 1 <;>
          first | rfl | simp
      rw [hderiv.deriv, show
        -(2 * x * (2 + x * a) ^ 2) +
            (1 - x ^ 2) * (2 * (2 + x * a) * a) =
          2 * (2 + x * a) * (a - 2 * x - 2 * a * x ^ 2) by ring]
      positivity
  exact hmono.monotoneOn ⟨hs0, hst.trans ht1⟩
    ⟨hs0.trans hst, ht1⟩ hst


section FirstSeamCell

/-- The first saved normalized-density subslab. -/
def firstMuInterval : QInterval :=
  ⟨251 / 20, 17821 / 1280, by norm_num⟩

/-- Midpoint of the first normalized-density subslab. -/
def firstMuMid : ℚ := 6777 / 512

/-- Saved affine predictor center for the scale coordinate `tau`. -/
def firstTauCenter : ℚ :=
  322443258270306467163254222213 / 316912650057057350374175801344

/-- Saved affine predictor slope for the scale coordinate `tau`. -/
def firstTauSlope : ℚ :=
  8120056054247740876800390493 / 316912650057057350374175801344

/-- Saved displacement interval for the scale coordinate `tau`. -/
def firstTauDisplacement : QInterval :=
  ⟨-(297630472323338886479737139 / 316912650057057350374175801344),
    297630472323338886479737139 / 316912650057057350374175801344,
    by norm_num⟩

/-- Saved affine predictor center for the second-order `z` coordinate. -/
def firstUCenter : ℚ :=
  2099535218738366358723433159063 / 39614081257132168796771975168

/-- Saved affine predictor slope for the second-order `z` coordinate. -/
def firstUSlope : ℚ :=
  36630991070183533991691645 / 633825300114114700748351602688

/-- Saved displacement interval for the second-order `z` coordinate. -/
def firstUDisplacement : QInterval :=
  ⟨-(129449977930346532808986187 / 1267650600228229401496703205376),
    129449977930346532808986187 / 1267650600228229401496703205376,
    by norm_num⟩

/-- Saved affine predictor center for the second-order physical `a` coordinate. -/
def firstVCenter : ℚ :=
  31336623081398261903305886966369 / 633825300114114700748351602688

/-- Saved affine predictor slope for the second-order physical `a` coordinate. -/
def firstVSlope : ℚ :=
  62384141782151216103292073 / 1267650600228229401496703205376

/-- Saved displacement interval for the second-order physical `a` coordinate. -/
def firstVDisplacement : QInterval :=
  ⟨-(16131415723891861554797475 / 158456325028528675187087900672),
    16131415723891861554797475 / 158456325028528675187087900672,
    by norm_num⟩

/-- Saved affine predictor center for the second-order physical `b` coordinate. -/
def firstBCorrectionCenter : ℚ :=
  -950081345735298032602579375283795 / 1267650600228229401496703205376

/-- Saved affine predictor slope for the second-order physical `b` coordinate. -/
def firstBCorrectionSlope : ℚ :=
  -267434309128420384049863015 / 316912650057057350374175801344

/-- Saved displacement interval for the second-order physical `b` coordinate. -/
def firstBCorrectionDisplacement : QInterval :=
  ⟨-(3178927473294540211382782433 / 316912650057057350374175801344),
    3178927473294540211382782433 / 316912650057057350374175801344,
    by norm_num⟩

/-- Physical scale factor for the first pilot band. -/
def firstScale : ℚ := 1 / 126334

/-- Exact, unrounded enclosure obtained from the saved affine data. -/
def firstSRawEnclosure : QInterval :=
  scaledEnclosure firstScale
    (affineEnclosure firstMuInterval firstTauDisplacement
      firstMuMid firstTauCenter firstTauSlope)

/-- Exact, unrounded enclosure of the saved affine `u` predictor. -/
def firstURawEnclosure : QInterval :=
  affineEnclosure firstMuInterval firstUDisplacement
    firstMuMid firstUCenter firstUSlope

/-- Exact, unrounded enclosure of the saved affine `v` predictor. -/
def firstVRawEnclosure : QInterval :=
  affineEnclosure firstMuInterval firstVDisplacement
    firstMuMid firstVCenter firstVSlope

/-- Exact interval replay of `z = pi + pi^2*s + u*s^2`. -/
def firstZRawEnclosure : QInterval :=
  NearOneLocalInterval.piInterval.add
    ((ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul NearOneLocalInterval.piInterval
        NearOneLocalInterval.piInterval)
      firstSRawEnclosure).add
      (ScalarSuffixCertificate.QInterval.mul firstURawEnclosure
        (ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
          firstSRawEnclosure)))

/-- Exact interval replay of `A = 1 + s*z`. -/
def firstARawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 1).add
    (ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
      firstZRawEnclosure)

/-- Exact interval replay of the physical coordinate
`a = 5*pi/12 + s*(43*pi^2+1056)/144 + v*s^2`. -/
def firstPhysicalARawEnclosure : QInterval :=
  (scaledEnclosure (5 / 12) NearOneLocalInterval.piInterval).add
    ((ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
      (scaledEnclosure (1 / 144)
        ((scaledEnclosure 43
          (ScalarSuffixCertificate.QInterval.mul
            NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)).add
          (LeanSuffixReflective.QInterval.point 1056)))).add
      (ScalarSuffixCertificate.QInterval.mul
        (ScalarSuffixCertificate.QInterval.mul
          firstSRawEnclosure firstSRawEnclosure)
        firstVRawEnclosure))

/-- Exact interval replay of `R = 2 + s*a`. -/
def firstRRawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 2).add
    (ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstPhysicalARawEnclosure)

/-- Exact interval replay of `W = s*R`. -/
def firstWRawEnclosure : QInterval :=
  ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure firstRRawEnclosure

/-- Exact, unrounded enclosure of the saved affine `w` predictor. -/
def firstBCorrectionRawEnclosure : QInterval :=
  affineEnclosure firstMuInterval firstBCorrectionDisplacement
    firstMuMid firstBCorrectionCenter firstBCorrectionSlope

/-- Exact interval replay of
`b = -44 + 19*pi^2/24 + s*pi*(295*pi^2-14256)/216 + w*s^2`. -/
def firstPhysicalBRawEnclosure : QInterval :=
  ((LeanSuffixReflective.QInterval.point (-44)).add
    (scaledEnclosure (19 / 24)
      (ScalarSuffixCertificate.QInterval.mul
        NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval))).add
  ((ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
      (scaledEnclosure (1 / 216)
        (ScalarSuffixCertificate.QInterval.mul NearOneLocalInterval.piInterval
          ((scaledEnclosure 295
            (ScalarSuffixCertificate.QInterval.mul
              NearOneLocalInterval.piInterval
              NearOneLocalInterval.piInterval)).add
            (LeanSuffixReflective.QInterval.point (-14256)))))).add
    (ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure)
      firstBCorrectionRawEnclosure))

/-- Exact interval replay of `e = 6*a - 2*z + s*b`. -/
def firstERawEnclosure : QInterval :=
  ((scaledEnclosure 6 firstPhysicalARawEnclosure).add
    (scaledEnclosure (-2) firstZRawEnclosure)).add
  (ScalarSuffixCertificate.QInterval.mul
    firstSRawEnclosure firstPhysicalBRawEnclosure)

/-- Exact interval replay of the factor `R + s*e` in `V`. -/
def firstVInteriorRawEnclosure : QInterval :=
  firstRRawEnclosure.add
    (ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstERawEnclosure)

/-- Exact interval replay of `V = s*(R+s*e)`. -/
def firstTangentVRawEnclosure : QInterval :=
  ScalarSuffixCertificate.QInterval.mul
    firstSRawEnclosure firstVInteriorRawEnclosure

/-- Exact interval replay of `s^3`, shared by the two arctangent-addition
guards. -/
def firstSCubeRawEnclosure : QInterval :=
  ScalarSuffixCertificate.QInterval.mul
    (ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    firstSRawEnclosure

/-- Exact interval replay of the type-(iv) angle denominator
`1 + s*Y = 1 + s^2*A`. -/
def firstAngleDenFourRawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 1).add
    (ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure)
      firstARawEnclosure)

private theorem firstAngleDenFourRaw_lo_pos :
    0 < firstAngleDenFourRawEnclosure.lo := by
  norm_num [firstAngleDenFourRawEnclosure, firstARawEnclosure,
    firstZRawEnclosure, firstURawEnclosure, firstSRawEnclosure,
    scaledEnclosure, affineEnclosure, firstMuInterval, firstTauDisplacement,
    firstUDisplacement, firstMuMid, firstTauCenter, firstTauSlope,
    firstUCenter, firstUSlope, firstScale, NearOneLocalInterval.piInterval,
    ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]

/-- Exact interval replay of the type-(iii) angle denominator
`1 + W*V = 1 + s^2*R*(R+s*e)`. -/
def firstAngleDenThreeRawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 1).add
    (ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstRRawEnclosure firstVInteriorRawEnclosure)
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure))

private theorem firstAngleDenThreeRaw_lo_pos :
    0 < firstAngleDenThreeRawEnclosure.lo := by
  norm_num [firstAngleDenThreeRawEnclosure, firstVInteriorRawEnclosure,
    firstERawEnclosure, firstPhysicalBRawEnclosure,
    firstBCorrectionRawEnclosure, firstRRawEnclosure,
    firstPhysicalARawEnclosure, firstVRawEnclosure, firstZRawEnclosure,
    firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
    firstMuInterval, firstTauDisplacement, firstUDisplacement,
    firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
    firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
    firstVCenter, firstVSlope, firstBCorrectionCenter,
    firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
    ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]

/-- Exact interval DAG for `1 - s*q4`, where
`q4 = s^2*z/(1+s*Y)`. -/
def firstAtanGuardFourRawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 1).sub
    (ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.divPos firstZRawEnclosure
        firstAngleDenFourRawEnclosure firstAngleDenFourRaw_lo_pos)
      firstSCubeRawEnclosure)

/-- Exact interval DAG for `1 - W*q3`, where
`q3 = s^2*e/(1+W*V)`. -/
def firstAtanGuardThreeRawEnclosure : QInterval :=
  (LeanSuffixReflective.QInterval.point 1).sub
    (ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSCubeRawEnclosure firstRRawEnclosure)
      (ScalarSuffixCertificate.QInterval.divPos firstERawEnclosure
        firstAngleDenThreeRawEnclosure firstAngleDenThreeRaw_lo_pos))

private theorem firstZRawEnclosure_sound {s u : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hu : firstURawEnclosure.RealContains u) :
    firstZRawEnclosure.RealContains
      (Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)
    le_rfl le_rfl hpi hpi
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  apply LeanSuffixReflective.QInterval.realContains_add hpi
  apply LeanSuffixReflective.QInterval.realContains_add
  · simpa [pow_two] using NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        (ScalarSuffixCertificate.QInterval.mul
          NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)
        firstSRawEnclosure)
      le_rfl le_rfl hpiSq hs
  · simpa [pow_two] using NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul firstURawEnclosure
        (ScalarSuffixCertificate.QInterval.mul
          firstSRawEnclosure firstSRawEnclosure))
      le_rfl le_rfl hu hsSq

private theorem firstPhysicalARawEnclosure_sound {s v : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hv : firstVRawEnclosure.RealContains v) :
    firstPhysicalARawEnclosure.RealContains
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v)) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)
    le_rfl le_rfl hpi hpi
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have hfivePi := scaledEnclosure_sound (5 / 12) _ hpi
  have hfortyThreePiSq := scaledEnclosure_sound 43 _ hpiSq
  have hcoefficientSum :=
    LeanSuffixReflective.QInterval.realContains_add hfortyThreePiSq
      ((LeanSuffixReflective.QInterval.realContains_point (1056 : ℚ)
        (1056 : ℝ)).2 (by norm_num))
  have hcoefficient := scaledEnclosure_sound (1 / 144) _ hcoefficientSum
  have hlinear := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
      (scaledEnclosure (1 / 144)
        ((scaledEnclosure 43
          (ScalarSuffixCertificate.QInterval.mul
            NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)).add
          (LeanSuffixReflective.QInterval.point 1056))))
    le_rfl le_rfl hs hcoefficient
  have hquadratic := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure)
      firstVRawEnclosure)
    le_rfl le_rfl hsSq hv
  exact LeanSuffixReflective.QInterval.realContains_add hfivePi
    (LeanSuffixReflective.QInterval.realContains_add hlinear hquadratic)

private theorem firstPhysicalBRawEnclosure_sound {s w : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hw : firstBCorrectionRawEnclosure.RealContains w) :
    firstPhysicalBRawEnclosure.RealContains
      (((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
        (s * (((1 / 216 : ℚ) : ℝ) *
          (Real.pi *
            (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
          (s * s) * w)) := by
  have hpi := NearOneLocalInterval.piInterval_sound
  have hpiSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)
    le_rfl le_rfl hpi hpi
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have hbaseB := LeanSuffixReflective.QInterval.realContains_add
    ((LeanSuffixReflective.QInterval.realContains_point (-44 : ℚ)
      (-44 : ℝ)).2 (by norm_num))
    (scaledEnclosure_sound (19 / 24) _ hpiSq)
  have hpiDifference := LeanSuffixReflective.QInterval.realContains_add
    (scaledEnclosure_sound 295 _ hpiSq)
    ((LeanSuffixReflective.QInterval.realContains_point (-14256 : ℚ)
      (-14256 : ℝ)).2 (by norm_num))
  have hpiProduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      NearOneLocalInterval.piInterval
      ((scaledEnclosure 295
        (ScalarSuffixCertificate.QInterval.mul
          NearOneLocalInterval.piInterval NearOneLocalInterval.piInterval)).add
        (LeanSuffixReflective.QInterval.point (-14256))))
    le_rfl le_rfl hpi hpiDifference
  have hbCoefficient := scaledEnclosure_sound (1 / 216) _ hpiProduct
  have hbLinear := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul firstSRawEnclosure
      (scaledEnclosure (1 / 216)
        (ScalarSuffixCertificate.QInterval.mul NearOneLocalInterval.piInterval
          ((scaledEnclosure 295
            (ScalarSuffixCertificate.QInterval.mul
              NearOneLocalInterval.piInterval
              NearOneLocalInterval.piInterval)).add
            (LeanSuffixReflective.QInterval.point (-14256))))))
    le_rfl le_rfl hs hbCoefficient
  have hbQuadratic := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure)
      firstBCorrectionRawEnclosure)
    le_rfl le_rfl hsSq hw
  exact LeanSuffixReflective.QInterval.realContains_add hbaseB
    (LeanSuffixReflective.QInterval.realContains_add hbLinear hbQuadratic)

private theorem firstERawEnclosure_sound {s z a b : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z)
    (ha : firstPhysicalARawEnclosure.RealContains a)
    (hb : firstPhysicalBRawEnclosure.RealContains b) :
    firstERawEnclosure.RealContains
      (NearOneAnalyticSystem.eCoord s z a b) := by
  have he := LeanSuffixReflective.QInterval.realContains_add
    (LeanSuffixReflective.QInterval.realContains_add
      (scaledEnclosure_sound 6 _ ha)
      (scaledEnclosure_sound (-2) _ hz))
    (NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstPhysicalBRawEnclosure)
      le_rfl le_rfl hs hb)
  simpa [firstERawEnclosure, NearOneAnalyticSystem.eCoord, sub_eq_add_neg] using he

private theorem firstSCubeRawEnclosure_sound {s : ℝ}
    (hs : firstSRawEnclosure.RealContains s) :
    firstSCubeRawEnclosure.RealContains (s ^ 3) := by
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  simpa [firstSCubeRawEnclosure, pow_succ, pow_two] using
    NearOneLocalInterval.outwardMul_sound
      (outer := firstSCubeRawEnclosure) le_rfl le_rfl hsSq hs

private theorem firstARawEnclosure_sound {s z : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z) :
    firstARawEnclosure.RealContains
      (NearOneAnalyticSystem.aCoord s z) := by
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstZRawEnclosure)
    le_rfl le_rfl hs hz
  simpa [firstARawEnclosure, NearOneAnalyticSystem.aCoord] using
    LeanSuffixReflective.QInterval.realContains_add
      ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
        (by norm_num))
      hproduct

private theorem firstRRawEnclosure_sound {s a : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (ha : firstPhysicalARawEnclosure.RealContains a) :
    firstRRawEnclosure.RealContains
      (NearOneAnalyticSystem.rCoord s a) := by
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstPhysicalARawEnclosure)
    le_rfl le_rfl hs ha
  simpa [firstRRawEnclosure, NearOneAnalyticSystem.rCoord] using
    LeanSuffixReflective.QInterval.realContains_add
      ((LeanSuffixReflective.QInterval.realContains_point (2 : ℚ) (2 : ℝ)).2
        (by norm_num))
      hproduct

private theorem firstVInteriorRawEnclosure_sound {s z a b : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hr : firstRRawEnclosure.RealContains
      (NearOneAnalyticSystem.rCoord s a))
    (he : firstERawEnclosure.RealContains
      (NearOneAnalyticSystem.eCoord s z a b)) :
    firstVInteriorRawEnclosure.RealContains
      (NearOneAnalyticSystem.rCoord s a +
        s * NearOneAnalyticSystem.eCoord s z a b) := by
  exact LeanSuffixReflective.QInterval.realContains_add hr
    (NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstERawEnclosure)
      le_rfl le_rfl hs he)

private theorem firstAngleDenFourRawEnclosure_sound {s z : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z) :
    firstAngleDenFourRawEnclosure.RealContains
      (1 + s * NearOneAnalyticSystem.yCoord s z) := by
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have ha := firstARawEnclosure_sound hs hz
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure)
      firstARawEnclosure)
    le_rfl le_rfl hsSq ha
  have hden := LeanSuffixReflective.QInterval.realContains_add
    ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
      (by norm_num))
    hproduct
  simpa [firstAngleDenFourRawEnclosure, NearOneAnalyticSystem.yCoord, pow_two,
    mul_assoc] using hden

private theorem firstAngleDenThreeRawEnclosure_sound {s z a b : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z)
    (ha : firstPhysicalARawEnclosure.RealContains a)
    (hb : firstPhysicalBRawEnclosure.RealContains b) :
    firstAngleDenThreeRawEnclosure.RealContains
      (1 + NearOneAnalyticSystem.wCoord s a *
        NearOneAnalyticSystem.vCoord s z a b) := by
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have hr := firstRRawEnclosure_sound hs ha
  have he := firstERawEnclosure_sound hs hz ha hb
  have hinterior := firstVInteriorRawEnclosure_sound hs hr he
  have hri := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstRRawEnclosure firstVInteriorRawEnclosure)
    le_rfl le_rfl hr hinterior
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstRRawEnclosure firstVInteriorRawEnclosure)
      (ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstSRawEnclosure))
    le_rfl le_rfl hri hsSq
  have hden := LeanSuffixReflective.QInterval.realContains_add
    ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
      (by norm_num))
    hproduct
  have hidentity :
      1 + NearOneAnalyticSystem.wCoord s a *
          NearOneAnalyticSystem.vCoord s z a b =
        1 + (NearOneAnalyticSystem.rCoord s a *
          (NearOneAnalyticSystem.rCoord s a +
            s * NearOneAnalyticSystem.eCoord s z a b)) * (s * s) := by
    simp only [NearOneAnalyticSystem.wCoord, NearOneAnalyticSystem.vCoord]
    ring
  rw [hidentity]
  simpa [firstAngleDenThreeRawEnclosure] using hden

private theorem firstAtanGuardFourRawEnclosure_sound {s z : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z) :
    firstAtanGuardFourRawEnclosure.RealContains
      (1 - s * (s ^ 2 * z /
        (1 + s * NearOneAnalyticSystem.yCoord s z))) := by
  have hden := firstAngleDenFourRawEnclosure_sound hs hz
  have hquot := ScalarSuffixCertificate.QInterval.realContains_divPos
    firstAngleDenFourRaw_lo_pos hz hden
  have hcube := firstSCubeRawEnclosure_sound hs
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.divPos firstZRawEnclosure
        firstAngleDenFourRawEnclosure firstAngleDenFourRaw_lo_pos)
      firstSCubeRawEnclosure)
    le_rfl le_rfl hquot hcube
  have hguard := LeanSuffixReflective.QInterval.realContains_sub
    ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
      (by norm_num))
    hproduct
  rw [show firstAtanGuardFourRawEnclosure =
    (LeanSuffixReflective.QInterval.point 1).sub
      (ScalarSuffixCertificate.QInterval.mul
        (ScalarSuffixCertificate.QInterval.divPos firstZRawEnclosure
          firstAngleDenFourRawEnclosure firstAngleDenFourRaw_lo_pos)
        firstSCubeRawEnclosure) by rfl]
  convert hguard using 1
  ring_nf

private theorem firstAtanGuardThreeRawEnclosure_sound {s z a b : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hz : firstZRawEnclosure.RealContains z)
    (ha : firstPhysicalARawEnclosure.RealContains a)
    (hb : firstPhysicalBRawEnclosure.RealContains b) :
    firstAtanGuardThreeRawEnclosure.RealContains
      (1 - NearOneAnalyticSystem.wCoord s a *
        (s ^ 2 * NearOneAnalyticSystem.eCoord s z a b /
          (1 + NearOneAnalyticSystem.wCoord s a *
            NearOneAnalyticSystem.vCoord s z a b))) := by
  have hden := firstAngleDenThreeRawEnclosure_sound hs hz ha hb
  have he := firstERawEnclosure_sound hs hz ha hb
  have hquot := ScalarSuffixCertificate.QInterval.realContains_divPos
    firstAngleDenThreeRaw_lo_pos he hden
  have hcube := firstSCubeRawEnclosure_sound hs
  have hr := firstRRawEnclosure_sound hs ha
  have hscaleR := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSCubeRawEnclosure firstRRawEnclosure)
    le_rfl le_rfl hcube hr
  have hproduct := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      (ScalarSuffixCertificate.QInterval.mul
        firstSCubeRawEnclosure firstRRawEnclosure)
      (ScalarSuffixCertificate.QInterval.divPos firstERawEnclosure
        firstAngleDenThreeRawEnclosure firstAngleDenThreeRaw_lo_pos))
    le_rfl le_rfl hscaleR hquot
  have hguard := LeanSuffixReflective.QInterval.realContains_sub
    ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
      (by norm_num))
    hproduct
  rw [show firstAtanGuardThreeRawEnclosure =
    (LeanSuffixReflective.QInterval.point 1).sub
      (ScalarSuffixCertificate.QInterval.mul
        (ScalarSuffixCertificate.QInterval.mul
          firstSCubeRawEnclosure firstRRawEnclosure)
        (ScalarSuffixCertificate.QInterval.divPos firstERawEnclosure
          firstAngleDenThreeRawEnclosure firstAngleDenThreeRaw_lo_pos)) by rfl]
  convert hguard using 1
  simp only [NearOneAnalyticSystem.wCoord]
  ring

/-- The outward-rounded 160-bit `s_pos` enclosure retained by the pilot. -/
def firstSPosCertificate : QInterval :=
  ⟨11556140516974047480096112024270003398637311 /
      1461501637330902918203684832716283019655932542976,
    5992372107790807623661100401797155643002211 /
      730750818665451459101842416358141509827966271488,
    by norm_num⟩

/-- The outward-rounded 160-bit `s_lt_one` enclosure retained by the pilot. -/
def firstSLtOneCertificate : QInterval :=
  ⟨730744826293343668294218755257739712672323269277 /
      730750818665451459101842416358141509827966271488,
    1461490081190385944156204736604258749652533905665 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `y_pos` enclosure retained by the pilot. -/
def firstYPosCertificate : QInterval :=
  ⟨2889106896606960252316245241283273475317895 /
      365375409332725729550921208179070754913983135744,
    11985052974345930786365333365167135306852341 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `y_lt_one` enclosure retained by the pilot. -/
def firstYLtOneCertificate : QInterval :=
  ⟨1461489652277928572272898467382917852520625690635 /
      1461501637330902918203684832716283019655932542976,
    365372520225829122590668891933829471640507817849 /
      365375409332725729550921208179070754913983135744,
    by norm_num⟩

/-- The outward-rounded 160-bit `w_pos` enclosure retained by the pilot. -/
def firstWPosCertificate : QInterval :=
  ⟨11556200325338594786047022782544419797159757 /
      730750818665451459101842416358141509827966271488,
    23969617085619547202827607308100181939037315 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `w_lt_one` enclosure retained by the pilot. -/
def firstWLtOneCertificate : QInterval :=
  ⟨1461477667713817298656482005108974919473993505661 /
      1461501637330902918203684832716283019655932542976,
    730739262465126120507056369335358965408169111731 /
      730750818665451459101842416358141509827966271488,
    by norm_num⟩

/-- The outward-rounded 160-bit `v_pos` enclosure retained by the pilot. -/
def firstVPosCertificate : QInterval :=
  ⟨11556272092249783933588164709725329162198957 /
      730750818665451459101842416358141509827966271488,
    23969771467276519447406003074280743117690323 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `v_lt_one` enclosure retained by the pilot. -/
def firstVLtOneCertificate : QInterval :=
  ⟨1461477667559435641684237426713208738912814852653 /
      1461501637330902918203684832716283019655932542976,
    730739262393359209317908828193431784498804072531 /
      730750818665451459101842416358141509827966271488,
    by norm_num⟩

/-- The outward-rounded 160-bit `y_gt_s` enclosure retained by the pilot. -/
def firstYGtSCertificate : QInterval :=
  ⟨71693318272839093579264830294933719705 /
      365375409332725729550921208179070754913983135744,
    308857491276908043688881579152278491479 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `v_gt_w` enclosure retained by the pilot. -/
def firstVGtWCertificate : QInterval :=
  ⟨143222607726950946197354081976415101745 /
      1461501637330902918203684832716283019655932542976,
    154594030269029358631689545176145408929 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `density_den` enclosure retained by the pilot. -/
def firstDensityDenCertificate : QInterval :=
  ⟨1461501637232619419144315701386355331148338972583 /
      1461501637330902918203684832716283019655932542976,
    1461501637239523603156011894210201826544579055769 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `angle_den_four` enclosure retained by the pilot. -/
def firstAngleDenFourCertificate : QInterval :=
  ⟨365375409355569990831888634744931032306915786387 /
      365375409332725729550921208179070754913983135744,
    1461501637429183885284948641207970488853827416879 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `angle_den_three` enclosure retained by the pilot. -/
def firstAngleDenThreeCertificate : QInterval :=
  ⟨182687704712051009044683066828075053237728598801 /
      182687704666362864775460604089535377456991567872,
    1461501637724023410870189088983379701259080623369 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `atan_guard_four` enclosure retained by the
pilot. -/
def firstAtanGuardFourCertificate : QInterval :=
  ⟨1461501637330900386290808452128479221442061738329 /
      1461501637330902918203684832716283019655932542976,
    1461501637330900648336268191005680461959919523781 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `atan_guard_three` enclosure retained by the
pilot. -/
def firstAtanGuardThreeCertificate : QInterval :=
  ⟨1461501637330900386239910573262799049409951765717 /
      1461501637330902918203684832716283019655932542976,
    182687704666362581042353153004953085753881859979 /
      182687704666362864775460604089535377456991567872,
    by norm_num⟩

/-- The outward-rounded 160-bit `height_order` enclosure retained by the
pilot. -/
def firstHeightOrderCertificate : QInterval :=
  ⟨2923063786016638488975614378721634835189376010465 /
      1461501637330902918203684832716283019655932542976,
    2923066030454369575519963946948057790399520382891 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- The outward-rounded 160-bit `A_pos` enclosure retained by the pilot. -/
def firstAPosCertificate : QInterval :=
  ⟨91346121432432879475998000548931221071276797809 /
      91343852333181432387730302044767688728495783936,
    1461539289485297731677400514752440956139406890031 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩


/-- The exact affine predictor data kernel-replay the retained `s_pos` guard. -/
theorem first_s_pos_enclosure {μ dτ : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ) :
    firstSPosCertificate.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) := by
  apply NearOneLocalInterval.realContains_of_subset
    (inner := firstSRawEnclosure)
  · norm_num [firstSRawEnclosure, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstScale, firstSPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]
  · norm_num [firstSRawEnclosure, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstScale, firstSPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]
  · exact scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)

/-- The same predictor data kernel-replay the retained `s_lt_one` guard. -/
theorem first_s_lt_one_enclosure {μ dτ : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ) :
    firstSLtOneCertificate.RealContains
      (1 - (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) := by
  have hs := first_s_pos_enclosure hμ hdτ
  constructor
  · have hbound :
        (firstSLtOneCertificate.lo : ℝ) ≤ 1 - (firstSPosCertificate.hi : ℝ) := by
      norm_num [firstSLtOneCertificate, firstSPosCertificate]
    exact hbound.trans (sub_le_sub_left hs.2 1)
  · have hbound :
        1 - (firstSPosCertificate.lo : ℝ) ≤ (firstSLtOneCertificate.hi : ℝ) := by
      norm_num [firstSLtOneCertificate, firstSPosCertificate]
    exact (sub_le_sub_left hs.1 1).trans hbound

/-- The adjoining subslab stays in the positive principal scale chart. -/
theorem first_scale_principal {μ dτ : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ) :
    0 < (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ) ∧
      (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ) < 1 := by
  constructor
  · exact ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_s_pos_enclosure hμ hdτ) (by norm_num [firstSPosCertificate])
  · have hone := ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_s_lt_one_enclosure hμ hdτ) (by norm_num [firstSLtOneCertificate])
    linarith

/-- The exact affine predictors and shared interval DAG primitives replay the
retained `y_pos` guard for the actual local coordinate `Y = s*(1+s*z)`. -/
theorem first_y_pos_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstYPosCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       NearOneAnalyticSystem.yCoord s z) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hu : firstURawEnclosure.RealContains
      ((firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) :=
    affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu
  have hz := firstZRawEnclosure_sound hs hu
  have ha : firstARawEnclosure.RealContains
      (1 + ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) *
        (Real.pi + (Real.pi ^ 2 *
          ((firstScale : ℝ) *
            ((firstTauCenter : ℝ) +
              (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) +
          ((firstUCenter : ℝ) +
            (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) *
            ((firstScale : ℝ) *
              ((firstTauCenter : ℝ) +
                (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) ^ 2))) := by
    exact LeanSuffixReflective.QInterval.realContains_add
      ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
        (by norm_num))
      (NearOneLocalInterval.outwardMul_sound
        (outer := ScalarSuffixCertificate.QInterval.mul
          firstSRawEnclosure firstZRawEnclosure)
        le_rfl le_rfl hs hz)
  have hy := NearOneLocalInterval.outwardMul_sound
    (left := firstSRawEnclosure) (right := firstARawEnclosure)
    (outer := firstYPosCertificate)
    (by
      norm_num [firstYPosCertificate, firstARawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    (by
      norm_num [firstYPosCertificate, firstARawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    hs ha
  simpa [NearOneAnalyticSystem.yCoord, NearOneAnalyticSystem.aCoord] using hy

/-- The same generated expression replay certifies the retained `y_lt_one`
guard. -/
theorem first_y_lt_one_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstYLtOneCertificate.RealContains
      (1 -
        (let s :=
          (firstScale : ℝ) *
            ((firstTauCenter : ℝ) +
              (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
         let u :=
          (firstUCenter : ℝ) +
            (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
         let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
         NearOneAnalyticSystem.yCoord s z)) := by
  have hy := first_y_pos_enclosure hμ hdτ hdu
  constructor
  · have hbound :
        (firstYLtOneCertificate.lo : ℝ) ≤
          1 - (firstYPosCertificate.hi : ℝ) := by
      norm_num [firstYLtOneCertificate, firstYPosCertificate]
    exact hbound.trans (sub_le_sub_left hy.2 1)
  · have hbound :
        1 - (firstYPosCertificate.lo : ℝ) ≤
          (firstYLtOneCertificate.hi : ℝ) := by
      norm_num [firstYLtOneCertificate, firstYPosCertificate]
    exact (sub_le_sub_left hy.1 1).trans hbound

/-- The adjoining subslab keeps the actual type-(iv) upper tangent coordinate
in the principal chart. -/
theorem first_y_principal {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    0 < NearOneAnalyticSystem.yCoord s z ∧
      NearOneAnalyticSystem.yCoord s z < 1 := by
  dsimp only
  constructor
  · exact ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_y_pos_enclosure hμ hdτ hdu) (by norm_num [firstYPosCertificate])
  · have hone := ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_y_lt_one_enclosure hμ hdτ hdu)
      (by norm_num [firstYLtOneCertificate])
    dsimp only at hone
    linarith

/-- The third saved affine predictor and shared interval DAG primitives replay
the retained `w_pos` guard for the actual coordinate `W = s*(2+s*a)`. -/
theorem first_w_pos_enclosure {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    firstWPosCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       NearOneAnalyticSystem.wCoord s a) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hv : firstVRawEnclosure.RealContains
      ((firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv) :=
    affineEnclosure_sound firstMuInterval firstVDisplacement
      firstMuMid firstVCenter firstVSlope hμ hdv
  have ha := firstPhysicalARawEnclosure_sound hs hv
  have hr := LeanSuffixReflective.QInterval.realContains_add
    ((LeanSuffixReflective.QInterval.realContains_point (2 : ℚ) (2 : ℝ)).2
      (by norm_num))
    (NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstPhysicalARawEnclosure)
      le_rfl le_rfl hs ha)
  have hw := NearOneLocalInterval.outwardMul_sound
    (left := firstSRawEnclosure) (right := firstRRawEnclosure)
    (outer := firstWPosCertificate)
    (by
      norm_num [firstWPosCertificate, firstRRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstSRawEnclosure,
        scaledEnclosure, affineEnclosure, firstMuInterval,
        firstTauDisplacement, firstVDisplacement, firstMuMid, firstTauCenter,
        firstTauSlope, firstVCenter, firstVSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    (by
      norm_num [firstWPosCertificate, firstRRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstSRawEnclosure,
        scaledEnclosure, affineEnclosure, firstMuInterval,
        firstTauDisplacement, firstVDisplacement, firstMuMid, firstTauCenter,
        firstTauSlope, firstVCenter, firstVSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    hs hr
  simpa [NearOneAnalyticSystem.wCoord, NearOneAnalyticSystem.rCoord] using hw

/-- The same generated expression replay certifies the retained `w_lt_one`
guard. -/
theorem first_w_lt_one_enclosure {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    firstWLtOneCertificate.RealContains
      (1 -
        (let s :=
          (firstScale : ℝ) *
            ((firstTauCenter : ℝ) +
              (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
         let v :=
          (firstVCenter : ℝ) +
            (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
         let a :=
          (((5 / 12 : ℚ) : ℝ) * Real.pi +
            (s * (((1 / 144 : ℚ) : ℝ) *
              (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
              (s * s) * v))
         NearOneAnalyticSystem.wCoord s a)) := by
  have hw := first_w_pos_enclosure hμ hdτ hdv
  constructor
  · have hbound :
        (firstWLtOneCertificate.lo : ℝ) ≤
          1 - (firstWPosCertificate.hi : ℝ) := by
      norm_num [firstWLtOneCertificate, firstWPosCertificate]
    exact hbound.trans (sub_le_sub_left hw.2 1)
  · have hbound :
        1 - (firstWPosCertificate.lo : ℝ) ≤
          (firstWLtOneCertificate.hi : ℝ) := by
      norm_num [firstWLtOneCertificate, firstWPosCertificate]
    exact (sub_le_sub_left hw.1 1).trans hbound

/-- The adjoining subslab keeps the actual type-(iii) lower tangent coordinate
in the principal chart. -/
theorem first_w_principal {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    0 < NearOneAnalyticSystem.wCoord s a ∧
      NearOneAnalyticSystem.wCoord s a < 1 := by
  dsimp only
  constructor
  · exact ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_w_pos_enclosure hμ hdτ hdv) (by norm_num [firstWPosCertificate])
  · have hone := ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_w_lt_one_enclosure hμ hdτ hdv)
      (by norm_num [firstWLtOneCertificate])
    dsimp only at hone
    linarith


/-- The fourth saved affine predictor and shared interval DAG primitives replay
the retained `v_pos` guard for the actual coordinate `V = s*(R+s*e)`. -/
theorem first_v_pos_enclosure {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    firstVPosCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let w :=
        (firstBCorrectionCenter : ℝ) +
          (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       let b :=
        ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
          (s * (((1 / 216 : ℚ) : ℝ) *
            (Real.pi *
              (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
            (s * s) * w)
       NearOneAnalyticSystem.vCoord s z a b) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hu : firstURawEnclosure.RealContains
      ((firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) :=
    affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu
  have hv : firstVRawEnclosure.RealContains
      ((firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv) :=
    affineEnclosure_sound firstMuInterval firstVDisplacement
      firstMuMid firstVCenter firstVSlope hμ hdv
  have hw : firstBCorrectionRawEnclosure.RealContains
      ((firstBCorrectionCenter : ℝ) +
        (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw) :=
    affineEnclosure_sound firstMuInterval firstBCorrectionDisplacement
      firstMuMid firstBCorrectionCenter firstBCorrectionSlope hμ hdw
  have hz := firstZRawEnclosure_sound hs hu
  have ha := firstPhysicalARawEnclosure_sound hs hv
  have hb := firstPhysicalBRawEnclosure_sound hs hw
  have he := firstERawEnclosure_sound hs hz ha hb
  have hr := LeanSuffixReflective.QInterval.realContains_add
    ((LeanSuffixReflective.QInterval.realContains_point (2 : ℚ) (2 : ℝ)).2
      (by norm_num))
    (NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstPhysicalARawEnclosure)
      le_rfl le_rfl hs ha)
  have hinterior := LeanSuffixReflective.QInterval.realContains_add hr
    (NearOneLocalInterval.outwardMul_sound
      (outer := ScalarSuffixCertificate.QInterval.mul
        firstSRawEnclosure firstERawEnclosure)
      le_rfl le_rfl hs he)
  have hV := NearOneLocalInterval.outwardMul_sound
    (left := firstSRawEnclosure) (right := firstVInteriorRawEnclosure)
    (outer := firstVPosCertificate)
    (by
      norm_num [firstVPosCertificate, firstVInteriorRawEnclosure,
        firstERawEnclosure, firstPhysicalBRawEnclosure,
        firstBCorrectionRawEnclosure, firstRRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement,
        firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
        firstVCenter, firstVSlope, firstBCorrectionCenter,
        firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    (by
      norm_num [firstVPosCertificate, firstVInteriorRawEnclosure,
        firstERawEnclosure, firstPhysicalBRawEnclosure,
        firstBCorrectionRawEnclosure, firstRRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement,
        firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
        firstVCenter, firstVSlope, firstBCorrectionCenter,
        firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    hs hinterior
  simpa [NearOneAnalyticSystem.vCoord, NearOneAnalyticSystem.rCoord,
    NearOneAnalyticSystem.eCoord, pow_two, sub_eq_add_neg] using hV

/-- The same generated expression replay certifies the retained `v_lt_one`
guard. -/
theorem first_v_lt_one_enclosure {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    firstVLtOneCertificate.RealContains
      (1 -
        (let s :=
          (firstScale : ℝ) *
            ((firstTauCenter : ℝ) +
              (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
         let u :=
          (firstUCenter : ℝ) +
            (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
         let v :=
          (firstVCenter : ℝ) +
            (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
         let w :=
          (firstBCorrectionCenter : ℝ) +
            (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
         let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
         let a :=
          (((5 / 12 : ℚ) : ℝ) * Real.pi +
            (s * (((1 / 144 : ℚ) : ℝ) *
              (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
              (s * s) * v))
         let b :=
          ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
            (s * (((1 / 216 : ℚ) : ℝ) *
              (Real.pi *
                (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
              (s * s) * w)
         NearOneAnalyticSystem.vCoord s z a b)) := by
  have hV := first_v_pos_enclosure hμ hdτ hdu hdv hdw
  constructor
  · have hbound :
        (firstVLtOneCertificate.lo : ℝ) ≤
          1 - (firstVPosCertificate.hi : ℝ) := by
      norm_num [firstVLtOneCertificate, firstVPosCertificate]
    exact hbound.trans (sub_le_sub_left hV.2 1)
  · have hbound :
        1 - (firstVPosCertificate.lo : ℝ) ≤
          (firstVLtOneCertificate.hi : ℝ) := by
      norm_num [firstVLtOneCertificate, firstVPosCertificate]
    exact (sub_le_sub_left hV.1 1).trans hbound

/-- The adjoining subslab keeps the type-(iii) upper tangent coordinate in the
principal chart. -/
theorem first_v_principal {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let w :=
      (firstBCorrectionCenter : ℝ) +
        (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    let b :=
      ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
        (s * (((1 / 216 : ℚ) : ℝ) *
          (Real.pi *
            (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
          (s * s) * w)
    0 < NearOneAnalyticSystem.vCoord s z a b ∧
      NearOneAnalyticSystem.vCoord s z a b < 1 := by
  dsimp only
  constructor
  · exact ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_v_pos_enclosure hμ hdτ hdu hdv hdw)
      (by norm_num [firstVPosCertificate])
  · have hone := ScalarSuffixCertificate.QInterval.positive_of_realContains
      (first_v_lt_one_enclosure hμ hdτ hdu hdv hdw)
      (by norm_num [firstVLtOneCertificate])
    dsimp only at hone
    linarith

private theorem firstYGtS_of_raw {s u : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hu : firstURawEnclosure.RealContains u) :
    firstYGtSCertificate.RealContains
      (NearOneAnalyticSystem.yCoord s
        (Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)) - s) := by
  let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
  have hz : firstZRawEnclosure.RealContains z := by
    simpa only [z] using firstZRawEnclosure_sound hs hu
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have hdiff := NearOneLocalInterval.outwardMul_sound
    (left := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    (right := firstZRawEnclosure)
    (outer := firstYGtSCertificate)
    (by
      norm_num [firstYGtSCertificate, firstZRawEnclosure, firstURawEnclosure,
        firstSRawEnclosure, scaledEnclosure, affineEnclosure, firstMuInterval,
        firstTauDisplacement, firstUDisplacement, firstMuMid, firstTauCenter,
        firstTauSlope, firstUCenter, firstUSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    (by
      norm_num [firstYGtSCertificate, firstZRawEnclosure, firstURawEnclosure,
        firstSRawEnclosure, scaledEnclosure, affineEnclosure, firstMuInterval,
        firstTauDisplacement, firstUDisplacement, firstMuMid, firstTauCenter,
        firstTauSlope, firstUCenter, firstUSlope, firstScale,
        NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    hsSq hz
  have hidentity :
      NearOneAnalyticSystem.yCoord s z - s = s ^ 2 * z := by
    simp only [NearOneAnalyticSystem.yCoord, NearOneAnalyticSystem.aCoord]
    ring
  rw [show Real.pi + (Real.pi ^ 2 * s + u * s ^ 2) = z by rfl, hidentity]
  simpa [pow_two] using hdiff

/-- The generated coordinate expression kernel-replays the retained `y_gt_s`
guard, including the dependency cancellation `Y - s = s^2*z`. -/
theorem first_y_gt_s_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstYGtSCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       NearOneAnalyticSystem.yCoord s z - s) := by
  exact firstYGtS_of_raw
    (scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ))
    (affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu)

private theorem firstVGtW_of_raw {s u v w : ℝ}
    (hs : firstSRawEnclosure.RealContains s)
    (hu : firstURawEnclosure.RealContains u)
    (hv : firstVRawEnclosure.RealContains v)
    (hw : firstBCorrectionRawEnclosure.RealContains w) :
    firstVGtWCertificate.RealContains
      (let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       let b :=
        ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
          (s * (((1 / 216 : ℚ) : ℝ) *
            (Real.pi *
              (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
            (s * s) * w)
       NearOneAnalyticSystem.vCoord s z a b -
         NearOneAnalyticSystem.wCoord s a) := by
  let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
  let a :=
    (((5 / 12 : ℚ) : ℝ) * Real.pi +
      (s * (((1 / 144 : ℚ) : ℝ) *
        (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
        (s * s) * v))
  let b :=
    ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
      (s * (((1 / 216 : ℚ) : ℝ) *
        (Real.pi *
          (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
        (s * s) * w)
  have hz : firstZRawEnclosure.RealContains z := by
    simpa only [z] using firstZRawEnclosure_sound hs hu
  have ha : firstPhysicalARawEnclosure.RealContains a := by
    simpa only [a] using firstPhysicalARawEnclosure_sound hs hv
  have hb : firstPhysicalBRawEnclosure.RealContains b := by
    simpa only [b] using firstPhysicalBRawEnclosure_sound hs hw
  have he := firstERawEnclosure_sound hs hz ha hb
  have hsSq := NearOneLocalInterval.outwardMul_sound
    (outer := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    le_rfl le_rfl hs hs
  have hdiff := NearOneLocalInterval.outwardMul_sound
    (left := ScalarSuffixCertificate.QInterval.mul
      firstSRawEnclosure firstSRawEnclosure)
    (right := firstERawEnclosure)
    (outer := firstVGtWCertificate)
    (by
      norm_num [firstVGtWCertificate, firstERawEnclosure,
        firstPhysicalBRawEnclosure, firstBCorrectionRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement,
        firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
        firstVCenter, firstVSlope, firstBCorrectionCenter,
        firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    (by
      norm_num [firstVGtWCertificate, firstERawEnclosure,
        firstPhysicalBRawEnclosure, firstBCorrectionRawEnclosure,
        firstPhysicalARawEnclosure, firstVRawEnclosure, firstZRawEnclosure,
        firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
        firstMuInterval, firstTauDisplacement, firstUDisplacement,
        firstVDisplacement, firstBCorrectionDisplacement, firstMuMid,
        firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
        firstVCenter, firstVSlope, firstBCorrectionCenter,
        firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg])
    hsSq he
  have hidentity :
      NearOneAnalyticSystem.vCoord s z a b -
          NearOneAnalyticSystem.wCoord s a =
        s ^ 2 * NearOneAnalyticSystem.eCoord s z a b := by
    simp only [NearOneAnalyticSystem.vCoord, NearOneAnalyticSystem.wCoord,
      NearOneAnalyticSystem.rCoord]
    ring
  dsimp only
  rw [hidentity]
  simpa [pow_two] using hdiff

/-- The generated coordinate expression kernel-replays the retained `v_gt_w`
guard, including the dependency cancellation `V - W = s^2*e`. -/
theorem first_v_gt_w_enclosure {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    firstVGtWCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let w :=
        (firstBCorrectionCenter : ℝ) +
          (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       let b :=
        ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
          (s * (((1 / 216 : ℚ) : ℝ) *
            (Real.pi *
              (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
            (s * s) * w)
       NearOneAnalyticSystem.vCoord s z a b -
         NearOneAnalyticSystem.wCoord s a) := by
  exact firstVGtW_of_raw
    (scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ))
    (affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu)
    (affineEnclosure_sound firstMuInterval firstVDisplacement
      firstMuMid firstVCenter firstVSlope hμ hdv)
    (affineEnclosure_sound firstMuInterval firstBCorrectionDisplacement
      firstMuMid firstBCorrectionCenter firstBCorrectionSlope hμ hdw)

/-- The seam-adjoining cell has the strict type-(iv) tangent order `s < Y`. -/
theorem first_s_lt_y {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    s < NearOneAnalyticSystem.yCoord s z := by
  have hpos := ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_y_gt_s_enclosure hμ hdτ hdu)
    (by norm_num [firstYGtSCertificate])
  dsimp only at hpos ⊢
  linarith

/-- The seam-adjoining cell has the strict type-(iii) tangent order `W < V`. -/
theorem first_w_lt_v {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let w :=
      (firstBCorrectionCenter : ℝ) +
        (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    let b :=
      ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
        (s * (((1 / 216 : ℚ) : ℝ) *
          (Real.pi *
            (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
          (s * s) * w)
    NearOneAnalyticSystem.wCoord s a <
      NearOneAnalyticSystem.vCoord s z a b := by
  have hpos := ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_v_gt_w_enclosure hμ hdτ hdu hdv hdw)
    (by norm_num [firstVGtWCertificate])
  dsimp only at hpos ⊢
  linarith

private theorem firstDensityDen_of_coordinate {y : ℝ}
    (hy : firstYPosCertificate.RealContains y) :
    firstDensityDenCertificate.RealContains (1 - y ^ 2) := by
  let product : QInterval :=
    ScalarSuffixCertificate.QInterval.mul
      firstYPosCertificate firstYPosCertificate
  let inner : QInterval :=
    (LeanSuffixReflective.QInterval.point 1).sub product
  have hySq : product.RealContains (y * y) :=
    NearOneLocalInterval.outwardMul_sound
      (outer := product) le_rfl le_rfl hy hy
  have hinner : inner.RealContains (1 - y * y) := by
    exact LeanSuffixReflective.QInterval.realContains_sub
      ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
        (by norm_num))
      hySq
  apply NearOneLocalInterval.realContains_of_subset
    (inner := inner)
  · norm_num [inner, product, firstDensityDenCertificate, firstYPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]
  · norm_num [inner, product, firstDensityDenCertificate, firstYPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]
  · simpa [pow_two] using hinner

private theorem firstAngleDenFour_of_coordinates {s y : ℝ}
    (hs : firstSPosCertificate.RealContains s)
    (hy : firstYPosCertificate.RealContains y) :
    firstAngleDenFourCertificate.RealContains (1 + s * y) := by
  let product : QInterval :=
    ScalarSuffixCertificate.QInterval.mul firstSPosCertificate firstYPosCertificate
  let inner : QInterval :=
    (LeanSuffixReflective.QInterval.point 1).add product
  have hproduct : product.RealContains (s * y) :=
    NearOneLocalInterval.outwardMul_sound
      (outer := product) le_rfl le_rfl hs hy
  have hinner : inner.RealContains (1 + s * y) := by
    exact LeanSuffixReflective.QInterval.realContains_add
      ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
        (by norm_num))
      hproduct
  apply NearOneLocalInterval.realContains_of_subset
    (inner := inner)
  · norm_num [inner, product, firstAngleDenFourCertificate,
      firstSPosCertificate, firstYPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg]
  · norm_num [inner, product, firstAngleDenFourCertificate,
      firstSPosCertificate, firstYPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg]
  · exact hinner

private theorem firstAngleDenThree_of_coordinates {w v : ℝ}
    (hw : firstWPosCertificate.RealContains w)
    (hv : firstVPosCertificate.RealContains v) :
    firstAngleDenThreeCertificate.RealContains (1 + w * v) := by
  let product : QInterval :=
    ScalarSuffixCertificate.QInterval.mul firstWPosCertificate firstVPosCertificate
  let inner : QInterval :=
    (LeanSuffixReflective.QInterval.point 1).add product
  have hproduct : product.RealContains (w * v) :=
    NearOneLocalInterval.outwardMul_sound
      (outer := product) le_rfl le_rfl hw hv
  have hinner : inner.RealContains (1 + w * v) := by
    exact LeanSuffixReflective.QInterval.realContains_add
      ((LeanSuffixReflective.QInterval.realContains_point (1 : ℚ) (1 : ℝ)).2
        (by norm_num))
      hproduct
  apply NearOneLocalInterval.realContains_of_subset
    (inner := inner)
  · norm_num [inner, product, firstAngleDenThreeCertificate,
      firstWPosCertificate, firstVPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg]
  · norm_num [inner, product, firstAngleDenThreeCertificate,
      firstWPosCertificate, firstVPosCertificate,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg]
  · exact hinner

/-- The checked `Y` coordinate enclosure kernel-replays the retained
`density_den = 1 - Y^2` guard. -/
theorem first_density_den_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstDensityDenCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       1 - NearOneAnalyticSystem.yCoord s z ^ 2) := by
  dsimp only
  exact firstDensityDen_of_coordinate
    (first_y_pos_enclosure hμ hdτ hdu)

/-- The checked `s` and `Y` coordinate enclosures kernel-replay the retained
`angle_den_four = 1 + s*Y` guard. -/
theorem first_angle_den_four_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstAngleDenFourCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       1 + s * NearOneAnalyticSystem.yCoord s z) := by
  dsimp only
  exact firstAngleDenFour_of_coordinates
    (first_s_pos_enclosure hμ hdτ)
    (first_y_pos_enclosure hμ hdτ hdu)

/-- The checked `W` and `V` coordinate enclosures kernel-replay the retained
`angle_den_three = 1 + W*V` guard. -/
theorem first_angle_den_three_enclosure {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    firstAngleDenThreeCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let w :=
        (firstBCorrectionCenter : ℝ) +
          (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       let b :=
        ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
          (s * (((1 / 216 : ℚ) : ℝ) *
            (Real.pi *
              (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
            (s * s) * w)
       1 + NearOneAnalyticSystem.wCoord s a *
         NearOneAnalyticSystem.vCoord s z a b) := by
  dsimp only
  exact firstAngleDenThree_of_coordinates
    (first_w_pos_enclosure hμ hdτ hdv)
    (first_v_pos_enclosure hμ hdτ hdu hdv hdw)

private theorem firstAtanGuardFourRaw_subset :
    firstAtanGuardFourCertificate.lo ≤ firstAtanGuardFourRawEnclosure.lo ∧
      firstAtanGuardFourRawEnclosure.hi ≤ firstAtanGuardFourCertificate.hi := by
  constructor <;>
    norm_num [firstAtanGuardFourCertificate, firstAtanGuardFourRawEnclosure,
      firstSCubeRawEnclosure, firstAngleDenFourRawEnclosure,
      firstARawEnclosure, firstZRawEnclosure, firstURawEnclosure,
      firstSRawEnclosure, scaledEnclosure, affineEnclosure, firstMuInterval,
      firstTauDisplacement, firstUDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstUCenter, firstUSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]

private theorem firstAtanGuardThreeRaw_subset :
    firstAtanGuardThreeCertificate.lo ≤ firstAtanGuardThreeRawEnclosure.lo ∧
      firstAtanGuardThreeRawEnclosure.hi ≤ firstAtanGuardThreeCertificate.hi := by
  constructor <;>
    norm_num [firstAtanGuardThreeCertificate, firstAtanGuardThreeRawEnclosure,
      firstSCubeRawEnclosure, firstAngleDenThreeRawEnclosure,
      firstVInteriorRawEnclosure, firstERawEnclosure,
      firstPhysicalBRawEnclosure, firstBCorrectionRawEnclosure,
      firstRRawEnclosure, firstPhysicalARawEnclosure, firstVRawEnclosure,
      firstZRawEnclosure, firstURawEnclosure, firstSRawEnclosure,
      scaledEnclosure, affineEnclosure, firstMuInterval, firstTauDisplacement,
      firstUDisplacement, firstVDisplacement, firstBCorrectionDisplacement,
      firstMuMid, firstTauCenter, firstTauSlope, firstUCenter, firstUSlope,
      firstVCenter, firstVSlope, firstBCorrectionCenter,
      firstBCorrectionSlope, firstScale, NearOneLocalInterval.piInterval,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]

/-- The exact generated expression kernel-replays the retained
`atan_guard_four = 1 - s*q4` enclosure. -/
theorem first_atan_guard_four_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstAtanGuardFourCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       1 - s * (s ^ 2 * z /
         (1 + s * NearOneAnalyticSystem.yCoord s z))) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hu : firstURawEnclosure.RealContains
      ((firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) :=
    affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu
  have hz := firstZRawEnclosure_sound hs hu
  exact NearOneLocalInterval.realContains_of_subset
    firstAtanGuardFourRaw_subset.1 firstAtanGuardFourRaw_subset.2
    (firstAtanGuardFourRawEnclosure_sound hs hz)

/-- The positive retained enclosure verifies the generated type-(iv)
arctangent-addition guard. -/
theorem first_atan_guard_four_positive {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    0 < 1 - s * (s ^ 2 * z /
      (1 + s * NearOneAnalyticSystem.yCoord s z)) := by
  exact ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_atan_guard_four_enclosure hμ hdτ hdu)
    (by norm_num [firstAtanGuardFourCertificate])

/-- The exact generated expression kernel-replays the retained
`atan_guard_three = 1 - W*q3` enclosure. -/
theorem first_atan_guard_three_enclosure {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    firstAtanGuardThreeCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let w :=
        (firstBCorrectionCenter : ℝ) +
          (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       let b :=
        ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
          (s * (((1 / 216 : ℚ) : ℝ) *
            (Real.pi *
              (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
            (s * s) * w)
       1 - NearOneAnalyticSystem.wCoord s a *
         (s ^ 2 * NearOneAnalyticSystem.eCoord s z a b /
           (1 + NearOneAnalyticSystem.wCoord s a *
             NearOneAnalyticSystem.vCoord s z a b))) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hu : firstURawEnclosure.RealContains
      ((firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) :=
    affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu
  have hv : firstVRawEnclosure.RealContains
      ((firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv) :=
    affineEnclosure_sound firstMuInterval firstVDisplacement
      firstMuMid firstVCenter firstVSlope hμ hdv
  have hw : firstBCorrectionRawEnclosure.RealContains
      ((firstBCorrectionCenter : ℝ) +
        (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw) :=
    affineEnclosure_sound firstMuInterval firstBCorrectionDisplacement
      firstMuMid firstBCorrectionCenter firstBCorrectionSlope hμ hdw
  have hz := firstZRawEnclosure_sound hs hu
  have ha := firstPhysicalARawEnclosure_sound hs hv
  have hb := firstPhysicalBRawEnclosure_sound hs hw
  exact NearOneLocalInterval.realContains_of_subset
    firstAtanGuardThreeRaw_subset.1 firstAtanGuardThreeRaw_subset.2
    (firstAtanGuardThreeRawEnclosure_sound hs hz ha hb)

/-- The positive retained enclosure verifies the generated type-(iii)
arctangent-addition guard. -/
theorem first_atan_guard_three_positive {μ dτ du dv dw : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du)
    (hdv : firstVDisplacement.RealContains dv)
    (hdw : firstBCorrectionDisplacement.RealContains dw) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let w :=
      (firstBCorrectionCenter : ℝ) +
        (firstBCorrectionSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dw
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    let b :=
      ((-44 : ℝ) + ((19 / 24 : ℚ) : ℝ) * (Real.pi * Real.pi)) +
        (s * (((1 / 216 : ℚ) : ℝ) *
          (Real.pi *
            (((295 : ℚ) : ℝ) * (Real.pi * Real.pi) - (14256 : ℝ)))) +
          (s * s) * w)
    0 < 1 - NearOneAnalyticSystem.wCoord s a *
      (s ^ 2 * NearOneAnalyticSystem.eCoord s z a b /
        (1 + NearOneAnalyticSystem.wCoord s a *
          NearOneAnalyticSystem.vCoord s z a b)) := by
  exact ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_atan_guard_three_enclosure hμ hdτ hdu hdv hdw)
    (by norm_num [firstAtanGuardThreeCertificate])

private theorem firstHeightOrderCertificate_corners :
    (firstHeightOrderCertificate.lo : ℝ) ≤
        heightOrderMargin firstSRawEnclosure.lo
          firstPhysicalARawEnclosure.lo ∧
      heightOrderMargin firstSRawEnclosure.hi
          firstPhysicalARawEnclosure.hi ≤
        (firstHeightOrderCertificate.hi : ℝ) := by
  constructor <;>
    norm_num [heightOrderMargin, firstHeightOrderCertificate,
      firstPhysicalARawEnclosure, firstVRawEnclosure, firstSRawEnclosure,
      scaledEnclosure, affineEnclosure, firstMuInterval,
      firstTauDisplacement, firstVDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstVCenter, firstVSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]

/-- The exact affine predictors kernel-replay the retained polynomial
`height_order = (1-s^2)*R^2-2` enclosure. -/
theorem first_height_order_enclosure {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    firstHeightOrderCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let v :=
        (firstVCenter : ℝ) +
          (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
       let a :=
        (((5 / 12 : ℚ) : ℝ) * Real.pi +
          (s * (((1 / 144 : ℚ) : ℝ) *
            (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
            (s * s) * v))
       (1 - s ^ 2) * NearOneAnalyticSystem.rCoord s a ^ 2 - 2) := by
  dsimp only
  let s : ℝ :=
    (firstScale : ℝ) *
      ((firstTauCenter : ℝ) +
        (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
  let v : ℝ :=
    (firstVCenter : ℝ) +
      (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
  let a : ℝ :=
    (((5 / 12 : ℚ) : ℝ) * Real.pi +
      (s * (((1 / 144 : ℚ) : ℝ) *
        (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
        (s * s) * v))
  have hs : firstSRawEnclosure.RealContains s :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hv : firstVRawEnclosure.RealContains v :=
    affineEnclosure_sound firstMuInterval firstVDisplacement
      firstMuMid firstVCenter firstVSlope hμ hdv
  have ha : firstPhysicalARawEnclosure.RealContains a :=
    firstPhysicalARawEnclosure_sound hs hv
  have hsLo0 : (0 : ℝ) ≤ firstSRawEnclosure.lo := by
    norm_num [firstSRawEnclosure, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstScale, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have hsHi1 : (firstSRawEnclosure.hi : ℝ) ≤ 1 / 100 := by
    norm_num [firstSRawEnclosure, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstScale, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have haLo1 : (1 : ℝ) ≤ firstPhysicalARawEnclosure.lo := by
    norm_num [firstPhysicalARawEnclosure, firstVRawEnclosure,
      firstSRawEnclosure, scaledEnclosure, affineEnclosure, firstMuInterval,
      firstTauDisplacement, firstVDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstVCenter, firstVSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have haHi2 : (firstPhysicalARawEnclosure.hi : ℝ) ≤ 2 := by
    norm_num [firstPhysicalARawEnclosure, firstVRawEnclosure,
      firstSRawEnclosure, scaledEnclosure, affineEnclosure, firstMuInterval,
      firstTauDisplacement, firstVDisplacement, firstMuMid, firstTauCenter,
      firstTauSlope, firstVCenter, firstVSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.neg]
  have hs0 : 0 ≤ s := hsLo0.trans hs.1
  have hs1 : s ≤ 1 / 100 := hs.2.trans hsHi1
  have ha0 : 1 ≤ a := haLo1.trans ha.1
  have ha1 : a ≤ 2 := ha.2.trans haHi2
  change firstHeightOrderCertificate.RealContains (heightOrderMargin s a)
  constructor
  · calc
      (firstHeightOrderCertificate.lo : ℝ) ≤
          heightOrderMargin firstSRawEnclosure.lo
            firstPhysicalARawEnclosure.lo :=
        firstHeightOrderCertificate_corners.1
      _ ≤ heightOrderMargin firstSRawEnclosure.lo a :=
        heightOrderMargin_mono_coordinate hsLo0
          ((hs.1.trans hs1).trans (by norm_num : (1 / 100 : ℝ) ≤ 1))
          (le_trans (by norm_num) haLo1) ha.1
      _ ≤ heightOrderMargin s a :=
        heightOrderMargin_mono_scale ha0 ha1 hsLo0 hs.1 hs1
  · calc
      heightOrderMargin s a ≤
          heightOrderMargin firstSRawEnclosure.hi a :=
        heightOrderMargin_mono_scale ha0 ha1 hs0 hs.2 hsHi1
      _ ≤ heightOrderMargin firstSRawEnclosure.hi
          firstPhysicalARawEnclosure.hi :=
        heightOrderMargin_mono_coordinate
          ((hsLo0.trans hs.1).trans hs.2)
          (hsHi1.trans (by norm_num : (1 / 100 : ℝ) ≤ 1))
          (le_trans (by norm_num) ha0) ha.2
      _ ≤ (firstHeightOrderCertificate.hi : ℝ) :=
        firstHeightOrderCertificate_corners.2

/-- The retained interval has positive polynomial height-order margin. -/
theorem first_height_order_positive {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    2 < (1 - s ^ 2) * NearOneAnalyticSystem.rCoord s a ^ 2 := by
  have hpos := ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_height_order_enclosure hμ hdτ hdv)
    (by norm_num [firstHeightOrderCertificate])
  dsimp only at hpos ⊢
  linarith

/-- The checked polynomial margin transports through `height_order_iff` to the
strict source height order used by the scalar consumer. -/
theorem first_strict_height_order {μ dτ dv : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdv : firstVDisplacement.RealContains dv) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let v :=
      (firstVCenter : ℝ) +
        (firstVSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dv
    let a :=
      (((5 / 12 : ℚ) : ℝ) * Real.pi +
        (s * (((1 / 144 : ℚ) : ℝ) *
          (((43 : ℚ) : ℝ) * (Real.pi * Real.pi) + (1056 : ℝ))) +
          (s * s) * v))
    (1 + NearOneAnalyticSystem.halfCos
        (NearOneAnalyticSystem.wCoord s a)) / 2 <
      NearOneAnalyticSystem.halfCos s := by
  dsimp only
  exact (NearOneLocalHeightOrder.height_order_iff
    (first_scale_principal hμ hdτ).1
    (first_scale_principal hμ hdτ).2).2
      (first_height_order_positive hμ hdτ hdv)

private theorem firstARaw_subset :
    firstAPosCertificate.lo ≤ firstARawEnclosure.lo ∧
      firstARawEnclosure.hi ≤ firstAPosCertificate.hi := by
  constructor <;>
    norm_num [firstAPosCertificate, firstARawEnclosure, firstZRawEnclosure,
      firstURawEnclosure, firstSRawEnclosure, scaledEnclosure, affineEnclosure,
      firstMuInterval, firstTauDisplacement, firstUDisplacement, firstMuMid,
      firstTauCenter, firstTauSlope, firstUCenter, firstUSlope, firstScale,
      NearOneLocalInterval.piInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg]

/-- The exact affine predictors kernel-replay the retained
`A_pos = 1 + s*z` enclosure. -/
theorem first_A_pos_enclosure {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    firstAPosCertificate.RealContains
      (let s :=
        (firstScale : ℝ) *
          ((firstTauCenter : ℝ) +
            (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
       let u :=
        (firstUCenter : ℝ) +
          (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
       let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
       NearOneAnalyticSystem.aCoord s z) := by
  dsimp only
  have hs : firstSRawEnclosure.RealContains
      ((firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)) :=
    scaledEnclosure_sound firstScale _
      (affineEnclosure_sound firstMuInterval firstTauDisplacement
        firstMuMid firstTauCenter firstTauSlope hμ hdτ)
  have hu : firstURawEnclosure.RealContains
      ((firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du) :=
    affineEnclosure_sound firstMuInterval firstUDisplacement
      firstMuMid firstUCenter firstUSlope hμ hdu
  have hz := firstZRawEnclosure_sound hs hu
  exact NearOneLocalInterval.realContains_of_subset
    firstARaw_subset.1 firstARaw_subset.2
    (firstARawEnclosure_sound hs hz)

/-- The retained enclosure proves the generated regularized coordinate
`A = 1 + s*z` is strictly positive. -/
theorem first_A_positive {μ dτ du : ℝ}
    (hμ : firstMuInterval.RealContains μ)
    (hdτ : firstTauDisplacement.RealContains dτ)
    (hdu : firstUDisplacement.RealContains du) :
    let s :=
      (firstScale : ℝ) *
        ((firstTauCenter : ℝ) +
          (firstTauSlope : ℝ) * (μ - (firstMuMid : ℝ)) + dτ)
    let u :=
      (firstUCenter : ℝ) +
        (firstUSlope : ℝ) * (μ - (firstMuMid : ℝ)) + du
    let z := Real.pi + (Real.pi ^ 2 * s + u * s ^ 2)
    0 < NearOneAnalyticSystem.aCoord s z := by
  exact ScalarSuffixCertificate.QInterval.positive_of_realContains
    (first_A_pos_enclosure hμ hdτ hdu)
    (by norm_num [firstAPosCertificate])
end FirstSeamCell

end NearOneLocalPredictor
