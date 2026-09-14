/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CompactCellAssembly

/-!
# Reusable exact-rational compact-cell certificates

Box-independent inverse-sine, atom, formula, and centered mean-value enclosure
machinery.  Concrete cells supply only rational intervals and discharge the
resulting rational inequalities with `norm_num`.
-/

open Real Set
noncomputable section

namespace CompactCellCertificate

abbrev QInterval := ScalarSuffixCertificate.QInterval

namespace QInterval

/-- Exact-rational wrapper around the degree-27 Taylor inverse-sine rule. -/
theorem realContains_arcsin_of_taylor
    (a : QInterval) (x : ℚ)
    (hx : (-1 : ℚ) ≤ x ∧ x ≤ 1)
    (hbranch : (a.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (a.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2))
    (hlo : (ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi ≤ x)
    (hhi : x ≤ (ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo) :
    a.RealContains (arcsin (x : ℝ)) := by
  apply ScalarSuffixCertificate.realContains_arcsin_of_sin_bounds
  · simpa [Set.mem_Icc] using (show ((-1 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1) by
      exact_mod_cast hx)
  · exact hbranch
  · exact (ScalarSuffixCertificate.sinTaylor27Interval_sound a.lo).2.trans
      (show ((ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi : ℝ) ≤
          (x : ℝ) by exact_mod_cast hlo)
  · exact (show (x : ℝ) ≤
        ((ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo : ℝ) by
      exact_mod_cast hhi).trans
      (ScalarSuffixCertificate.sinTaylor27Interval_sound a.hi).1

/-- Interval-input version of the inverse-sine Taylor wrapper. -/
theorem realContains_arcsin_of_taylor_interval
    (a xInterval : QInterval) (x : ℝ)
    (hx : xInterval.RealContains x)
    (hxUnit : (-1 : ℝ) ≤ x ∧ x ≤ 1)
    (hbranch : (a.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (a.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2))
    (hlo : (ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi ≤ xInterval.lo)
    (hhi : xInterval.hi ≤
      (ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo) :
    a.RealContains (arcsin x) := by
  apply ScalarSuffixCertificate.realContains_arcsin_of_sin_bounds hxUnit hbranch
  · exact (ScalarSuffixCertificate.sinTaylor27Interval_sound a.lo).2.trans
      (show ((ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi : ℝ) ≤ x by
        exact (show ((ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi : ℝ) ≤
          (xInterval.lo : ℝ) by exact_mod_cast hlo) |>.trans hx.1)
  · exact hx.2.trans
      ((show (xInterval.hi : ℝ) ≤
          ((ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo : ℝ) by
        exact_mod_cast hhi).trans
        (ScalarSuffixCertificate.sinTaylor27Interval_sound a.hi).1)

end QInterval

/-- Convexity of an enclosing rational interval, stated for an unordered pair. -/
theorem realContains_of_mem_uIcc {i : QInterval} {c h x : ℝ}
    (hc : i.RealContains c) (hh : i.RealContains h)
    (hx : x ∈ uIcc c h) : i.RealContains x := by
  rcases Set.mem_uIcc.mp hx with hx | hx
  · exact ⟨hc.1.trans hx.1, hx.2.trans hh.2⟩
  · exact ⟨hh.1.trans hx.1, hx.2.trans hc.2⟩

/-- Box-independent centered type-(iv) area enclosure. -/
theorem typeFourArea_centered_enclosure
    (lambdaInterval hInterval : QInterval) (center : ℚ)
    {lam h : ℝ}
    (_hlam : lambdaInterval.RealContains lam)
    (hh : hInterval.RealContains h)
    (hcenter : hInterval.RealContains (center : ℝ))
    (hlambda : 1 < lam)
    (hregular : ∀ {x : ℝ}, hInterval.RealContains x → x ∈ Ioo (0 : ℝ) 1)
    (base slope displacement : QInterval)
    (hbase : base.RealContains (LeanSuffixAnalytic.typeFourArea lam (center : ℝ)))
    (hslope : ∀ x, hInterval.RealContains x →
      slope.RealContains (LeanSuffixAnalytic.typeFourFold lam x / x ^ 3))
    (hdisplacement : displacement.RealContains (h - (center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeFourArea lam h) := by
  apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (LeanSuffixAnalytic.typeFourArea lam)
    (fun x => LeanSuffixAnalytic.typeFourFold lam x / x ^ 3)
  · intro x hx
    have hxSlab := realContains_of_mem_uIcc hcenter hh hx
    have hxReg := hregular hxSlab
    exact LeanSuffixAnalytic.hasDerivAt_typeFourArea
      hlambda hxReg.1 hxReg.2
  · exact hbase
  · intro x hx
    exact hslope x (realContains_of_mem_uIcc hcenter hh hx)
  · exact hdisplacement

/-- Box-independent centered type-(iv) perimeter enclosure. -/
theorem typeFourPerimeter_centered_enclosure
    (lambdaInterval hInterval : QInterval) (center : ℚ)
    {lam h : ℝ}
    (_hlam : lambdaInterval.RealContains lam)
    (hh : hInterval.RealContains h)
    (hcenter : hInterval.RealContains (center : ℝ))
    (hlambda : 1 < lam)
    (hregular : ∀ {x : ℝ}, hInterval.RealContains x → x ∈ Ioo (0 : ℝ) 1)
    (base slope displacement : QInterval)
    (hbase : base.RealContains (LeanSuffixAnalytic.typeFourPerimeter lam (center : ℝ)))
    (hslope : ∀ x, hInterval.RealContains x →
      slope.RealContains (LeanSuffixAnalytic.typeFourFold lam x / x ^ 2))
    (hdisplacement : displacement.RealContains (h - (center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeFourPerimeter lam h) := by
  apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (LeanSuffixAnalytic.typeFourPerimeter lam)
    (fun x => LeanSuffixAnalytic.typeFourFold lam x / x ^ 2)
  · intro x hx
    have hxSlab := realContains_of_mem_uIcc hcenter hh hx
    have hxReg := hregular hxSlab
    exact LeanSuffixAnalytic.hasDerivAt_typeFourPerimeter
      hlambda hxReg.1 hxReg.2
  · exact hbase
  · intro x hx
    exact hslope x (realContains_of_mem_uIcc hcenter hh hx)
  · exact hdisplacement

/-- Box-independent centered type-(iii) area enclosure. -/
theorem typeThreeArea_centered_enclosure
    (lambdaInterval hInterval : QInterval) (center : ℚ)
    {lam h : ℝ}
    (_hlam : lambdaInterval.RealContains lam)
    (hh : hInterval.RealContains h)
    (hcenter : hInterval.RealContains (center : ℝ))
    (hlambda : 1 < lam)
    (hregular : ∀ {x : ℝ}, hInterval.RealContains x → x ∈ Ioo (0 : ℝ) 1)
    (base slope displacement : QInterval)
    (hbase : base.RealContains (LeanSuffixAnalytic.typeThreeArea lam (center : ℝ)))
    (hslope : ∀ x, hInterval.RealContains x →
      slope.RealContains (LeanSuffixAnalytic.typeThreeFold lam x / x ^ 3))
    (hdisplacement : displacement.RealContains (h - (center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeThreeArea lam h) := by
  apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (LeanSuffixAnalytic.typeThreeArea lam)
    (fun x => LeanSuffixAnalytic.typeThreeFold lam x / x ^ 3)
  · intro x hx
    have hxSlab := realContains_of_mem_uIcc hcenter hh hx
    have hxReg := hregular hxSlab
    exact LeanSuffixAnalytic.hasDerivAt_typeThreeArea
      hlambda hxReg.1 hxReg.2
  · exact hbase
  · intro x hx
    exact hslope x (realContains_of_mem_uIcc hcenter hh hx)
  · exact hdisplacement

/-- Box-independent centered type-(iii) perimeter enclosure. -/
theorem typeThreePerimeter_centered_enclosure
    (lambdaInterval hInterval : QInterval) (center : ℚ)
    {lam h : ℝ}
    (_hlam : lambdaInterval.RealContains lam)
    (hh : hInterval.RealContains h)
    (hcenter : hInterval.RealContains (center : ℝ))
    (hlambda : 1 < lam)
    (hregular : ∀ {x : ℝ}, hInterval.RealContains x → x ∈ Ioo (0 : ℝ) 1)
    (base slope displacement : QInterval)
    (hbase : base.RealContains (LeanSuffixAnalytic.typeThreePerimeter lam (center : ℝ)))
    (hslope : ∀ x, hInterval.RealContains x →
      slope.RealContains (LeanSuffixAnalytic.typeThreeFold lam x / x ^ 2))
    (hdisplacement : displacement.RealContains (h - (center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam h) := by
  apply ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (LeanSuffixAnalytic.typeThreePerimeter lam)
    (fun x => LeanSuffixAnalytic.typeThreeFold lam x / x ^ 2)
  · intro x hx
    have hxSlab := realContains_of_mem_uIcc hcenter hh hx
    have hxReg := hregular hxSlab
    exact LeanSuffixAnalytic.hasDerivAt_typeThreePerimeter
      hlambda hxReg.1 hxReg.2
  · exact hbase
  · intro x hx
    exact hslope x (realContains_of_mem_uIcc hcenter hh hx)
  · exact hdisplacement

/-- Common half-pi enclosure. -/
def halfPiBox : QInterval :=
  ScalarSuffixCertificate.piInterval.nsmul (1 / 2) (by norm_num)

@[simp] theorem halfPiBox_lo : halfPiBox.lo = 392699 / 250000 := by
  norm_num [halfPiBox, ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.nsmul]

/-- The common rational half-pi box encloses the exact principal-branch
endpoint. -/
theorem halfPiBox_sound : halfPiBox.RealContains (π / 2) := by
  unfold halfPiBox
  convert ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (1 / 2 : ℚ)) (by norm_num)
    ScalarSuffixCertificate.piInterval_sound using 1 <;> norm_num <;> ring

/-- Exact rational branch check for inverse-sine certificates.  Unlike the old
`3 / 2` cutoff, this accepts every interval below the certified lower endpoint
of the common half-pi box. -/
theorem principalAsinBranch_of_nonneg_of_hi_le_halfPiBox
    (a : QInterval) (h : 0 ≤ a.lo ∧ a.hi ≤ halfPiBox.lo) :
    (a.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (a.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2) := by
  have hlo : (0 : ℝ) ≤ a.lo := by exact_mod_cast h.1
  have hord : (a.lo : ℝ) ≤ a.hi := by exact_mod_cast a.ordered
  have hhi : (a.hi : ℝ) ≤ π / 2 :=
    (show (a.hi : ℝ) ≤ (halfPiBox.lo : ℝ) by exact_mod_cast h.2) |>.trans
      halfPiBox_sound.1
  exact ⟨⟨by linarith [Real.pi_pos], hord.trans hhi⟩,
    ⟨by linarith [Real.pi_pos], hhi⟩⟩

/-- Exact atom production from rational square and degree-27 Taylor bounds. -/
theorem typeThree_atoms_of_exact_bounds
    (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hlambdaLoPos : 0 < lambdaInterval.lo)
    (hlambdaOne : 1 < lam)
    (hqNonneg : 0 ≤ ((hI.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)).lo)
    (hqLeOne : ((hI.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1)
    (huNonneg : 0 ≤ uI.lo)
    (huLower : uI.lo ^ 2 ≤ 1 - ((hI.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)).hi ^ 2)
    (huUpper : 1 - ((hI.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ uI.hi ^ 2)
    (hdNonneg : 0 ≤ dI.lo)
    (hdLower : dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2)
    (hdUpper : lambdaInterval.hi ^ 2 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ dI.hi ^ 2)
    (hasinQBranch : 0 ≤ asinQI.lo ∧ asinQI.hi ≤ halfPiBox.lo)
    (hasinQLower : (ScalarSuffixCertificate.sinTaylor27Interval asinQI.lo).hi ≤
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo)
    (hasinQUpper : ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ≤
      (ScalarSuffixCertificate.sinTaylor27Interval asinQI.hi).lo)
    (hasinRatioBranch : 0 ≤ asinRatioI.lo ∧ asinRatioI.hi ≤ halfPiBox.lo)
    (hasinRatioLower :
      (ScalarSuffixCertificate.sinTaylor27Interval asinRatioI.lo).hi ≤
      (ScalarSuffixCertificate.QInterval.divPos
        ((hI.nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1))
        lambdaInterval hlambdaLoPos).lo)
    (hasinRatioUpper :
      (ScalarSuffixCertificate.QInterval.divPos
        ((hI.nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1))
        lambdaInterval hlambdaLoPos).hi ≤
      (ScalarSuffixCertificate.sinTaylor27Interval asinRatioI.hi).lo) :
    uI.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRatioI.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
  let qI : QInterval := (hI.nsmul 2 (by norm_num)).sub
    (LeanSuffixReflective.QInterval.point 1)
  have hq : qI.RealContains (LeanSuffixAnalytic.typeThreeShape h) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_nsmul (by norm_num) hh)
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
  have hqNonnegR : (0 : ℝ) ≤ qI.lo := by exact_mod_cast hqNonneg
  have hqLeOneR : (qI.hi : ℝ) ≤ 1 := by exact_mod_cast hqLeOne
  have hu : uI.RealContains
      (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt huNonneg
    · have huLowerR : ((uI.lo : ℚ) : ℝ) ^ 2 ≤
          1 - ((qI.hi : ℚ) : ℝ) ^ 2 := by exact_mod_cast huLower
      have hqhiNonneg : (0 : ℝ) ≤ qI.hi :=
        hqNonnegR.trans (by exact_mod_cast qI.ordered)
      have hsq : LeanSuffixAnalytic.typeThreeShape h ^ 2 ≤
          (qI.hi : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.2)
          (add_nonneg (hqNonnegR.trans hq.1) hqhiNonneg)]
      linarith
    · have huUpperR : 1 - ((qI.lo : ℚ) : ℝ) ^ 2 ≤
          ((uI.hi : ℚ) : ℝ) ^ 2 := by exact_mod_cast huUpper
      have hsq : (qI.lo : ℝ) ^ 2 ≤
          LeanSuffixAnalytic.typeThreeShape h ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.1)
          (add_nonneg hqNonnegR (hqNonnegR.trans hq.1))]
      linarith
  have hd : dI.RealContains
      (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt hdNonneg
    · have hdLowerR : ((dI.lo : ℚ) : ℝ) ^ 2 ≤
          (lambdaInterval.lo : ℝ) ^ 2 - (qI.hi : ℝ) ^ 2 := by
        exact_mod_cast hdLower
      have hlamLoNonneg : (0 : ℝ) ≤ lambdaInterval.lo := by
        exact_mod_cast hlambdaLoPos.le
      have hlamSq : (lambdaInterval.lo : ℝ) ^ 2 ≤ lam ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam.1)
          (add_nonneg hlamLoNonneg (hlamLoNonneg.trans hlam.1))]
      have hqhiNonneg : (0 : ℝ) ≤ qI.hi :=
        hqNonnegR.trans (by exact_mod_cast qI.ordered)
      have hqSq : LeanSuffixAnalytic.typeThreeShape h ^ 2 ≤
          (qI.hi : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.2)
          (add_nonneg (hqNonnegR.trans hq.1) hqhiNonneg)]
      linarith
    · have hdUpperR : (lambdaInterval.hi : ℝ) ^ 2 -
          (qI.lo : ℝ) ^ 2 ≤ ((dI.hi : ℚ) : ℝ) ^ 2 := by
        exact_mod_cast hdUpper
      have hlamLoNonneg : (0 : ℝ) ≤ lambdaInterval.lo := by
        exact_mod_cast hlambdaLoPos.le
      have hlamNonneg : (0 : ℝ) ≤ lam := hlamLoNonneg.trans hlam.1
      have hlamHiNonneg : (0 : ℝ) ≤ lambdaInterval.hi := by
        exact_mod_cast hlambdaLoPos.le.trans lambdaInterval.ordered
      have hlamSq : lam ^ 2 ≤ (lambdaInterval.hi : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam.2)
          (add_nonneg hlamNonneg hlamHiNonneg)]
      have hqSq : (qI.lo : ℝ) ^ 2 ≤
          LeanSuffixAnalytic.typeThreeShape h ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.1)
          (add_nonneg hqNonnegR (hqNonnegR.trans hq.1))]
      linarith
  have hasinQ : asinQI.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape h)) := by
    apply QInterval.realContains_arcsin_of_taylor_interval asinQI qI _ hq
    · exact ⟨by linarith [hqNonnegR, hq.1], by linarith [hqLeOneR, hq.2]⟩
    · exact principalAsinBranch_of_nonneg_of_hi_le_halfPiBox asinQI hasinQBranch
    · simpa [qI] using hasinQLower
    · simpa [qI] using hasinQUpper
  have hratio : (ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval
      hlambdaLoPos).RealContains (LeanSuffixAnalytic.typeThreeShape h / lam) :=
    ScalarSuffixCertificate.QInterval.realContains_divPos hlambdaLoPos hq hlam
  have hasinRatio : asinRatioI.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
    apply QInterval.realContains_arcsin_of_taylor_interval asinRatioI
      (ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval hlambdaLoPos) _ hratio
    · have hlamPos : 0 < lam := lt_trans (by norm_num) hlambdaOne
      have hq0 : 0 ≤ LeanSuffixAnalytic.typeThreeShape h := hqNonnegR.trans hq.1
      have hq1 : LeanSuffixAnalytic.typeThreeShape h ≤ 1 := hq.2.trans hqLeOneR
      exact ⟨(show (-1 : ℝ) ≤ 0 by norm_num).trans (div_nonneg hq0 hlamPos.le),
        (div_le_one hlamPos).2 (hq1.trans hlambdaOne.le)⟩
    · exact principalAsinBranch_of_nonneg_of_hi_le_halfPiBox
        asinRatioI hasinRatioBranch
    · simpa [qI] using hasinRatioLower
    · simpa [qI] using hasinRatioUpper
  exact ⟨hu, hd, hasinQ, hasinRatio⟩

/-- Reparametrization used to reuse the type-(iii) atom checker for type-(iv)
atoms: `typeThreeShape ((h + 1) / 2) = h`. -/
def typeFourShiftedInterval (hI : QInterval) : QInterval :=
  (hI.add (LeanSuffixReflective.QInterval.point 1)).nsmul
    (1 / 2) (by norm_num)

/-- Exact type-(iv) atom production from rational square and degree-27 Taylor
bounds.  This is the box-independent counterpart of
`typeThree_atoms_of_exact_bounds`; concrete generated cells discharge the
single rational conjunction with `norm_num`. -/
theorem typeFour_atoms_of_exact_bounds
    (lambdaInterval hI uI dI asinHI asinRI : QInterval) {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : hI.RealContains h)
    (hlambdaLoPos : 0 < lambdaInterval.lo)
    (hlambdaOne : 1 < lam)
    (hexact :
      0 ≤ (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ∧
      (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1 ∧
      0 ≤ uI.lo ∧
      uI.lo ^ 2 ≤ 1 - (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      1 - (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ uI.hi ^ 2 ∧
      0 ≤ dI.lo ∧
      dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 -
        (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      lambdaInterval.hi ^ 2 -
        (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ dI.hi ^ 2 ∧
      (0 ≤ asinHI.lo ∧ asinHI.hi ≤ halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinHI.lo).hi ≤
        (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).lo ∧
      (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinHI.hi).lo ∧
      (0 ≤ asinRI.lo ∧ asinRI.hi ≤ halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinRI.lo).hi ≤
        (ScalarSuffixCertificate.QInterval.divPos
          (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
            (LeanSuffixReflective.QInterval.point 1)) lambdaInterval
          hlambdaLoPos).lo ∧
      (ScalarSuffixCertificate.QInterval.divPos
          (((typeFourShiftedInterval hI).nsmul 2 (by norm_num)).sub
            (LeanSuffixReflective.QInterval.point 1)) lambdaInterval
          hlambdaLoPos).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinRI.hi).lo) :
    uI.RealContains (sqrt (1 - h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - h ^ 2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRI.RealContains (arcsin (h / lam)) := by
  let shifted : QInterval :=
    (hI.add (LeanSuffixReflective.QInterval.point 1)).nsmul
      (1 / 2) (by norm_num)
  have ht : shifted.RealContains ((h + 1) / 2) := by
    have ha := LeanSuffixReflective.QInterval.realContains_add hh
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
    convert ScalarSuffixCertificate.QInterval.realContains_nsmul
      (q := (1 / 2 : ℚ)) (by norm_num) ha using 1 <;> ring
  rcases hexact with
    ⟨hq0, hq1, hu0, hul, huh, hd0, hdl, hdh, haB, hal, hah, hrB, hrl, hrh⟩
  have ha := typeThree_atoms_of_exact_bounds
    lambdaInterval shifted uI dI asinHI asinRI hlam ht
    hlambdaLoPos hlambdaOne hq0 hq1 hu0 hul huh hd0 hdl hdh
    haB hal hah hrB hrl hrh
  have hs : LeanSuffixAnalytic.typeThreeShape ((h + 1) / 2) = h := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  simpa [hs] using ha


def typeThreeQBox (hI : QInterval) : QInterval :=
  (hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)

def typeThreeAngleBox (lambdaInterval asinQI asinRatioI : QInterval) : QInterval :=
  (lambdaInterval.mul (halfPiBox.sub asinRatioI)).add asinQI

def typeThreeDeltaBox (lambdaInterval uI dI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) : QInterval :=
  (dI.divPos lambdaInterval hlambda).sub uI

def typeThreeAreaBox (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) (hhSq : 0 < (hI.mul hI).lo) : QInterval :=
  ScalarSuffixCertificate.QInterval.divPos
    ((typeThreeAngleBox lambdaInterval asinQI asinRatioI).add halfPiBox |>.add
      (ScalarSuffixCertificate.QInterval.mul
        ((typeThreeQBox hI).add (LeanSuffixReflective.QInterval.point 2))
        (typeThreeDeltaBox lambdaInterval uI dI hlambda))) (hI.mul hI) hhSq

def typeThreePerimeterBox (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) (hh : 0 < hI.lo) : QInterval :=
  (ScalarSuffixCertificate.QInterval.divPos
    ((typeThreeAngleBox lambdaInterval asinQI asinRatioI).add halfPiBox |>.add
      (typeThreeDeltaBox lambdaInterval uI dI hlambda)) hI hh).nsmul 2 (by norm_num)

/-- Exact interval expression for the type-(iii) fold numerator. -/
def typeThreeFoldBox (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) (hu : 0 < uI.lo)
    (hlambdaD : 0 < (lambdaInterval.mul dI).lo) : QInterval :=
  let qI := typeThreeQBox hI
  let angleI := typeThreeAngleBox lambdaInterval asinQI asinRatioI
  let deltaI := typeThreeDeltaBox lambdaInterval uI dI hlambda
  let first := ScalarSuffixCertificate.QInterval.divPos
    ((LeanSuffixReflective.QInterval.point 1).add qI) uI hu
  let second := ScalarSuffixCertificate.QInterval.divPos
    ((lambdaInterval.mul lambdaInterval).add qI)
    (lambdaInterval.mul dI) hlambdaD
  ((hI.mul (first.sub second)).nsmul 4 (by norm_num)).sub
    (((angleI.add halfPiBox).add deltaI).nsmul 2 (by norm_num))

/-- Formula enclosure assembled from type-(iii) atoms for the fold numerator. -/
theorem typeThree_fold_atom_enclosure
    (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    {lam h : ℝ} (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hatoms : uI.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRatioI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)))
    (hlambda : 0 < lambdaInterval.lo) (huPos : 0 < uI.lo)
    (hlambdaD : 0 < (lambdaInterval.mul dI).lo) :
    (typeThreeFoldBox lambdaInterval hI uI dI asinQI asinRatioI
      hlambda huPos hlambdaD).RealContains
      (LeanSuffixAnalytic.typeThreeFold lam h) := by
  rcases hatoms with ⟨hu, hd, hasinQ, hasinRatio⟩
  have hq : (typeThreeQBox hI).RealContains
      (LeanSuffixAnalytic.typeThreeShape h) := by
    unfold typeThreeQBox LeanSuffixAnalytic.typeThreeShape
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_nsmul (by norm_num) hh)
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
  have hhalfPi : halfPiBox.RealContains (π / 2) := halfPiBox_sound
  have hacos : (halfPiBox.sub asinRatioI).RealContains
      (arccos (LeanSuffixAnalytic.typeThreeShape h / lam)) :=
    ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hangle : (typeThreeAngleBox lambdaInterval asinQI asinRatioI).RealContains
      (LeanSuffixAnalytic.typeThreeAngle lam h) := by
    unfold typeThreeAngleBox LeanSuffixAnalytic.typeThreeAngle
    exact LeanSuffixReflective.QInterval.realContains_add
      (ScalarSuffixCertificate.QInterval.realContains_mul hlam hacos) hasinQ
  have hdelta : (typeThreeDeltaBox lambdaInterval uI dI hlambda).RealContains
      (LeanSuffixAnalytic.typeThreeDelta lam h) := by
    unfold typeThreeDeltaBox LeanSuffixAnalytic.typeThreeDelta
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_divPos hlambda hd hlam) hu
  have hnumOne := LeanSuffixReflective.QInterval.realContains_add
    (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num)) hq
  have hdivOne := ScalarSuffixCertificate.QInterval.realContains_divPos
    huPos hnumOne hu
  have hlamSq := ScalarSuffixCertificate.QInterval.realContains_mul hlam hlam
  have hnumTwo := LeanSuffixReflective.QInterval.realContains_add hlamSq hq
  have hlamD := ScalarSuffixCertificate.QInterval.realContains_mul hlam hd
  have hdivTwo := ScalarSuffixCertificate.QInterval.realContains_divPos
    hlambdaD hnumTwo hlamD
  have hfirst := ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (4 : ℚ)) (by norm_num)
    (ScalarSuffixCertificate.QInterval.realContains_mul hh
      (LeanSuffixReflective.QInterval.realContains_sub hdivOne hdivTwo))
  have hsecond := ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (2 : ℚ)) (by norm_num)
    (LeanSuffixReflective.QInterval.realContains_add
      (LeanSuffixReflective.QInterval.realContains_add hangle hhalfPi) hdelta)
  convert LeanSuffixReflective.QInterval.realContains_sub hfirst hsecond using 1 <;>
    simp only [typeThreeFoldBox, LeanSuffixAnalytic.typeThreeFold] <;> ring

/-- Formula enclosure assembled from type-(iii) atoms. -/
theorem typeThree_area_perimeter_atom_enclosure
    (lambdaInterval hI uI dI asinQI asinRatioI : QInterval)
    {lam h : ℝ} (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hatoms : uI.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRatioI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)))
    (hlambda : 0 < lambdaInterval.lo) (hhPos : 0 < hI.lo)
    (hhSq : 0 < (hI.mul hI).lo) :
    (typeThreeAreaBox lambdaInterval hI uI dI asinQI asinRatioI hlambda hhSq).RealContains
        (LeanSuffixAnalytic.typeThreeArea lam h) ∧
      (typeThreePerimeterBox lambdaInterval hI uI dI asinQI asinRatioI hlambda hhPos).RealContains
        (LeanSuffixAnalytic.typeThreePerimeter lam h) := by
  rcases hatoms with ⟨hu, hd, hasinQ, hasinRatio⟩
  have hhalfPi : halfPiBox.RealContains (π / 2) := halfPiBox_sound
  have hq : (typeThreeQBox hI).RealContains (LeanSuffixAnalytic.typeThreeShape h) := by
    unfold typeThreeQBox LeanSuffixAnalytic.typeThreeShape
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_nsmul (by norm_num) hh)
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
  have hacos : (halfPiBox.sub asinRatioI).RealContains
      (arccos (LeanSuffixAnalytic.typeThreeShape h / lam)) :=
    ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hangle : (typeThreeAngleBox lambdaInterval asinQI asinRatioI).RealContains
      (LeanSuffixAnalytic.typeThreeAngle lam h) := by
    unfold typeThreeAngleBox LeanSuffixAnalytic.typeThreeAngle
    exact LeanSuffixReflective.QInterval.realContains_add
      (ScalarSuffixCertificate.QInterval.realContains_mul hlam hacos) hasinQ
  have hdelta : (typeThreeDeltaBox lambdaInterval uI dI hlambda).RealContains
      (LeanSuffixAnalytic.typeThreeDelta lam h) := by
    unfold typeThreeDeltaBox LeanSuffixAnalytic.typeThreeDelta
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_divPos hlambda hd hlam) hu
  have hqPlusTwo := LeanSuffixReflective.QInterval.realContains_add hq
    (LeanSuffixReflective.QInterval.realContains_point 2 (2 : ℝ) |>.2 (by norm_num))
  have hnumArea := LeanSuffixReflective.QInterval.realContains_add
    (LeanSuffixReflective.QInterval.realContains_add hangle hhalfPi)
    (ScalarSuffixCertificate.QInterval.realContains_mul hqPlusTwo hdelta)
  have hhSquare := ScalarSuffixCertificate.QInterval.realContains_mul hh hh
  have harea := ScalarSuffixCertificate.QInterval.realContains_divPos hhSq hnumArea hhSquare
  have hnumPerimeter := LeanSuffixReflective.QInterval.realContains_add
    (LeanSuffixReflective.QInterval.realContains_add hangle hhalfPi) hdelta
  have hperimeterDiv := ScalarSuffixCertificate.QInterval.realContains_divPos
    hhPos hnumPerimeter hh
  constructor
  · convert harea using 1 <;>
      simp only [typeThreeAreaBox, LeanSuffixAnalytic.typeThreeArea] <;> ring
  · convert ScalarSuffixCertificate.QInterval.realContains_nsmul
        (q := (2 : ℚ)) (by norm_num) hperimeterDiv using 1 <;>
      simp only [typeThreePerimeterBox, LeanSuffixAnalytic.typeThreePerimeter] <;> ring

def typeFourAngleBox (lambdaInterval asinHI asinRatioI : QInterval) : QInterval :=
  (lambdaInterval.mul (halfPiBox.sub asinRatioI)).add asinHI

def typeFourDeltaBox (lambdaInterval uI dI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) : QInterval :=
  (dI.divPos lambdaInterval hlambda).sub uI

def typeFourAreaBox (lambdaInterval hI uI dI asinHI asinRatioI : QInterval)
    (hlambda : 0 < lambdaInterval.lo) (hhSq : 0 < (hI.mul hI).lo) : QInterval :=
  ScalarSuffixCertificate.QInterval.divPos
    (LeanSuffixReflective.QInterval.nsmul 2 (by norm_num)
      ((typeFourAngleBox lambdaInterval asinHI asinRatioI).add
        (hI.mul (typeFourDeltaBox lambdaInterval uI dI hlambda))))
    (hI.mul hI) hhSq

def typeFourPerimeterBox (lambdaInterval hI asinHI asinRatioI : QInterval)
    (hh : 0 < hI.lo) : QInterval :=
  (ScalarSuffixCertificate.QInterval.divPos
    ((typeFourAngleBox lambdaInterval asinHI asinRatioI).nsmul 4 (by norm_num)) hI hh)

def typeFourFoldBox (lambdaInterval hI uI dI asinHI asinRatioI : QInterval)
    (_hlambda : 0 < lambdaInterval.lo) (hu : 0 < uI.lo) (hd : 0 < dI.lo) : QInterval :=
  ((hI.mul ((uI.recipPos hu).sub (lambdaInterval.divPos dI hd))).sub
    (typeFourAngleBox lambdaInterval asinHI asinRatioI)).nsmul 4 (by norm_num)

/-- Formula enclosures assembled from type-(iv) atoms. -/
theorem typeFour_atom_enclosures
    (lambdaInterval hI uI dI asinHI asinRatioI : QInterval)
    {lam h : ℝ} (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hatoms : uI.RealContains (sqrt (1 - h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - h ^ 2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRatioI.RealContains (arcsin (h / lam)))
    (hlambda : 0 < lambdaInterval.lo) (hhPos : 0 < hI.lo)
    (hhSq : 0 < (hI.mul hI).lo) (huPos : 0 < uI.lo) (hdPos : 0 < dI.lo) :
    (typeFourAreaBox lambdaInterval hI uI dI asinHI asinRatioI hlambda hhSq).RealContains
        (LeanSuffixAnalytic.typeFourArea lam h) ∧
      (typeFourPerimeterBox lambdaInterval hI asinHI asinRatioI hhPos).RealContains
        (LeanSuffixAnalytic.typeFourPerimeter lam h) ∧
      (typeFourFoldBox lambdaInterval hI uI dI asinHI asinRatioI
        hlambda huPos hdPos).RealContains (LeanSuffixAnalytic.typeFourFold lam h) := by
  rcases hatoms with ⟨hu, hd, hasinH, hasinRatio⟩
  have hhalfPi : halfPiBox.RealContains (π / 2) := halfPiBox_sound
  have hacos : (halfPiBox.sub asinRatioI).RealContains (arccos (h / lam)) :=
    ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hangle : (typeFourAngleBox lambdaInterval asinHI asinRatioI).RealContains
      (LeanSuffixAnalytic.typeFourAngle lam h) := by
    unfold typeFourAngleBox LeanSuffixAnalytic.typeFourAngle
    exact LeanSuffixReflective.QInterval.realContains_add
      (ScalarSuffixCertificate.QInterval.realContains_mul hlam hacos) hasinH
  have hdelta : (typeFourDeltaBox lambdaInterval uI dI hlambda).RealContains
      (LeanSuffixAnalytic.typeFourDelta lam h) := by
    unfold typeFourDeltaBox LeanSuffixAnalytic.typeFourDelta
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_divPos hlambda hd hlam) hu
  have hareaNum := ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (2 : ℚ)) (by norm_num)
    (LeanSuffixReflective.QInterval.realContains_add hangle
      (ScalarSuffixCertificate.QInterval.realContains_mul hh hdelta))
  have hhSquare := ScalarSuffixCertificate.QInterval.realContains_mul hh hh
  have harea := ScalarSuffixCertificate.QInterval.realContains_divPos
    hhSq hareaNum hhSquare
  have hperimeterNum := ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (4 : ℚ)) (by norm_num) hangle
  have hperimeter := ScalarSuffixCertificate.QInterval.realContains_divPos
    hhPos hperimeterNum hh
  have hinvU := ScalarSuffixCertificate.QInterval.realContains_recipPos huPos hu
  have hlamDivD := ScalarSuffixCertificate.QInterval.realContains_divPos hdPos hlam hd
  have hfold := ScalarSuffixCertificate.QInterval.realContains_nsmul
    (q := (4 : ℚ)) (by norm_num)
    (LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_mul hh
        (LeanSuffixReflective.QInterval.realContains_sub hinvU hlamDivD)) hangle)
  refine ⟨?_, ?_, ?_⟩
  · convert harea using 1 <;>
      simp only [typeFourAreaBox, LeanSuffixAnalytic.typeFourArea] <;> ring
  · convert hperimeter using 1 <;>
      simp only [typeFourPerimeterBox, LeanSuffixAnalytic.typeFourPerimeter] <;> ring
  · convert hfold using 1 <;>
      simp only [typeFourFoldBox, LeanSuffixAnalytic.typeFourFold] <;> ring

end CompactCellCertificate
