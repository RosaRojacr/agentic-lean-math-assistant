/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import SameCurvatureArea
import CMVTypeThreeSourceExclusion

/-!
# Singularity-free type-(iii) endpoint chart for CMV Figure 5

The actual type-(iii) area is identified with this angular extension only on
`0 ≤ u < π`.  In particular, no negative-angle source identity is asserted:
the square root of `sin u ^ 2` is `|sin u|`, not `sin u`, off that branch.
-/

open Set
open Real
open Filter
open scoped Topology

noncomputable section

namespace CMVFigureFive

/-- Principal closed-Snell angle at the type-(iii) endpoint. -/
def endpointAngle (lam : ℝ) : ℝ := arccos (1 / lam)

/-- Strict exterior support gap `lambda * theta - sin theta`. -/
def endpointGap (lam : ℝ) : ℝ :=
  lam * endpointAngle lam - sin (endpointAngle lam)

/-- Regular endpoint chart `h = (1 + cos u) / 2`. -/
def angularHeight (u : ℝ) : ℝ := (1 + cos u) / 2

/-- Pole-free angular angle numerator. -/
def angularAngle (lam u : ℝ) : ℝ :=
  lam * arccos (cos u / lam) + π - u

/-- Pole-free angular radial displacement. -/
def angularDelta (lam u : ℝ) : ℝ :=
  sqrt (lam ^ 2 - cos u ^ 2) / lam - sin u

/-- Smooth angular extension of the actual type-(iii) area at `u = 0`. -/
def angularArea (lam u : ℝ) : ℝ :=
  (angularAngle lam u + (cos u + 2) * angularDelta lam u) /
    angularHeight u ^ 2

/-- The endpoint angle lies strictly in the first quadrant. -/
theorem endpointAngle_mem {lam : ℝ} (hlam : 1 < lam) :
    endpointAngle lam ∈ Ioo 0 (π / 2) := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hratio_pos : 0 < 1 / lam := one_div_pos.mpr hlam_pos
  have hratio_lt : 1 / lam < 1 := (div_lt_one hlam_pos).2 hlam
  exact ⟨Real.arccos_pos.mpr hratio_lt,
    (Real.arccos_lt_pi_div_two).2 hratio_pos⟩

/-- The endpoint support gap is strictly positive. -/
theorem endpointGap_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < endpointGap lam := by
  have htheta := (endpointAngle_mem hlam).1
  have hsin_lt : sin (endpointAngle lam) < endpointAngle lam :=
    Real.sin_lt htheta
  have hmul : endpointAngle lam < lam * endpointAngle lam := by
    nlinarith
  exact sub_pos.mpr (hsin_lt.trans hmul)

/-- On the nonnegative angular branch, the pole-free formula is the actual
source type-(iii) area. -/
theorem angularArea_eq_typeThreeArea {lam u : ℝ}
    (hu : 0 ≤ u) (hupi : u < π) :
    angularArea lam u =
      LeanSuffixAnalytic.typeThreeArea lam (angularHeight u) := by
  have hucos : arccos (cos u) = u :=
    Real.arccos_cos hu hupi.le
  have huSin : 0 ≤ sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu hupi.le
  have hsqrt : sqrt (1 - cos u ^ 2) = sin u := by
    rw [show 1 - cos u ^ 2 = sin u ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq u], Real.sqrt_sq_eq_abs,
      abs_of_nonneg huSin]
  unfold angularArea angularAngle angularDelta angularHeight
  unfold LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  rw [show 2 * ((1 + cos u) / 2) - 1 = cos u by ring,
    Real.arcsin_eq_pi_div_two_sub_arccos, hucos, hsqrt]
  ring

/-- The regular endpoint chart has zero first derivative at the cusp. -/
theorem angularHeight_hasDerivAt_zero :
    HasDerivAt angularHeight 0 0 := by
  simpa [angularHeight] using!
    (((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
      (Real.hasDerivAt_cos 0)).div_const (2 : ℝ))

/-- The angular angle term has derivative `-1` at the cusp. -/
theorem angularAngle_hasDerivAt_zero {lam : ℝ} (hlam : 1 < lam) :
    HasDerivAt (angularAngle lam) (-1) 0 := by
  change HasDerivAt
    (fun u : ℝ => lam * arccos (cos u / lam) + π - u) (-1) 0
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hneg : (1 / lam : ℝ) ≠ -1 := by
    exact ne_of_gt (lt_trans (by norm_num) (one_div_pos.mpr hlam_pos))
  have hpos : (1 / lam : ℝ) ≠ 1 := by
    exact ne_of_lt ((div_lt_one hlam_pos).2 hlam)
  have hinnerRaw := (Real.hasDerivAt_cos 0).div_const lam
  have hnegAt : cos 0 / lam ≠ (-1 : ℝ) := by simpa using hneg
  have hposAt : cos 0 / lam ≠ (1 : ℝ) := by simpa using hpos
  have harccosRaw :=
    (Real.hasDerivAt_arccos hnegAt hposAt).comp 0 hinnerRaw
  have harccos : HasDerivAt (fun u : ℝ => arccos (cos u / lam)) 0 0 := by
    simpa [Function.comp_def] using! harccosRaw
  have hraw := (harccos.const_mul lam).add_const π |>.sub (hasDerivAt_id 0)
  simpa only [Pi.sub_apply, id_eq] using! hraw.congr_deriv (by ring)

/-- The angular radial term has derivative `-1` at the cusp. -/
theorem angularDelta_hasDerivAt_zero {lam : ℝ} (hlam : 1 < lam) :
    HasDerivAt (angularDelta lam) (-1) 0 := by
  change HasDerivAt
    (fun u : ℝ => sqrt (lam ^ 2 - cos u ^ 2) / lam - sin u) (-1) 0
  have hrad : lam ^ 2 - 1 ≠ 0 := by nlinarith
  have hcos : HasDerivAt (fun u : ℝ => cos u ^ 2) 0 0 := by
    simpa using! (Real.hasDerivAt_cos 0).pow 2
  have hinside : HasDerivAt (fun u : ℝ => lam ^ 2 - cos u ^ 2) 0 0 := by
    simpa only [Pi.pow_apply, neg_zero] using hcos.const_sub (lam ^ 2)
  have hsqrt := hinside.sqrt (by simpa using hrad)
  have hraw := (hsqrt.div_const lam).sub (Real.hasDerivAt_sin 0)
  simpa only [Pi.sub_apply] using! hraw.congr_deriv (by norm_num)

/-- The complete pole-free angular area has exact derivative `-4` at zero. -/
theorem angularArea_hasDerivAt_zero {lam : ℝ} (hlam : 1 < lam) :
    HasDerivAt (angularArea lam) (-4) 0 := by
  change HasDerivAt
    (fun u : ℝ =>
      (angularAngle lam u + (cos u + 2) * angularDelta lam u) /
        angularHeight u ^ 2) (-4) 0
  have hangle := angularAngle_hasDerivAt_zero hlam
  have hdelta := angularDelta_hasDerivAt_zero hlam
  have hcosPlus : HasDerivAt (fun u : ℝ => cos u + 2) 0 0 := by
    simpa using! (Real.hasDerivAt_cos 0).add_const 2
  have hnum := hangle.add (hcosPlus.mul hdelta)
  have hden := angularHeight_hasDerivAt_zero.pow 2
  have hden_ne : angularHeight 0 ^ 2 ≠ 0 := by norm_num [angularHeight]
  have hraw := hnum.div hden hden_ne
  simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] using!
    hraw.congr_deriv (by
      norm_num [angularAngle, angularDelta, angularHeight])

/-- The endpoint sine is the nonsingular scaled radial square root. -/
theorem endpointSine_eq_scaledRadical {lam : ℝ} (hlam : 1 < lam) :
    sin (endpointAngle lam) = sqrt (lam ^ 2 - 1) / lam := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hrad : 0 ≤ lam ^ 2 - 1 := by nlinarith
  rw [endpointAngle, Real.sin_arccos]
  calc
    sqrt (1 - (1 / lam) ^ 2) =
        sqrt ((lam ^ 2 - 1) / lam ^ 2) := by
      congr 1
      field_simp [hlam_ne]
    _ = sqrt (lam ^ 2 - 1) / sqrt (lam ^ 2) := by
      rw [Real.sqrt_div hrad]
    _ = sqrt (lam ^ 2 - 1) / lam := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos]

/-- The smooth chart has the actual closed endpoint area at zero. -/
theorem angularArea_zero_eq_typeThreeArea_one (lam : ℝ) :
    angularArea lam 0 = LeanSuffixAnalytic.typeThreeArea lam 1 := by
  simpa [angularHeight] using
    (angularArea_eq_typeThreeArea (lam := lam) (u := 0)
      (by norm_num) Real.pi_pos)

/-- Exact type-(iii) endpoint support intercept. -/
theorem typeThree_endpoint_support {lam : ℝ} (hlam : 1 < lam) :
    LeanSuffixAnalytic.typeThreePerimeter lam 1 -
        LeanSuffixAnalytic.typeThreeArea lam 1 =
      π + endpointGap lam := by
  have hsine := endpointSine_eq_scaledRadical hlam
  unfold LeanSuffixAnalytic.typeThreePerimeter
    LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  norm_num [Real.arcsin_one]
  rw [← hsine]
  unfold endpointGap endpointAngle
  ring_nf

/-- The negative angular derivative produces an actual regular height whose
area lies strictly below the closed endpoint area.  Only positive angles are
identified with the source formula. -/
theorem exists_regular_height_area_lt_endpoint {lam : ℝ} (hlam : 1 < lam) :
    ∃ h ∈ Ioo (0 : ℝ) 1,
      LeanSuffixAnalytic.typeThreeArea lam h <
        LeanSuffixAnalytic.typeThreeArea lam 1 := by
  have hslope_tendsto :
      Tendsto (slope (angularArea lam) 0) (𝓝[>] (0 : ℝ)) (𝓝 (-4 : ℝ)) :=
    (angularArea_hasDerivAt_zero hlam).tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE 0)
  have hslope : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      slope (angularArea lam) 0 u < 0 :=
    hslope_tendsto.eventually (eventually_lt_nhds (by norm_num))
  have hupper : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < π / 2 :=
    (eventually_lt_nhds Real.pi_div_two_pos).filter_mono inf_le_left
  have hpositive : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u :=
    self_mem_nhdsWithin
  rcases (hslope.and (hupper.and hpositive)).exists with
    ⟨u, huSlope, huUpper, huPos⟩
  have huPi : u < π := huUpper.trans (half_lt_self Real.pi_pos)
  have hcosPos : 0 < cos u :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, huUpper⟩
  have hcosLt : cos u < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Icc 0 π by exact ⟨le_rfl, Real.pi_pos.le⟩)
      (show u ∈ Icc 0 π by exact ⟨huPos.le, huPi.le⟩) huPos
    simpa using hanti
  have hheight : angularHeight u ∈ Ioo (0 : ℝ) 1 := by
    unfold angularHeight
    constructor <;> nlinarith
  have harea :
      angularArea lam u < angularArea lam 0 :=
    (slope_neg_iff_of_le (f := angularArea lam) huPos.le).mp huSlope
  refine ⟨angularHeight u, hheight, ?_⟩
  rw [← angularArea_zero_eq_typeThreeArea_one lam,
    ← angularArea_eq_typeThreeArea huPos.le huPi]
  exact harea

/-- Every target area at or above the closed type-(iii) endpoint is attained
by a regular type-(iii) height strictly below its endpoint support line. -/
theorem exists_regular_typeThree_below_endpoint_support
    {lam V : ℝ} (hlam : 1 < lam)
    (hV : LeanSuffixAnalytic.typeThreeArea lam 1 ≤ V) :
    ∃ r ∈ Ioo (0 : ℝ) 1,
      LeanSuffixAnalytic.typeThreeArea lam r = V ∧
      LeanSuffixAnalytic.typeThreePerimeter lam r <
        V + π + endpointGap lam := by
  rcases exists_regular_height_area_lt_endpoint hlam with
    ⟨anchor, hanchor, hanchorArea⟩
  have hanchorV : LeanSuffixAnalytic.typeThreeArea lam anchor < V :=
    hanchorArea.trans_le hV
  have hlarge :=
    (LeanSuffixAnalytic.typeThreeArea_tendsto_atRight_zero hlam)
      |>.eventually_gt_atTop V
  have hbelow : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < anchor :=
    (eventually_lt_nhds hanchor.1).filter_mono inf_le_left
  have hpositive : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h :=
    self_mem_nhdsWithin
  rcases (hlarge.and (hbelow.and hpositive)).exists with
    ⟨a, haLarge, haAnchor, haPos⟩
  have hcont : ContinuousOn (LeanSuffixAnalytic.typeThreeArea lam)
      (Icc a anchor) := by
    intro x hx
    exact (LeanSuffixAnalytic.hasDerivAt_typeThreeArea hlam
      (haPos.trans_le hx.1) (hx.2.trans_lt hanchor.2)
    ).continuousAt.continuousWithinAt
  have htarget :
      V ∈ Icc (LeanSuffixAnalytic.typeThreeArea lam anchor)
        (LeanSuffixAnalytic.typeThreeArea lam a) :=
    ⟨hanchorV.le, haLarge.le⟩
  rcases intermediate_value_Icc' haAnchor.le hcont htarget with
    ⟨r, hrInterval, hrArea⟩
  have hrPos : 0 < r := haPos.trans_le hrInterval.1
  have hrAnchor : r < anchor := by
    apply lt_of_le_of_ne hrInterval.2
    intro hre
    subst r
    exact (ne_of_lt hanchorV) hrArea
  have hrRegular : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hrPos, hrAnchor.trans hanchor.2⟩
  have hsublevel : ∀ x ∈ Icc r 1,
      LeanSuffixAnalytic.typeThreeArea lam x ≤ V := by
    intro x hx
    have hbound := LeanSuffixAnalytic.typeThreeArea_le_max_endpoints
      (a := r) (b := 1) (x := x) hlam hrPos hx.1 hx.2 le_rfl
    rw [hrArea, max_eq_left hV] at hbound
    exact hbound
  have hsupportMono : MonotoneOn
      (LeanSuffixAnalytic.typeThreeAreaSupport lam V) (Icc r 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => V - LeanSuffixAnalytic.typeThreeArea lam x)
      (convex_Icc r 1)
    · exact LeanSuffixAnalytic.typeThreeAreaSupport_continuousOn_Icc
        hlam hrPos
    · intro x hx
      rw [interior_Icc] at hx
      exact (LeanSuffixAnalytic.typeThreeAreaSupport_hasDerivAt
        hlam (hrPos.trans hx.1) hx.2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact sub_nonneg.mpr (hsublevel x ⟨hx.1.le, hx.2.le⟩)
  have hsupportDeriv :=
    LeanSuffixAnalytic.typeThreeAreaSupport_hasDerivAt
      (V := V) hlam hanchor.1 hanchor.2
  have hsupportSlopeTendsto :
      Tendsto
        (slope (LeanSuffixAnalytic.typeThreeAreaSupport lam V) anchor)
        (𝓝[>] anchor)
        (𝓝 (V - LeanSuffixAnalytic.typeThreeArea lam anchor)) :=
    hsupportDeriv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE anchor)
  have hsupportDerivPos :
      0 < V - LeanSuffixAnalytic.typeThreeArea lam anchor :=
    sub_pos.mpr hanchorV
  have hsupportSlope : ∀ᶠ y in 𝓝[>] anchor,
      0 < slope (LeanSuffixAnalytic.typeThreeAreaSupport lam V) anchor y :=
    hsupportSlopeTendsto.eventually
      (eventually_gt_nhds hsupportDerivPos)
  have hyUpper : ∀ᶠ y in 𝓝[>] anchor, y < 1 :=
    (eventually_lt_nhds hanchor.2).filter_mono inf_le_left
  have hyRight : ∀ᶠ y in 𝓝[>] anchor, anchor < y :=
    self_mem_nhdsWithin
  rcases (hsupportSlope.and (hyUpper.and hyRight)).exists with
    ⟨y, hySlope, hyOne, hanchorY⟩
  have hsupportAnchorY :
      LeanSuffixAnalytic.typeThreeAreaSupport lam V anchor <
        LeanSuffixAnalytic.typeThreeAreaSupport lam V y :=
    (slope_pos_iff_of_le hanchorY.le).mp hySlope
  have hrMem : r ∈ Icc r 1 := ⟨le_rfl, hrRegular.2.le⟩
  have hanchorMem : anchor ∈ Icc r 1 :=
    ⟨hrAnchor.le, hanchor.2.le⟩
  have hyMem : y ∈ Icc r 1 :=
    ⟨(hrAnchor.trans hanchorY).le, hyOne.le⟩
  have honeMem : (1 : ℝ) ∈ Icc r 1 :=
    ⟨hrRegular.2.le, le_rfl⟩
  have hsupportStrict :
      LeanSuffixAnalytic.typeThreeAreaSupport lam V r <
        LeanSuffixAnalytic.typeThreeAreaSupport lam V 1 :=
    lt_of_le_of_lt
      (hsupportMono hrMem hanchorMem hrAnchor.le)
      (lt_of_lt_of_le hsupportAnchorY
        (hsupportMono hyMem honeMem hyOne.le))
  refine ⟨r, hrRegular, hrArea, ?_⟩
  calc
    LeanSuffixAnalytic.typeThreePerimeter lam r =
        LeanSuffixAnalytic.typeThreeAreaSupport lam V r := by
      unfold LeanSuffixAnalytic.typeThreeAreaSupport
      rw [hrArea]
      ring
    _ < LeanSuffixAnalytic.typeThreeAreaSupport lam V 1 := hsupportStrict
    _ = V +
        (LeanSuffixAnalytic.typeThreePerimeter lam 1 -
          LeanSuffixAnalytic.typeThreeArea lam 1) := by
      unfold LeanSuffixAnalytic.typeThreeAreaSupport
      ring
    _ = V + π + endpointGap lam := by
      rw [typeThree_endpoint_support hlam]
      ring

/-- The support-line producer is realized by the existing branch-complete
type-(iii) carrier and its checked smooth recovery. -/
theorem exists_admissible_typeThree_below_endpoint_support
    {lam V : ℝ} (hlam : 1 < lam)
    (hV : LeanSuffixAnalytic.typeThreeArea lam 1 ≤ V) :
    ∃ a : _root_.TypeThreeAssembly lam,
      a.h ∈ Ioo (0 : ℝ) 1 ∧
      (CMVRelaxation.relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier = V ∧
      a.WeightedPerimeter < V + π + endpointGap lam := by
  rcases exists_regular_typeThree_below_endpoint_support hlam hV with
    ⟨r, hr, hrArea, hrPerimeter⟩
  let a : _root_.TypeThreeAssembly lam :=
    { h := r
      density_jump := hlam
      h_pos := hr.1
      h_lt_one := hr.2 }
  refine ⟨a, hr, CMVRelaxation.TypeThreeRecovery.isAdmissible_typeThree a,
    ?_, ?_⟩
  · change a.WeightedArea = V
    rw [a.weightedArea_formula,
      CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea]
    exact hrArea
  · rw [a.weightedPerimeter_formula,
      CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter]
    exact hrPerimeter

end CMVFigureFive
