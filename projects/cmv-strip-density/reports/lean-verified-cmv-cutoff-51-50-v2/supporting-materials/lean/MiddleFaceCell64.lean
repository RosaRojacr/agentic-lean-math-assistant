/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MiddleFaceAssembly

/-!
# Middle-face inventory brick B0064

Kernel-checked projected-face certificate for the exact rational data recorded
in `middle_face_tiling/bricks/B0064.json`.
-/

open Real Set
open scoped BigOperators
noncomputable section
open ScalarSuffixCertificate
open MiddleFaceAssembly.EResidual
namespace MiddleFaceCell64

abbrev Brick := MiddleFaceAssembly.Brick

/-- Exact inventory brick `B0064`, spanning `[102641/100000, 102651/100000]`. -/
def brick : Brick where
  lamLo := 102641 / 100000
  lamHi := 102651 / 100000
  centers := ![493709796384460787 / 2500000000000000000,
    1500845812320836633 / 5000000000000000000,
    568171967621107097 / 1250000000000000000,
    5047329603622433701 / 10000000000000000000]
  slopes := ![334524180651462607 / 200000000000000000,
    4228783750437913453 / 1000000000000000000,
    2501376108049616283 / 500000000000000000,
    3094216132326103829 / 500000000000000000]
  yXiSlope := 16161383 / 25000000
  vRhoSlope := 884517 / 1000000
  radii := ![1 / 100000, 1 / 1000000, 1 / 100000, 1 / 1000000]
  lamOrdered := by norm_num
  radiiPos := by intro j; fin_cases j <;> norm_num

private abbrev eReduced := MiddleFaceAssembly.EResidual.reduced brick
private abbrev eReducedDerivT :=
  MiddleFaceAssembly.EResidual.derivT brick
private abbrev eReducedDerivXi :=
  MiddleFaceAssembly.EResidual.derivXi brick
private abbrev eReducedDerivEta :=
  MiddleFaceAssembly.EResidual.derivEta brick
private abbrev eReducedDerivRho :=
  MiddleFaceAssembly.EResidual.derivRho brick
private abbrev eReducedDerivSigma :=
  MiddleFaceAssembly.EResidual.derivSigma brick
private abbrev c4Reduced :=
  MiddleFaceAssembly.C4Residual.reduced brick
private abbrev c4ReducedDerivT :=
  MiddleFaceAssembly.C4Residual.derivT brick
private abbrev c4ReducedDerivXi :=
  MiddleFaceAssembly.C4Residual.derivXi brick
private abbrev c4ReducedDerivEta :=
  MiddleFaceAssembly.C4Residual.derivEta brick
private abbrev fReduced :=
  MiddleFaceAssembly.FResidual.reduced brick
private abbrev fReducedDerivT :=
  MiddleFaceAssembly.FResidual.derivT brick
private abbrev fReducedDerivEta :=
  MiddleFaceAssembly.FResidual.derivEta brick
private abbrev c3Reduced :=
  MiddleFaceAssembly.C3Residual.reduced brick
private abbrev c3ReducedDerivT :=
  MiddleFaceAssembly.C3Residual.derivT brick
private abbrev c3ReducedDerivRho :=
  MiddleFaceAssembly.C3Residual.derivRho brick
private abbrev c3ReducedDerivSigma :=
  MiddleFaceAssembly.C3Residual.derivSigma brick


abbrev lamMid : ℚ := (brick.lamLo + brick.lamHi) / 2
abbrev tRadius : ℚ := (brick.lamHi - brick.lamLo) / 2

def tInterval : QInterval := ⟨-tRadius, tRadius, by norm_num [tRadius, brick]⟩
def lamInterval : QInterval := ⟨brick.lamLo, brick.lamHi, brick.lamOrdered.le⟩

theorem lambda_iff_centered {lam : ℝ} :
    lamInterval.RealContains lam ↔ tInterval.RealContains (lam - (lamMid : ℝ)) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;>
      norm_num [lamInterval, tInterval, lamMid, tRadius, brick,
        LeanSuffixReflective.QInterval.RealContains] at h₁ h₂ ⊢ <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;>
      norm_num [lamInterval, tInterval, lamMid, tRadius, brick,
        LeanSuffixReflective.QInterval.RealContains] at h₁ h₂ ⊢ <;> linarith

/-- Unconditional real-range conclusion for the B0064 cell. -/
theorem lambda_in_retainedSuffix {lam : ℝ} (h : lamInterval.RealContains lam) :
    LeanSuffixAnalytic.InRetainedSuffix lam := by
  unfold LeanSuffixAnalytic.InRetainedSuffix
  norm_num [lamInterval, LeanSuffixReflective.QInterval.RealContains, brick] at h ⊢
  exact ⟨by linarith [h.1], h.2.trans (by norm_num)⟩

/-- The whole exact-data cell lies in the retained real suffix. -/
theorem brick_real_range :
    ∀ lam : ℝ, (102641 / 100000 : ℝ) ≤ lam → lam ≤ 102651 / 100000 →
      LeanSuffixAnalytic.InRetainedSuffix lam := by
  intro lam hlo hhi
  apply lambda_in_retainedSuffix
  simpa [lamInterval, LeanSuffixReflective.QInterval.RealContains, brick] using
    And.intro hlo hhi

abbrev Point := MiddleFaceAssembly.Point

def lam (p : Point) : ℝ := (lamMid : ℝ) + p.t
def x (p : Point) : ℝ := brick.centers 0 + brick.slopes 0 * p.t + p.xi
def y (p : Point) : ℝ := brick.centers 1 + brick.slopes 1 * p.t +
  brick.yXiSlope * p.xi + p.eta
def w (p : Point) : ℝ := brick.centers 2 + brick.slopes 2 * p.t + p.rho
def v (p : Point) : ℝ := brick.centers 3 + brick.slopes 3 * p.t +
  brick.vRhoSlope * p.rho + p.sigma

def B4 (p : Point) : ℝ := lam p * y p + π / 2 - x p
def D4 (p : Point) : ℝ := sin (y p) - sin (x p)
def N4 (p : Point) : ℝ := B4 p + cos (x p) * D4 p
def B3 (p : Point) : ℝ := lam p * v p + π - w p
def D3 (p : Point) : ℝ := sin (v p) - sin (w p)
def N3 (p : Point) : ℝ := B3 p + (cos (w p) + 2) * D3 p

def C4 (p : Point) : ℝ := cos (x p) - lam p * cos (y p)
def F (p : Point) : ℝ := cos (x p) * D4 p - sin (x p) * sin (y p) * B4 p
def C3 (p : Point) : ℝ := cos (w p) - lam p * cos (v p)
def E (p : Point) : ℝ :=
  2 * cos (x p) ^ 2 * N3 p - (1 + cos (w p)) ^ 2 * N4 p
def G (p : Point) : ℝ :=
  cos (x p) * (B3 p + D3 p) - (1 + cos (w p)) * B4 p

/-- The shared analytic interpretation of the checker coordinates at a point
on the recorded angle branch.  The equation and sign fields deliberately take
their checker hypotheses as arguments, so the expensive trigonometric
translation is proved only once. -/
structure PointEquationSemantics (p : Point) : Prop where
  typeThreeHeight_gt_half : 1 / 2 < (1 + cos (w p)) / 2
  typeThreeHeight_lt_one : (1 + cos (w p)) / 2 < 1
  typeFourHeight_pos : 0 < cos (x p)
  typeFourHeight_lt_one : cos (x p) < 1
  equalArea_of_E_zero : E p = 0 →
    LeanSuffixAnalytic.typeThreeArea (lam p) ((1 + cos (w p)) / 2) =
      LeanSuffixAnalytic.typeFourArea (lam p) (cos (x p))
  stationary_of_F_zero : F p = 0 →
    LeanSuffixAnalytic.typeFourFold (lam p) (cos (x p)) = 0
  perimeter_lt_of_G_neg : G p < 0 →
    LeanSuffixAnalytic.typeThreePerimeter (lam p) ((1 + cos (w p)) / 2) <
      LeanSuffixAnalytic.typeFourPerimeter (lam p) (cos (x p))

/-- The checker coordinates have their intended analytic semantics on the
recorded angle branch. -/
theorem pointEquationSemantics
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4)
    (hC4 : C4 p = 0) (hC3 : C3 p = 0) :
    PointEquationSemantics p := by
  have hs := MiddleFaceAssembly.pointEquationSemantics brick p
    (by simpa [MiddleFaceAssembly.Model.lam, lam] using hlam)
    (by simpa [MiddleFaceAssembly.Model.x, MiddleFaceAssembly.Model.y,
      MiddleFaceAssembly.Model.w, MiddleFaceAssembly.Model.v, x, y, w, v]
      using hbranches)
    (by simpa [MiddleFaceAssembly.Model.C4, MiddleFaceAssembly.Model.x,
      MiddleFaceAssembly.Model.y, MiddleFaceAssembly.Model.lam,
      C4, x, y, lam] using hC4)
    (by simpa [MiddleFaceAssembly.Model.C3, MiddleFaceAssembly.Model.w,
      MiddleFaceAssembly.Model.v, MiddleFaceAssembly.Model.lam,
      C3, w, v, lam] using hC3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [MiddleFaceAssembly.Model.w, w] using hs.typeThreeHeight_gt_half
  · simpa [MiddleFaceAssembly.Model.w, w] using hs.typeThreeHeight_lt_one
  · simpa [MiddleFaceAssembly.Model.x, x] using hs.typeFourHeight_pos
  · simpa [MiddleFaceAssembly.Model.x, x] using hs.typeFourHeight_lt_one
  · intro hE
    apply hs.equalArea_of_E_zero
    simpa [MiddleFaceAssembly.Model.E, MiddleFaceAssembly.Model.N3,
      MiddleFaceAssembly.Model.N4, MiddleFaceAssembly.Model.B3,
      MiddleFaceAssembly.Model.B4, MiddleFaceAssembly.Model.D3,
      MiddleFaceAssembly.Model.D4, MiddleFaceAssembly.Model.lam,
      MiddleFaceAssembly.Model.x, MiddleFaceAssembly.Model.y,
      MiddleFaceAssembly.Model.w, MiddleFaceAssembly.Model.v,
      E, N3, N4, B3, B4, D3, D4, lam, x, y, w, v] using hE
  · intro hF
    apply hs.stationary_of_F_zero
    simpa [MiddleFaceAssembly.Model.F, MiddleFaceAssembly.Model.B4,
      MiddleFaceAssembly.Model.D4, MiddleFaceAssembly.Model.lam,
      MiddleFaceAssembly.Model.x, MiddleFaceAssembly.Model.y,
      F, B4, D4, lam, x, y] using hF
  · intro hG
    apply hs.perimeter_lt_of_G_neg
    simpa [MiddleFaceAssembly.Model.G, MiddleFaceAssembly.Model.B3,
      MiddleFaceAssembly.Model.B4, MiddleFaceAssembly.Model.D3,
      MiddleFaceAssembly.Model.lam, MiddleFaceAssembly.Model.x,
      MiddleFaceAssembly.Model.y, MiddleFaceAssembly.Model.w,
      MiddleFaceAssembly.Model.v, G, B3, B4, D3, lam, x, y, w, v] using hG

/-- The primitive checker equations have their intended analytic meaning on
the recorded angle branch.  In particular, `E = 0` is equal weighted area,
`F = 0` is the type-(iv) stationary fold, and `G < 0` is strict type-(iii)
perimeter improvement. -/
theorem point_equations_to_scalar_improvement
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4)
    (hC4 : C4 p = 0) (hF : F p = 0)
    (hC3 : C3 p = 0) (hE : E p = 0) (hG : G p < 0) :
    let h₃ := (1 + cos (w p)) / 2
    let h₄ := cos (x p)
    1 / 2 < h₃ ∧ h₃ < 1 ∧
      0 < h₄ ∧ h₄ < 1 ∧
      LeanSuffixAnalytic.typeThreeArea (lam p) h₃ =
        LeanSuffixAnalytic.typeFourArea (lam p) h₄ ∧
      LeanSuffixAnalytic.typeFourFold (lam p) h₄ = 0 ∧
      LeanSuffixAnalytic.typeThreePerimeter (lam p) h₃ <
        LeanSuffixAnalytic.typeFourPerimeter (lam p) h₄ ∧
      LeanSuffixAnalytic.reducedFoldGap (lam p) h₃ h₄ < 0 := by
  dsimp only
  have hs := pointEquationSemantics p hlam hbranches hC4 hC3
  have harea := hs.equalArea_of_E_zero hE
  have hfold := hs.stationary_of_F_zero hF
  have hperimeter := hs.perimeter_lt_of_G_neg hG
  have hgap :=
    (LeanSuffixAnalytic.stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) hs.typeThreeHeight_gt_half))
      (ne_of_gt hs.typeFourHeight_pos) harea hfold).mp hperimeter
  exact ⟨hs.typeThreeHeight_gt_half, hs.typeThreeHeight_lt_one,
    hs.typeFourHeight_pos, hs.typeFourHeight_lt_one, harea, hfold,
    hperimeter, hgap⟩

def K3 (p : Point) : ℝ :=
  let h3 := (1 + cos (w p)) / 2
  4 * h3 * ((1 + cos (w p)) / sin (w p) -
    (lam p ^ 2 + cos (w p)) / (lam p * (lam p * sin (v p)))) -
    2 * (B3 p + D3 p)

/-- On the certified angle branch, the checker quantity `K3` is exactly the
numerator of the type-(iii) area derivative. -/
theorem typeThreeArea_deriv_eq_K3
    (p : Point) (hlam : 1 < lam p)
    (hbranches :
      0 < w p ∧ w p < π / 4 ∧ 0 < v p ∧ v p < π / 4)
    (hC3 : C3 p = 0) :
    deriv (LeanSuffixAnalytic.typeThreeArea (lam p))
        ((1 + cos (w p)) / 2) =
      K3 p / ((1 + cos (w p)) / 2) ^ 3 := by
  simpa [MiddleFaceAssembly.Model.lam, MiddleFaceAssembly.Model.w,
    MiddleFaceAssembly.Model.v, MiddleFaceAssembly.Model.C3,
    MiddleFaceAssembly.Model.K3, MiddleFaceAssembly.Model.B3,
    MiddleFaceAssembly.Model.D3, lam, w, v, C3, K3, B3, D3] using
    (MiddleFaceAssembly.typeThreeArea_deriv_eq_K3 brick p
      (by simpa [MiddleFaceAssembly.Model.lam, lam] using hlam)
      (by simpa [MiddleFaceAssembly.Model.w, MiddleFaceAssembly.Model.v,
        w, v] using hbranches)
      (by simpa [MiddleFaceAssembly.Model.C3, MiddleFaceAssembly.Model.w,
        MiddleFaceAssembly.Model.v, MiddleFaceAssembly.Model.lam,
        C3, w, v, lam] using hC3))

def vars (p : Point) : Vec4 := ![p.xi, p.eta, p.rho, p.sigma]
def radiiReal : Vec4 := fun j => (brick.radii j : ℝ)
def pointOf (t : ℝ) (z : Vec4) : Point := ⟨t, z 0, z 1, z 2, z 3⟩

def rootMap (t : ℝ) (z : Vec4) : Vec4 :=
  let p := pointOf t z
  ![-F p, C4 p, E p, C3 p]

theorem rootMap_continuous (t : ℝ) : Continuous (rootMap t) := by
  apply continuous_pi
  intro j
  fin_cases j <;>
    simp [rootMap, F, C4, E, C3, N3, N4, B3, B4, D3, D4, pointOf,
      lam, x, y, w, v] <;> fun_prop





/-- Exact Taylor enclosure for every type-(iv) `x` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c4_sin_x_range {q : ℝ}
    (hq : (19739 / 100000 : ℝ) ≤ q ∧ q ≤ 19758 / 100000) :
    (196110 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (196297 / 1000000 : ℝ) := by
  have hmonoLo : sin (19739 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (19758 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (19739 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (19758 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iv) `cos x` occurring in the
`F` face estimates. -/
private theorem c4_cos_x_range {q : ℝ}
    (hq : (19739 / 100000 : ℝ) ≤ q ∧ q ≤ 19758 / 100000) :
    (980544 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (980582 / 1000000 : ℝ) := by
  have hmonoLo : cos (19758 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (19739 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (19758 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (19739 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iv) `y` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c4_sin_y_range {q : ℝ}
    (hq : (29995 / 100000 : ℝ) ≤ q ∧ q ≤ 30039 / 100000) :
    (295472 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (295893 / 1000000 : ℝ) := by
  have hmonoLo : sin (29995 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (30039 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (29995 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (30039 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for the correlated `cos y` term in the `t`
derivative of `C4`. -/
private theorem c4_cos_y_range {q : ℝ}
    (hq : (29995 / 100000 : ℝ) ≤ q ∧ q ≤ 30039 / 100000) :
    (955221 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (955352 / 1000000 : ℝ) := by
  have hmonoLo : cos (30039 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (29995 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (30039 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (29995 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iii) `w` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c3_sin_w_range {q : ℝ}
    (hq : (45427 / 100000 : ℝ) ≤ q ∧ q ≤ 45480 / 100000) :
    (438806 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (439283 / 1000000 : ℝ) := by
  have hmonoLo : sin (45427 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (45480 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (45427 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (45480 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for every type-(iii) `v` occurring in the
correlation-preserving mean-value estimates below. -/
private theorem c3_sin_v_range {q : ℝ}
    (hq : (50441 / 100000 : ℝ) ≤ q ∧ q ≤ 50506 / 100000) :
    (483291 / 1000000 : ℝ) ≤ sin q ∧
      sin q ≤ (483860 / 1000000 : ℝ) := by
  have hmonoLo : sin (50441 / 100000 : ℝ) ≤ sin q :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hmonoHi : sin q ≤ sin (50506 / 100000 : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hlo := (sinTaylor27Interval_sound (50441 / 100000)).1
  have hhi := (sinTaylor27Interval_sound (50506 / 100000)).2
  norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith

/-- Exact Taylor enclosure for the correlated `cos v` term in the `t`
derivative of `C3`. -/
private theorem c3_cos_v_range {q : ℝ}
    (hq : (50441 / 100000 : ℝ) ≤ q ∧ q ≤ 50506 / 100000) :
    (875145 / 1000000 : ℝ) ≤ cos q ∧
      cos q ≤ (875460 / 1000000 : ℝ) := by
  have hmonoLo : cos (50506 / 100000 : ℝ) ≤ cos q :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hmonoHi : cos q ≤ cos (50441 / 100000 : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  have hlo := (cosTaylor26Interval_sound (50506 / 100000)).1
  have hhi := (cosTaylor26Interval_sound (50441 / 100000)).2
  norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hlo hhi
  constructor <;> norm_num <;> linarith


/- Tighter trigonometric enclosures used only for the cancellation-sensitive
`E` derivative.  The decimal endpoints are exact rationals. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_x_trig_range {q : ℝ}
    (hq : (19739000 / 100000000 : ℝ) ≤ q ∧
      q ≤ 19758000 / 100000000) :
    (19611000 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (19629700 / 100000000 : ℝ) ∧
      (98054400 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (98058200 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (19739000 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (19758000 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (19758000 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (19739000 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_y_trig_range {q : ℝ}
    (hq : (29995000 / 100000000 : ℝ) ≤ q ∧
      q ≤ 30039000 / 100000000) :
    (29547200 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (29589300 / 100000000 : ℝ) ∧
      (95522100 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (95535200 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (29995000 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (30039000 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (30039000 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (29995000 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_w_trig_range {q : ℝ}
    (hq : (45427000 / 100000000 : ℝ) ≤ q ∧
      q ≤ 45480000 / 100000000) :
    (43880600 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (43928300 / 100000000 : ℝ) ∧
      (89834800 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (89858200 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (45427000 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (45480000 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (45480000 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (45427000 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith

set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem e_v_trig_range {q : ℝ}
    (hq : (50441000 / 100000000 : ℝ) ≤ q ∧
      q ≤ 50506000 / 100000000) :
    (48329100 / 100000000 : ℝ) ≤ sin q ∧
      sin q ≤ (48386000 / 100000000 : ℝ) ∧
      (87514500 / 100000000 : ℝ) ≤ cos q ∧
      cos q ≤ (87546000 / 100000000 : ℝ) := by
  have hslo := (sinTaylor27Interval_sound (50441000 / 100000000)).1
  have hshi := (sinTaylor27Interval_sound (50506000 / 100000000)).2
  have hclo := (cosTaylor26Interval_sound (50506000 / 100000000)).1
  have hchi := (cosTaylor26Interval_sound (50441000 / 100000000)).2
  have hsLoMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.1
  have hsHiMono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_d6]) hq.2
  have hcLoMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith [Real.pi_gt_d6]) hq.2
  have hcHiMono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num) (by linarith [Real.pi_gt_d6]) hq.1
  norm_num [sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hslo hshi hclo hchi
  constructor
  · norm_num
    linarith
  constructor
  · norm_num
    linarith
  constructor <;> norm_num <;> linarith
/- A single correlation-preserving interval certificate bounds all five
directional derivatives of the equal-area residual on B0064. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem eReduced_deriv_bounds {t xi eta rho sigma : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧
      sigma ≤ 1 / 1000000) :
    |eReducedDerivT t xi eta rho sigma| ≤ (7 / 100 : ℝ) ∧
      |eReducedDerivXi t xi eta rho sigma| ≤ (3 / 500 : ℝ) ∧
      |eReducedDerivEta t xi eta rho sigma| ≤ (721 / 100 : ℝ) ∧
      (47 / 25 : ℝ) ≤ eReducedDerivRho t xi eta rho sigma ∧
      |eReducedDerivSigma t xi eta rho sigma| ≤ (351 / 50 : ℝ) := by
  let ll := (lamMid : ℝ) + t
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ww := (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho
  let vv := (brick.centers 3 : ℝ) + brick.slopes 3 * t +
    brick.vRhoSlope * rho + sigma
  have hll : (102641 / 100000 : ℝ) ≤ ll ∧ ll ≤ 102651 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hxx : (19739000 / 100000000 : ℝ) ≤ xx ∧
      xx ≤ 19758000 / 100000000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (29995000 / 100000000 : ℝ) ≤ yy ∧
      yy ≤ 30039000 / 100000000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hww : (45427000 / 100000000 : ℝ) ≤ ww ∧
      ww ≤ 45480000 / 100000000 := by
    dsimp [ww]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    constructor <;> linarith
  have hvv : (50441000 / 100000000 : ℝ) ≤ vv ∧
      vv ≤ 50506000 / 100000000 := by
    dsimp [vv]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    constructor <;> linarith
  have hxtrig := e_x_trig_range hxx
  have hytrig := e_y_trig_range hyy
  have hwtrig := e_w_trig_range hww
  have hvtrig := e_v_trig_range hvv
  let ell : CertificateExpr := .atom ll
    ⟨102641 / 100000, 102651 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let ex : CertificateExpr := .atom xx
    ⟨19739000 / 100000000, 19758000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let ey : CertificateExpr := .atom yy
    ⟨29995000 / 100000000, 30039000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ew : CertificateExpr := .atom ww
    ⟨45427000 / 100000000, 45480000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hww)
  let ev : CertificateExpr := .atom vv
    ⟨50441000 / 100000000, 50506000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hvv)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨19611000 / 100000000, 19629700 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hxtrig.1 hxtrig.2.1)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨98054400 / 100000000, 98058200 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hxtrig.2.2.1 hxtrig.2.2.2)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨29547200 / 100000000, 29589300 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hytrig.1 hytrig.2.1)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨95522100 / 100000000, 95535200 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hytrig.2.2.1 hytrig.2.2.2)
  let esw : CertificateExpr := .atom (sin ww)
    ⟨43880600 / 100000000, 43928300 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hwtrig.1 hwtrig.2.1)
  let ecw : CertificateExpr := .atom (cos ww)
    ⟨89834800 / 100000000, 89858200 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hwtrig.2.2.1 hwtrig.2.2.2)
  let esv : CertificateExpr := .atom (sin vv)
    ⟨48329100 / 100000000, 48386000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hvtrig.1 hvtrig.2.1)
  let ecv : CertificateExpr := .atom (cos vv)
    ⟨87514500 / 100000000, 87546000 / 100000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using
        And.intro hvtrig.2.2.1 hvtrig.2.2.2)
  let ep : CertificateExpr := .atom π piInterval piInterval_sound
  let ed (dl dx dy dw dv : ℚ) : CertificateExpr :=
    formulaDerivExpr ell ex ey ew ev esx ecx esy ecy esw ecw esv ecv ep
      dl dx dy dw dv
  have hvalue (dl dx dy dw dv : ℚ) :
      (ed dl dx dy dw dv).value =
        formulaDeriv ll xx yy ww vv
          (dl : ℝ) (dx : ℝ) (dy : ℝ) (dw : ℝ) (dv : ℝ) := by
    simp [ed, MiddleFaceAssembly.EResidual.formulaDerivExpr, ell, ex, ey, ew,
      ev, esx, ecx, esy, ecy, esw, ecw, esv, ecv, ep,
      CertificateExpr.value, MiddleFaceAssembly.EResidual.formulaDeriv]
    ring
  have hvT :
      (ed 1 (brick.slopes 0) (brick.slopes 1) (brick.slopes 2)
        (brick.slopes 3)).value =
        eReducedDerivT t xi eta rho sigma := by
    rw [hvalue]
    simp [MiddleFaceAssembly.EResidual.derivT, ll, xx, yy, ww, vv]
  have hvXi :
      (ed 0 1 brick.yXiSlope 0 0).value =
        eReducedDerivXi t xi eta rho sigma := by
    rw [hvalue]
    simp [MiddleFaceAssembly.EResidual.derivXi, ll, xx, yy, ww, vv]
  have hvEta :
      (ed 0 0 1 0 0).value =
        eReducedDerivEta t xi eta rho sigma := by
    rw [hvalue]
    simp [MiddleFaceAssembly.EResidual.derivEta, ll, xx, yy, ww, vv]
  have hvRho :
      (ed 0 0 0 1 brick.vRhoSlope).value =
        eReducedDerivRho t xi eta rho sigma := by
    rw [hvalue]
    simp [MiddleFaceAssembly.EResidual.derivRho, ll, xx, yy, ww, vv]
  have hvSigma :
      (ed 0 0 0 0 1).value =
        eReducedDerivSigma t xi eta rho sigma := by
    rw [hvalue]
    simp [MiddleFaceAssembly.EResidual.derivSigma, ll, xx, yy, ww, vv]
  have hT := CertificateExpr.sound
    (ed 1 (brick.slopes 0) (brick.slopes 1) (brick.slopes 2)
      (brick.slopes 3))
  have hXi := CertificateExpr.sound (ed 0 1 brick.yXiSlope 0 0)
  have hEta := CertificateExpr.sound (ed 0 0 1 0 0)
  have hRho := CertificateExpr.sound (ed 0 0 0 1 brick.vRhoSlope)
  have hSigma := CertificateExpr.sound (ed 0 0 0 0 1)
  rw [hvT] at hT
  rw [hvXi] at hXi
  rw [hvEta] at hEta
  rw [hvRho] at hRho
  rw [hvSigma] at hSigma
  norm_num [ed, MiddleFaceAssembly.EResidual.formulaDerivExpr, ell, ex, ey,
    ew, ev, esx, ecx, esy, ecy, esw, ecw, esv, ecv, ep, piInterval,
    CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    brick, Matrix.cons_val_two, Matrix.cons_val_three] at hT hXi hEta hRho hSigma
  constructor
  · rw [abs_le]
    constructor <;> linarith [hT.1, hT.2]
  constructor
  · rw [abs_le]
    constructor <;> linarith [hXi.1, hXi.2]
  constructor
  · rw [abs_le]
    constructor <;> linarith [hEta.1, hEta.2]
  constructor
  · linarith [hRho.1]
  · rw [abs_le]
    constructor <;> linarith [hSigma.1, hSigma.2]

/-- Exact affine box arithmetic puts every angle in the analytic branch used by
the B0064 brick. -/
theorem affine_branches :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      let p := pointOf t z
      0 < x p ∧ x p < π / 4 ∧ 0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧ 0 < v p ∧ v p < π / 4 := by
  intro t z ht hz
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  dsimp only
  norm_num [pointOf, x, y, w, v, brick, Matrix.cons_val_two,
    Matrix.cons_val_three]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  constructor
  · linarith [Real.pi_gt_d6]
  constructor
  · linarith
  · linarith [Real.pi_gt_d6]

/-- Exact affine box arithmetic separates the type-(iv) and type-(iii) angle
pairs throughout the B0064 brick. -/
theorem affine_angleOrder :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      let p := pointOf t z
      x p < y p ∧ w p < v p := by
  intro t z ht hz
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  dsimp only
  norm_num [pointOf, x, y, w, v, brick, Matrix.cons_val_two,
    Matrix.cons_val_three]
  constructor <;> linarith

/-! The following coarse `K3` enclosure is intentionally uniform over every
middle-inventory brick.  Cell-specific Taylor endpoints still tighten the
trigonometric range before these shared rational bounds are used. -/

/-- The type-(iii) equal-area branch is strictly descending throughout the
B0064 cell. -/
theorem descendingK3 :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      K3 (pointOf t z) < 0 := by
  intro t z ht hz
  let p := pointOf t z
  have hz0 := hz 0
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz2 hz3
  have hlamLo : (1 : ℝ) < lam p := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hlamHi : lam p < (26 / 25 : ℝ) := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hwLo : (2 / 5 : ℝ) ≤ w p := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwHi : w p ≤ (57 / 125 : ℝ) := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvLo : (9 / 20 : ℝ) ≤ v p := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvHi : v p ≤ (253 / 500 : ℝ) := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwI :
      (⟨2 / 5, 57 / 125, by norm_num⟩ : QInterval).RealContains (w p) := by
    constructor <;> norm_num <;> assumption
  have hvI :
      (⟨9 / 20, 253 / 500, by norm_num⟩ : QInterval).RealContains (v p) := by
    constructor <;> norm_num <;> assumption
  have hsw :
      (⟨389 / 1000, 47 / 100, by norm_num⟩ : QInterval).RealContains
        (sin (w p)) := by
    apply realContains_sin_interval hwI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (sinTaylor27Interval_sound (2 / 5)).1
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (sinTaylor27Interval_sound (57 / 125)).2
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hsv :
      (⟨2 / 5, 51 / 100, by norm_num⟩ : QInterval).RealContains
        (sin (v p)) := by
    apply realContains_sin_interval hvI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (sinTaylor27Interval_sound (9 / 20)).1
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (sinTaylor27Interval_sound (253 / 500)).2
      norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hsvHi : sin (v p) ≤ (51 / 100 : ℝ) := by
    norm_num
    nlinarith [hsv.2]
  have hcw :
      (⟨22 / 25, 461 / 500, by norm_num⟩ : QInterval).RealContains
        (cos (w p)) := by
    apply realContains_cos_interval hwI
    · constructor <;> linarith [Real.pi_gt_d6]
    · have h := (cosTaylor26Interval_sound (57 / 125)).1
      norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
    · have h := (cosTaylor26Interval_sound (2 / 5)).2
      norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
        Nat.factorial] at h
      norm_num
      linarith
  have hswPos : 0 < sin (w p) := lt_of_lt_of_le (by norm_num) hsw.1
  have hsvPos : 0 < sin (v p) := lt_of_lt_of_le (by norm_num) hsv.1
  have hlamPos : 0 < lam p := lt_trans (by norm_num) hlamLo
  have hlamSqPos : 0 < lam p ^ 2 := sq_pos_of_pos hlamPos
  have hA : (1 + cos (w p)) / sin (w p) < (99 / 20 : ℝ) := by
    apply (div_lt_iff₀ hswPos).2
    nlinarith [hcw.2, hsw.1]
  have hlamSqHi : lam p ^ 2 < (676 / 625 : ℝ) := by
    nlinarith
  have hdenHi :
      lam p * (lam p * sin (v p)) < (69 / 125 : ℝ) := by
    rw [show lam p * (lam p * sin (v p)) =
      lam p ^ 2 * sin (v p) by ring]
    have h₁ :
        lam p ^ 2 * sin (v p) ≤ lam p ^ 2 * (51 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hsvHi hlamSqPos.le
    have h₂ :
        lam p ^ 2 * (51 / 100 : ℝ) <
          (676 / 625 : ℝ) * (51 / 100 : ℝ) :=
      mul_lt_mul_of_pos_right hlamSqHi (by norm_num)
    norm_num at h₂ ⊢
    exact h₁.trans_lt (h₂.trans (by norm_num))
  have hdenPos : 0 < lam p * (lam p * sin (v p)) := by positivity
  have hnumLo : (47 / 25 : ℝ) < lam p ^ 2 + cos (w p) := by
    nlinarith [hcw.1]
  have hB : (17 / 5 : ℝ) <
      (lam p ^ 2 + cos (w p)) /
        (lam p * (lam p * sin (v p))) := by
    apply (lt_div_iff₀ hdenPos).2
    nlinarith [hnumLo, hdenHi]
  have hdiff :
      (1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p))) <
        (31 / 20 : ℝ) := by
    linarith
  have hfactorPos : 0 < 2 * (1 + cos (w p)) := by
    nlinarith [hcw.1]
  have hfactorHi : 2 * (1 + cos (w p)) ≤ (961 / 250 : ℝ) := by
    nlinarith [hcw.2]
  have hproduct :
      2 * (1 + cos (w p)) *
          ((1 + cos (w p)) / sin (w p) -
            (lam p ^ 2 + cos (w p)) /
              (lam p * (lam p * sin (v p)))) <
        (149 / 25 : ℝ) := by
    by_cases hd :
        0 ≤ (1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))
    · nlinarith [mul_lt_mul_of_pos_left hdiff hfactorPos,
        mul_le_mul_of_nonneg_right hfactorHi hd]
    · have hd' := lt_of_not_ge hd
      have hnegative := mul_neg_of_pos_of_neg hfactorPos hd'
      norm_num at hnegative ⊢
      linarith
  have hlamv : (9 / 20 : ℝ) < lam p * v p := by
    have hvPos : 0 < v p := lt_of_lt_of_le (by norm_num) hvLo
    nlinarith [mul_lt_mul_of_pos_right hlamLo hvPos]
  have hbase : (3 : ℝ) < B3 p + D3 p := by
    unfold B3 D3
    nlinarith [hlamv, Real.pi_gt_d6, hwHi, hsv.1, hsw.2]
  change K3 p < 0
  unfold K3
  dsimp only
  rw [show
    4 * ((1 + cos (w p)) / 2) *
        ((1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))) =
      2 * (1 + cos (w p)) *
        ((1 + cos (w p)) / sin (w p) -
          (lam p ^ 2 + cos (w p)) /
            (lam p * (lam p * sin (v p)))) by ring]
  linarith

/-- A direct rational interval decomposition proves the scalar perimeter gap
throughout the B0064 brick.  The explicit negative margin keeps this
leaf independent of the root-existence argument. -/
theorem gap_upper :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      G (pointOf t z) < -(437 / 1000000 : ℝ) := by
  intro t z ht hz
  let p := pointOf t z
  have hz0 := hz 0
  have hz1 := hz 1
  have hz2 := hz 2
  have hz3 := hz 3
  norm_num [tInterval, tRadius, brick,
    LeanSuffixReflective.QInterval.RealContains] at ht
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hz0 hz1 hz2 hz3
  have hlamLo : (102641 / 100000 : ℝ) ≤ lam p := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hlamHi : lam p ≤ (102651 / 100000 : ℝ) := by
    dsimp [p, pointOf, lam]
    norm_num [lamMid, brick]
    linarith
  have hxLo : (19739 / 100000 : ℝ) ≤ x p := by
    dsimp [p, pointOf, x]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hxHi : x p ≤ (19758 / 100000 : ℝ) := by
    dsimp [p, pointOf, x]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hyLo : (29995 / 100000 : ℝ) ≤ y p := by
    dsimp [p, pointOf, y]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwLo : (45427 / 100000 : ℝ) ≤ w p := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hwHi : w p ≤ (45480 / 100000 : ℝ) := by
    dsimp [p, pointOf, w]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvLo : (50441 / 100000 : ℝ) ≤ v p := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hvHi : v p ≤ (50506 / 100000 : ℝ) := by
    dsimp [p, pointOf, v]
    norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
    linarith
  have hcxHi : cos (x p) ≤ (980582 / 1000000 : ℝ) := by
    have hmono : cos (x p) ≤ cos (19739 / 100000 : ℝ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_gt_d6]) hxLo
    have h := (cosTaylor26Interval_sound (19739 / 100000)).2
    norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hcwLo : (898348 / 1000000 : ℝ) ≤ cos (w p) := by
    have hmono : cos (45480 / 100000 : ℝ) ≤ cos (w p) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_gt_d6]) hwHi
    have h := (cosTaylor26Interval_sound (45480 / 100000)).1
    norm_num [cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hsvHi : sin (v p) ≤ (483860 / 1000000 : ℝ) := by
    have hmono : sin (v p) ≤ sin (50506 / 100000 : ℝ) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_d6]) hvHi
    have h := (sinTaylor27Interval_sound (50506 / 100000)).2
    norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hswLo : (438806 / 1000000 : ℝ) ≤ sin (w p) := by
    have hmono : sin (45427 / 100000 : ℝ) ≤ sin (w p) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_d6]) hwLo
    have h := (sinTaylor27Interval_sound (45427 / 100000)).1
    norm_num [sinTaylor27Interval, sinTaylor27, Finset.sum_range_succ,
      Nat.factorial] at h
    linarith
  have hlamvHi : lam p * v p ≤
      (102651 / 100000 : ℝ) * (50506 / 100000 : ℝ) := by
    exact mul_le_mul hlamHi hvHi (by linarith) (by norm_num)
  have hlamyLo : (102641 / 100000 : ℝ) * (29995 / 100000 : ℝ) ≤
      lam p * y p := by
    exact mul_le_mul hlamLo hyLo (by norm_num) (by linarith)
  have hAHi : B3 p + D3 p < (16255 / 5000 : ℝ) := by
    unfold B3 D3
    linarith [Real.pi_lt_d6]
  have hALo : (0 : ℝ) < B3 p + D3 p := by
    unfold B3 D3
    have hsinv : -(1 : ℝ) ≤ sin (v p) := neg_one_le_sin _
    have hsinw : sin (w p) ≤ 1 := sin_le_one _
    nlinarith [Real.pi_gt_d6]
  have hBLo : (16810 / 10000 : ℝ) < B4 p := by
    unfold B4
    linarith [Real.pi_gt_d6]
  have hfirst : cos (x p) * (B3 p + D3 p) <
      (980582 / 1000000 : ℝ) * (16255 / 5000 : ℝ) := by
    have hcxPos : 0 < cos (x p) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
        by linarith [Real.pi_gt_d6]⟩
    have hmul := mul_lt_mul hAHi hcxHi hcxPos (by norm_num)
    nlinarith
  have hsecond : (189834 / 100000 : ℝ) * (16810 / 10000 : ℝ) <
      (1 + cos (w p)) * B4 p := by
    have hf : (189834 / 100000 : ℝ) < 1 + cos (w p) := by linarith
    exact mul_lt_mul hf hBLo.le (by norm_num) (by linarith)
  unfold G
  nlinarith [hfirst, hsecond]


/-- Exact Taylor enclosure of the correlated `C4` residual at the brick
origin. -/
private theorem c4Reduced_origin_abs_lt :
    |c4Reduced 0 0 0| < (1 / 25000000 : ℝ) := by
  have hxlo := (cosTaylor26Interval_sound (brick.centers 0)).1
  have hxhi := (cosTaylor26Interval_sound (brick.centers 0)).2
  have hylo := (cosTaylor26Interval_sound (brick.centers 1)).1
  have hyhi := (cosTaylor26Interval_sound (brick.centers 1)).2
  norm_num [c4Reduced, MiddleFaceAssembly.C4Residual.reduced, brick, lamMid,
    cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ,
    Nat.factorial] at hxlo hxhi hylo hyhi ⊢
  rw [abs_lt]
  constructor <;> nlinarith

/-- Exact-rational enclosure data for the three reusable `C4` derivative
bounds on the complete brick. -/
private theorem c4Reduced_derivativeBounds :
    MiddleFaceAssembly.C4Residual.DerivativeBounds brick := by
  intro t xi eta ht hxi heta
  have hxArg :
      (19739 / 100000 : ℝ) ≤
          (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi ∧
        (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi ≤
          19758 / 100000 := by
    norm_num [brick]
    constructor <;> linarith
  have hyArg :
      (29995 / 100000 : ℝ) ≤
          (brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + eta ∧
        (brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + eta ≤ 30039 / 100000 := by
    norm_num [brick]
    constructor <;> linarith
  have hsx := c4_sin_x_range hxArg
  have hsy := c4_sin_y_range hyArg
  have hcy := c4_cos_y_range hyArg
  have hlamLo : (102641 / 100000 : ℝ) ≤ (lamMid : ℝ) + t := by
    norm_num [lamMid, brick]
    linarith
  have hlamHi : (lamMid : ℝ) + t ≤ (102651 / 100000 : ℝ) := by
    norm_num [lamMid, brick]
    linarith
  have hprodLo :
      (102641 / 100000 : ℝ) * (295472 / 1000000 : ℝ) ≤
        ((lamMid : ℝ) + t) *
          sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + eta) :=
    mul_le_mul hlamLo hsy.1 (by norm_num) (by linarith)
  have hprodHi :
      ((lamMid : ℝ) + t) *
          sin ((brick.centers 1 : ℝ) + brick.slopes 1 * t +
            brick.yXiSlope * xi + eta) ≤
        (102651 / 100000 : ℝ) * (295893 / 1000000 : ℝ) :=
    mul_le_mul hlamHi hsy.2 (by linarith) (by norm_num)
  constructor
  · rw [abs_le]
    norm_num [c4ReducedDerivT, MiddleFaceAssembly.C4Residual.derivT,
      brick, lamMid] at hsx hcy hprodLo hprodHi ⊢
    constructor <;> linarith
  · constructor
    · rw [abs_le]
      norm_num [c4ReducedDerivXi, MiddleFaceAssembly.C4Residual.derivXi,
        brick, lamMid] at hsx hprodLo hprodHi ⊢
      constructor <;> linarith
    · norm_num [c4ReducedDerivEta, MiddleFaceAssembly.C4Residual.derivEta,
        brick, lamMid] at hprodLo ⊢
      linarith

/-- The lower `eta` face has the required `C4` sign with the strict exact
rational margin `11/10 · 10⁻⁹`. -/
theorem C4_eta_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 1 = -radiiReal 1 →
      C4 (pointOf t z) < -(11 / 10000000000 : ℝ) := by
  intro t z ht hz heta
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hxi := hz 0
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi
  have heta' : z 1 = -(1 / 1000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at heta
    exact heta
  change c4Reduced t (z 0) (z 1) < -(11 / 10000000000 : ℝ)
  rw [heta']
  exact MiddleFaceAssembly.C4Residual.low_face_margin brick
    c4Reduced_derivativeBounds c4Reduced_origin_abs_lt ht' hxi

/-- The upper `eta` face has the required `C4` sign with the strict exact
rational margin `11/10 · 10⁻⁹`. -/
theorem C4_eta_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 1 = radiiReal 1 →
      (11 / 10000000000 : ℝ) < C4 (pointOf t z) := by
  intro t z ht hz heta
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hxi := hz 0
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi
  have heta' : z 1 = (1 / 1000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at heta
    exact heta
  change (11 / 10000000000 : ℝ) < c4Reduced t (z 0) (z 1)
  rw [heta']
  exact MiddleFaceAssembly.C4Residual.high_face_margin brick
    c4Reduced_derivativeBounds c4Reduced_origin_abs_lt ht' hxi


/- Exact point certificate at the lower `xi` face, before the small `t` and
`eta` variations are introduced. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem fReduced_low_anchor :
    (8 / 1000000 : ℝ) < fReduced 0 (-(1 / 100000)) 0 := by
  let xq : ℚ := brick.centers 0 - 1 / 100000
  let yq : ℚ := brick.centers 1 - brick.yXiSlope / 100000
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let b : CertificateExpr :=
    .add (.rational (lamMid * yq - xq)) (.mul (.rational (1 / 2)) p)
  let e : CertificateExpr :=
    .add (.mul cx (.add sy (.neg sx)))
      (.neg (.mul (.mul sx sy) b))
  have he := CertificateExpr.sound e
  have hv : e.value = fReduced 0 (-(1 / 100000)) 0 := by
    norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.value,
      fReduced, MiddleFaceAssembly.FResidual.reduced, brick, lamMid]
    ring
  rw [hv] at he
  have hlo := he.1
  norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial, brick, lamMid] at hlo
  linarith


/- Exact point certificate at the upper `xi` face. -/
set_option maxHeartbeats 1000000 in
-- Exact degree-27/26 endpoint normalization exceeds the default heartbeat budget.
private theorem fReduced_high_anchor :
    fReduced 0 (1 / 100000) 0 < -(8 / 1000000 : ℝ) := by
  let xq : ℚ := brick.centers 0 + 1 / 100000
  let yq : ℚ := brick.centers 1 + brick.yXiSlope / 100000
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let b : CertificateExpr :=
    .add (.rational (lamMid * yq - xq)) (.mul (.rational (1 / 2)) p)
  let e : CertificateExpr :=
    .add (.mul cx (.add sy (.neg sx)))
      (.neg (.mul (.mul sx sy) b))
  have he := CertificateExpr.sound e
  have hv : e.value = fReduced 0 (1 / 100000) 0 := by
    norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.value,
      fReduced, MiddleFaceAssembly.FResidual.reduced, brick, lamMid]
    ring
  rw [hv] at he
  have hhi := he.2
  norm_num [e, b, p, sx, cx, sy, xq, yq, CertificateExpr.enclosure,
    QInterval.mul, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    sinTaylor27Interval, sinTaylor27, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial, brick, lamMid] at hhi
  linarith

/- Correlation-preserving interval bound for the `t` derivative of `F`.
The complete derivative is enclosed as one expression, so its large summands
are never rounded independently before cancellation. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem fReducedDerivT_abs_le {q xi : ℝ}
    (hq : -(1 / 20000 : ℝ) ≤ q ∧ q ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    |fReducedDerivT q xi 0| ≤ (1 / 200 : ℝ) := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * q + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * q +
    brick.yXiSlope * xi
  let ll := (lamMid : ℝ) + q
  have hxx : (19739 / 100000 : ℝ) ≤ xx ∧ xx ≤ 19758 / 100000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (29995 / 100000 : ℝ) ≤ yy ∧ yy ≤ 30039 / 100000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hll : (102641 / 100000 : ℝ) ≤ ll ∧ ll ≤ 102651 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hsx := c4_sin_x_range hxx
  have hcx := c4_cos_x_range hxx
  have hsy := c4_sin_y_range hyy
  have hcy := c4_cos_y_range hyy
  let exx : CertificateExpr := .atom xx
    ⟨19739 / 100000, 19758 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let eyy : CertificateExpr := .atom yy
    ⟨29995 / 100000, 30039 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ell : CertificateExpr := .atom ll
    ⟨102641 / 100000, 102651 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨196110 / 1000000, 196297 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsx)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨980544 / 1000000, 980582 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcx)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨295472 / 1000000, 295893 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsy)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨955221 / 1000000, 955352 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcy)
  let ep : CertificateExpr := .atom π
    ⟨3141592 / 1000000, 3141593 / 1000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d6]
        · norm_num at ⊢
          linarith [Real.pi_lt_d6])
  let ebb : CertificateExpr :=
    .add (.add (.mul ell eyy) (.mul (.rational (1 / 2)) ep)) (.neg exx)
  let ea : CertificateExpr := .rational (brick.slopes 0)
  let eb : CertificateExpr := .rational (brick.slopes 1)
  let e1 : CertificateExpr :=
    .mul (.mul (.neg ea) esx) (.add esy (.neg esx))
  let e2 : CertificateExpr :=
    .mul ecx (.add (.mul eb ecy) (.neg (.mul ea ecx)))
  let e3 : CertificateExpr :=
    .add
      (.add (.mul (.mul (.mul ea ecx) esy) ebb)
        (.mul (.mul (.mul esx eb) ecy) ebb))
      (.mul (.mul esx esy)
        (.add (.add eyy (.mul ell eb)) (.neg ea)))
  let ed : CertificateExpr := .add (.add e1 e2) (.neg e3)
  have he := CertificateExpr.sound ed
  have hv : ed.value = fReducedDerivT q xi 0 := by
    simp [ed, e1, e2, e3, ea, eb, ebb, ep, exx, eyy, ell, esx, ecx,
      esy, ecy, CertificateExpr.value, fReducedDerivT,
      MiddleFaceAssembly.FResidual.derivT, xx, yy, ll]
    ring
  rw [hv] at he
  rw [abs_le]
  norm_num [ed, e1, e2, e3, ea, eb, ebb, ep, exx, eyy, ell, esx, ecx,
    esy, ecy, CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, brick] at he ⊢
  constructor <;> linarith [he.1, he.2]

/- Uniform derivative bound in the thin `eta` direction. -/
set_option maxHeartbeats 1000000 in
-- The nested exact-rational interval expression requires extra normalization time.
private theorem fReducedDerivEta_abs_le {t xi eta : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    |fReducedDerivEta t xi eta| ≤ (61 / 100 : ℝ) := by
  let xx := (brick.centers 0 : ℝ) + brick.slopes 0 * t + xi
  let yy := (brick.centers 1 : ℝ) + brick.slopes 1 * t +
    brick.yXiSlope * xi + eta
  let ll := (lamMid : ℝ) + t
  have hxx : (19739 / 100000 : ℝ) ≤ xx ∧ xx ≤ 19758 / 100000 := by
    dsimp [xx]
    norm_num [brick]
    constructor <;> linarith
  have hyy : (29995 / 100000 : ℝ) ≤ yy ∧ yy ≤ 30039 / 100000 := by
    dsimp [yy]
    norm_num [brick]
    constructor <;> linarith
  have hll : (102641 / 100000 : ℝ) ≤ ll ∧ ll ≤ 102651 / 100000 := by
    dsimp [ll]
    norm_num [lamMid, brick]
    constructor <;> linarith
  have hsx := c4_sin_x_range hxx
  have hcx := c4_cos_x_range hxx
  have hsy := c4_sin_y_range hyy
  have hcy := c4_cos_y_range hyy
  let exx : CertificateExpr := .atom xx
    ⟨19739 / 100000, 19758 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hxx)
  let eyy : CertificateExpr := .atom yy
    ⟨29995 / 100000, 30039 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hyy)
  let ell : CertificateExpr := .atom ll
    ⟨102641 / 100000, 102651 / 100000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hll)
  let esx : CertificateExpr := .atom (sin xx)
    ⟨196110 / 1000000, 196297 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsx)
  let ecx : CertificateExpr := .atom (cos xx)
    ⟨980544 / 1000000, 980582 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcx)
  let esy : CertificateExpr := .atom (sin yy)
    ⟨295472 / 1000000, 295893 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hsy)
  let ecy : CertificateExpr := .atom (cos yy)
    ⟨955221 / 1000000, 955352 / 1000000, by norm_num⟩
      (by simpa [LeanSuffixReflective.QInterval.RealContains] using hcy)
  let ep : CertificateExpr := .atom π
    ⟨3141592 / 1000000, 3141593 / 1000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d6]
        · norm_num at ⊢
          linarith [Real.pi_lt_d6])
  let ebb : CertificateExpr :=
    .add (.add (.mul ell eyy) (.mul (.rational (1 / 2)) ep)) (.neg exx)
  let ed : CertificateExpr :=
    .add
      (.add (.mul ecx ecy) (.neg (.mul (.mul esx ecy) ebb)))
      (.neg (.mul (.mul esx esy) ell))
  have he := CertificateExpr.sound ed
  have hv : ed.value = fReducedDerivEta t xi eta := by
    simp [ed, ebb, ep, exx, eyy, ell, esx, ecx, esy, ecy,
      CertificateExpr.value, fReducedDerivEta,
      MiddleFaceAssembly.FResidual.derivEta, xx, yy, ll]
    ring
  rw [hv] at he
  rw [abs_le]
  norm_num [ed, ebb, ep, exx, eyy, ell, esx, ecx, esy, ecy,
    CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point] at he ⊢
  constructor <;> linarith [he.1, he.2]

/- Exact-rational enclosure data for the two reusable `F` derivative bounds
on the complete brick. -/
private theorem fReduced_derivativeBounds :
    MiddleFaceAssembly.FResidual.DerivativeBounds brick := by
  intro t xi eta ht hxi heta
  exact ⟨fReducedDerivT_abs_le ht hxi,
    fReducedDerivEta_abs_le ht hxi heta⟩

/-- On the lower `xi` face, `F` is uniformly positive with exact strict
margin `88 · 10⁻⁹` over the complete B0064 brick. -/
theorem F_xi_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 0 = -radiiReal 0 →
      (88 / 1000000000 : ℝ) < F (pointOf t z) := by
  intro t z ht hz hxiFace
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have heta := hz 1
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at heta
  have hxi : z 0 = -(1 / 100000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hxiFace
    exact hxiFace
  change (88 / 1000000000 : ℝ) < fReduced t (z 0) (z 1)
  rw [hxi]
  exact MiddleFaceAssembly.FResidual.low_face_margin brick
    fReduced_derivativeBounds fReduced_low_anchor ht' heta

/-- On the upper `xi` face, `F` is uniformly negative with exact strict
margin `86 · 10⁻⁹` over the complete B0064 brick. -/
theorem F_xi_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 0 = radiiReal 0 →
      F (pointOf t z) < -(86 / 1000000000 : ℝ) := by
  intro t z ht hz hxiFace
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have heta := hz 1
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at heta
  have hxi : z 0 = (1 / 100000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hxiFace
    exact hxiFace
  change fReduced t (z 0) (z 1) < -(86 / 1000000000 : ℝ)
  rw [hxi]
  exact MiddleFaceAssembly.FResidual.high_face_margin brick
    fReduced_derivativeBounds fReduced_high_anchor ht' heta


/-- Exact origin certificate for the correlated `C3` residual. -/
private theorem c3Reduced_origin_abs_lt :
    |c3Reduced 0 0 0| < (1 / 25000000 : ℝ) := by
  have hwlo := (cosTaylor26Interval_sound (brick.centers 2)).1
  have hwhi := (cosTaylor26Interval_sound (brick.centers 2)).2
  have hvlo := (cosTaylor26Interval_sound (brick.centers 3)).1
  have hvhi := (cosTaylor26Interval_sound (brick.centers 3)).2
  norm_num [c3Reduced, MiddleFaceAssembly.C3Residual.reduced, brick, lamMid,
    Matrix.cons_val_two, Matrix.cons_val_three, cosTaylor26Interval, cosTaylor26,
    Finset.sum_range_succ, Nat.factorial] at hwlo hwhi hvlo hvhi ⊢
  rw [abs_lt]
  constructor <;> nlinarith

/-- Exact-rational derivative enclosures used by the shared `C3` face lane. -/
private theorem c3Reduced_derivativeBounds :
    MiddleFaceAssembly.C3Residual.DerivativeBounds brick := by
  intro t rho sigma ht hrho hsigma
  constructor
  · have hwArg :
        (45427 / 100000 : ℝ) ≤
            (brick.centers 2 : ℝ) + brick.slopes 2 * t ∧
          (brick.centers 2 : ℝ) + brick.slopes 2 * t ≤
            45480 / 100000 := by
      norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
      constructor <;> linarith
    have hvArg :
        (50441 / 100000 : ℝ) ≤
            (brick.centers 3 : ℝ) + brick.slopes 3 * t ∧
          (brick.centers 3 : ℝ) + brick.slopes 3 * t ≤
            50506 / 100000 := by
      norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
      constructor <;> linarith
    have hsw := c3_sin_w_range hwArg
    have hsv := c3_sin_v_range hvArg
    have hcv := c3_cos_v_range hvArg
    have hlamLo : (102641 / 100000 : ℝ) ≤ (lamMid : ℝ) + t := by
      norm_num [lamMid, brick]
      linarith
    have hlamHi : (lamMid : ℝ) + t ≤ (102651 / 100000 : ℝ) := by
      norm_num [lamMid, brick]
      linarith
    have hprodLo :
        (102641 / 100000 : ℝ) * (483291 / 1000000 : ℝ) ≤
          ((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t) :=
      mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
    have hprodHi :
        ((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t) ≤
          (102651 / 100000 : ℝ) * (483860 / 1000000 : ℝ) :=
      mul_le_mul hlamHi hsv.2 (by linarith) (by norm_num)
    rw [abs_le]
    norm_num [c3ReducedDerivT, MiddleFaceAssembly.C3Residual.derivT,
      brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
      at hsw hsv hcv hprodLo hprodHi ⊢
    constructor <;> linarith
  constructor
  · have hwArg :
        (45427 / 100000 : ℝ) ≤
            (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho ∧
          (brick.centers 2 : ℝ) + brick.slopes 2 * t + rho ≤
            45480 / 100000 := by
      norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
      constructor <;> linarith
    have hvArg :
        (50441 / 100000 : ℝ) ≤
            (brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho ∧
          (brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho ≤ 50506 / 100000 := by
      norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
      constructor <;> linarith
    have hsw := c3_sin_w_range hwArg
    have hsv := c3_sin_v_range hvArg
    have hlamLo : (102641 / 100000 : ℝ) ≤ (lamMid : ℝ) + t := by
      norm_num [lamMid, brick]
      linarith
    have hlamHi : (lamMid : ℝ) + t ≤ (102651 / 100000 : ℝ) := by
      norm_num [lamMid, brick]
      linarith
    have hprodLo :
        (102641 / 100000 : ℝ) * (483291 / 1000000 : ℝ) ≤
          ((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho) :=
      mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
    have hprodHi :
        ((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho) ≤
          (102651 / 100000 : ℝ) * (483860 / 1000000 : ℝ) :=
      mul_le_mul hlamHi hsv.2 (by linarith) (by norm_num)
    rw [abs_le]
    norm_num [c3ReducedDerivRho, MiddleFaceAssembly.C3Residual.derivRho,
      brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
      at hsw hsv hprodLo hprodHi ⊢
    constructor <;> linarith
  · have hvArg :
        (50441 / 100000 : ℝ) ≤
            (brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho + sigma ∧
          (brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho + sigma ≤ 50506 / 100000 := by
      norm_num [brick, Matrix.cons_val_two, Matrix.cons_val_three]
      constructor <;> linarith
    have hsv := c3_sin_v_range hvArg
    have hlamLo : (102641 / 100000 : ℝ) ≤ (lamMid : ℝ) + t := by
      norm_num [lamMid, brick]
      linarith
    have hprodLo :
        (102641 / 100000 : ℝ) * (483291 / 1000000 : ℝ) ≤
          ((lamMid : ℝ) + t) *
            sin ((brick.centers 3 : ℝ) + brick.slopes 3 * t +
              brick.vRhoSlope * rho + sigma) :=
      mul_le_mul hlamLo hsv.1 (by norm_num) (by linarith)
    norm_num [c3ReducedDerivSigma, MiddleFaceAssembly.C3Residual.derivSigma,
      brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
      at hprodLo ⊢
    linarith

/-- The lower `sigma` face has the required `C3` sign with the strict exact
rational margin `10⁻⁹`. -/
theorem C3_sigma_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 3 = -radiiReal 3 →
      C3 (pointOf t z) < -(1 / 1000000000 : ℝ) := by
  intro t z ht hz hsigma
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hrho := hz 2
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hrho
  have hsigma' : z 3 = -(1 / 1000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at hsigma
    exact hsigma
  change c3Reduced t (z 2) (z 3) < -(1 / 1000000000 : ℝ)
  rw [hsigma']
  exact MiddleFaceAssembly.C3Residual.low_face_margin brick
    c3Reduced_derivativeBounds c3Reduced_origin_abs_lt ht' hrho

/-- The upper `sigma` face has the required `C3` sign with the strict exact
rational margin `10⁻⁹`. -/
theorem C3_sigma_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 3 = radiiReal 3 →
      (1 / 1000000000 : ℝ) < C3 (pointOf t z) := by
  intro t z ht hz hsigma
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hrho := hz 2
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hrho
  have hsigma' : z 3 = (1 / 1000000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three] at hsigma
    exact hsigma
  change (1 / 1000000000 : ℝ) < c3Reduced t (z 2) (z 3)
  rw [hsigma']
  exact MiddleFaceAssembly.C3Residual.high_face_margin brick
    c3Reduced_derivativeBounds c3Reduced_origin_abs_lt ht' hrho

set_option maxHeartbeats 1000000 in
-- Six exact degree-27/26 point enclosures require extra normalization time.
private theorem eReduced_origin_abs_lt :
    |eReduced 0 0 0 0 0| < (3 / 10000000 : ℝ) := by
  let xq : ℚ := brick.centers 0
  let yq : ℚ := brick.centers 1
  let wq : ℚ := brick.centers 2
  let vq : ℚ := brick.centers 3
  let sx : CertificateExpr :=
    .atom (sin (xq : ℝ)) (sinTaylor27Interval xq)
      (sinTaylor27Interval_sound xq)
  let cx : CertificateExpr :=
    .atom (cos (xq : ℝ)) (cosTaylor26Interval xq)
      (cosTaylor26Interval_sound xq)
  let sy : CertificateExpr :=
    .atom (sin (yq : ℝ)) (sinTaylor27Interval yq)
      (sinTaylor27Interval_sound yq)
  let sw : CertificateExpr :=
    .atom (sin (wq : ℝ)) (sinTaylor27Interval wq)
      (sinTaylor27Interval_sound wq)
  let cw : CertificateExpr :=
    .atom (cos (wq : ℝ)) (cosTaylor26Interval wq)
      (cosTaylor26Interval_sound wq)
  let sv : CertificateExpr :=
    .atom (sin (vq : ℝ)) (sinTaylor27Interval vq)
      (sinTaylor27Interval_sound vq)
  let p : CertificateExpr :=
    .atom π ⟨314159265358979323846 / 100000000000000000000,
      314159265358979323847 / 100000000000000000000, by norm_num⟩
      (by
        constructor
        · norm_num at ⊢
          linarith [Real.pi_gt_d20]
        · norm_num at ⊢
          linarith [Real.pi_lt_d20])
  let n4 : CertificateExpr :=
    .add
      (.add
        (.add (.rational (lamMid * yq))
          (.mul (.rational (1 / 2)) p))
        (.neg (.rational xq)))
      (.mul cx (.add sy (.neg sx)))
  let n3 : CertificateExpr :=
    .add
      (.add
        (.add (.rational (lamMid * vq)) p)
        (.neg (.rational wq)))
      (.mul (.add cw (.rational 2)) (.add sv (.neg sw)))
  let e : CertificateExpr :=
    .add
      (.mul (.mul (.rational 2) (.mul cx cx)) n3)
      (.neg
        (.mul
          (.mul (.add (.rational 1) cw) (.add (.rational 1) cw))
          n4))
  have he := CertificateExpr.sound e
  have hv : e.value = eReduced 0 0 0 0 0 := by
    norm_num [e, n3, n4, p, sx, cx, sy, sw, cw, sv, xq, yq, wq, vq,
      CertificateExpr.value, MiddleFaceAssembly.EResidual.reduced, brick,
      lamMid, Matrix.cons_val_two, Matrix.cons_val_three]
    ring
  rw [hv] at he
  rw [abs_lt]
  norm_num [e, n3, n4, p, sx, cx, sy, sw, cw, sv, xq, yq, wq, vq,
    CertificateExpr.enclosure, QInterval.mul,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, sinTaylor27Interval, sinTaylor27,
    cosTaylor26Interval, cosTaylor26, Finset.sum_range_succ, Nat.factorial,
    brick, lamMid, Matrix.cons_val_two, Matrix.cons_val_three] at he ⊢
  constructor <;> linarith [he.1, he.2]

theorem E_rho_low_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 2 = -radiiReal 2 →
      E (pointOf t z) < -(14 / 1000000000 : ℝ) := by
  intro t z ht hz hrhoFace
  have hxi := hz 0
  have heta := hz 1
  have hsigma := hz 3
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi heta hsigma
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hrho : z 2 = -(1 / 100000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hrhoFace
    exact hrhoFace
  have h := low_face_margin brick eReduced_deriv_bounds
    eReduced_origin_abs_lt ht' hxi heta hsigma
  rw [show E (pointOf t z) = eReduced t (z 0) (z 1) (z 2) (z 3) by rfl,
    hrho]
  exact h

theorem E_rho_high_face_margin :
    ∀ t z, tInterval.RealContains t → InSymmetricBox radiiReal z →
      z 2 = radiiReal 2 →
      (14 / 1000000000 : ℝ) < E (pointOf t z) := by
  intro t z ht hz hrhoFace
  have hxi := hz 0
  have heta := hz 1
  have hsigma := hz 3
  norm_num [InSymmetricBox, radiiReal, brick, Matrix.cons_val_two,
    Matrix.cons_val_three] at hxi heta hsigma
  have ht' : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000 := by
    norm_num [tInterval, tRadius, brick,
      LeanSuffixReflective.QInterval.RealContains] at ht
    exact ht
  have hrho : z 2 = (1 / 100000 : ℝ) := by
    norm_num [radiiReal, brick, Matrix.cons_val_two, Matrix.cons_val_three]
      at hrhoFace
    exact hrhoFace
  have h := high_face_margin brick eReduced_deriv_bounds
    eReduced_origin_abs_lt ht' hxi heta hsigma
  rw [show E (pointOf t z) = eReduced t (z 0) (z 1) (z 2) (z 3) by rfl,
    hrho]
  exact h

/-- Proof-producing checker instance for inventory brick `B0064`.

Every field is one strict semantic decision from the retained checker contract;
the rational margins are proved by the interval lemmas above rather than
trusted as serialized data. -/
theorem cellCertificate : MiddleFaceAssembly.CellCertificate brick where
  lambda_one_lt := by
    intro t ht
    change tInterval.RealContains t at ht
    change 1 < lam (pointOf t 0)
    have hlamCell : lamInterval.RealContains ((lamMid : ℝ) + t) := by
      apply lambda_iff_centered.mpr
      convert ht using 1 <;> ring
    simpa [lam, pointOf] using (lambda_in_retainedSuffix hlamCell).one_lt
  branches := by
    intro t z ht hz
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change
      let p := pointOf t z
      0 < x p ∧ x p < π / 4 ∧
      0 < y p ∧ y p < π / 4 ∧
      0 < w p ∧ w p < π / 4 ∧
      0 < v p ∧ v p < π / 4
    exact affine_branches t z ht hz
  F_xi_low_pos := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 0 = -radiiReal 0 at hface
    change 0 < F (pointOf t z)
    linarith [F_xi_low_face_margin t z ht hz hface]
  F_xi_high_neg := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 0 = radiiReal 0 at hface
    change F (pointOf t z) < 0
    linarith [F_xi_high_face_margin t z ht hz hface]
  C4_eta_low_neg := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 1 = -radiiReal 1 at hface
    change C4 (pointOf t z) < 0
    linarith [C4_eta_low_face_margin t z ht hz hface]
  C4_eta_high_pos := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 1 = radiiReal 1 at hface
    change 0 < C4 (pointOf t z)
    linarith [C4_eta_high_face_margin t z ht hz hface]
  E_rho_low_neg := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 2 = -radiiReal 2 at hface
    change E (pointOf t z) < 0
    linarith [E_rho_low_face_margin t z ht hz hface]
  E_rho_high_pos := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 2 = radiiReal 2 at hface
    change 0 < E (pointOf t z)
    linarith [E_rho_high_face_margin t z ht hz hface]
  C3_sigma_low_neg := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 3 = -radiiReal 3 at hface
    change C3 (pointOf t z) < 0
    linarith [C3_sigma_low_face_margin t z ht hz hface]
  C3_sigma_high_pos := by
    intro t z ht hz hface
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change z 3 = radiiReal 3 at hface
    change 0 < C3 (pointOf t z)
    linarith [C3_sigma_high_face_margin t z ht hz hface]
  K3_neg := by
    intro t z ht hz
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change K3 (pointOf t z) < 0
    exact descendingK3 t z ht hz
  G_neg := by
    intro t z ht hz
    change tInterval.RealContains t at ht
    change InSymmetricBox radiiReal z at hz
    change G (pointOf t z) < 0
    exact (gap_upper t z ht hz).trans (by norm_num)

/-- Sound projection of the B0064 checker instance into the generic
root/projection assembly contract. -/
theorem checkedConditions : MiddleFaceAssembly.Conditions brick :=
  MiddleFaceAssembly.CellCertificate.sound cellCertificate

/-- Every projected type-(iv) height in B0064 has an equal-area regular
 type-(iii) competitor with strictly smaller weighted perimeter. -/
theorem projected_typeFour_scalarImprovement_exists
    {t h₄ : ℝ}
    (ht : (MiddleFaceAssembly.tInterval brick).RealContains t)
    (hh₄ : h₄ ∈ MiddleFaceAssembly.Model.typeFourCellInterval brick t) :
    ∃ h₃,
      h₃ ∈ MiddleFaceAssembly.Model.typeThreeCellInterval brick t ∧
      h₃ ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea
          ((MiddleFaceAssembly.lamMid brick : ℝ) + t) h₃ =
        LeanSuffixAnalytic.typeFourArea
          ((MiddleFaceAssembly.lamMid brick : ℝ) + t) h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter
          ((MiddleFaceAssembly.lamMid brick : ℝ) + t) h₃ <
        LeanSuffixAnalytic.typeFourPerimeter
          ((MiddleFaceAssembly.lamMid brick : ℝ) + t) h₄ :=
  MiddleFaceAssembly.Conditions.projected_typeFour_scalarImprovement_exists
    checkedConditions ht hh₄

/-- Candidate-facing conclusion for B0064.  No stationarity hypothesis is
 required for candidates in the exact projected slice. -/
theorem projectedCandidate_not_isWeightedPerimeterMinimizer
    {t lam0 : ℝ}
    (ht : (MiddleFaceAssembly.tInterval brick).RealContains t)
    (hlam : (MiddleFaceAssembly.lamMid brick : ℝ) + t = lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hprojected :
      candidate.h ∈ MiddleFaceAssembly.Model.typeFourCellInterval brick t) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  MiddleFaceAssembly.Conditions.projectedCandidate_not_isWeightedPerimeterMinimizer
    checkedConditions ht hlam candidate hcandidate hprojected


/-- Complete B0064 candidate-facing conclusion.  The checked stationary pair
promotes to every modeled type-(iv) curvature at the same density, so neither
candidate stationarity nor membership in the brick's curvature projection is
an input. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    {lam0 : ℝ} (hlam : lamInterval.RealContains lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  have ht0 : tInterval.RealContains (lam0 - (lamMid : ℝ)) :=
    lambda_iff_centered.mp hlam
  have ht : (MiddleFaceAssembly.tInterval brick).RealContains
      (lam0 - (MiddleFaceAssembly.lamMid brick : ℝ)) := by
    change tInterval.RealContains (lam0 - (lamMid : ℝ))
    exact ht0
  have hcenter :
      (MiddleFaceAssembly.lamMid brick : ℝ) +
        (lam0 - (MiddleFaceAssembly.lamMid brick : ℝ)) = lam0 := by
    ring
  exact
    MiddleFaceAssembly.Conditions.candidate_not_isWeightedPerimeterMinimizer
      checkedConditions ht hcenter candidate hcandidate
end MiddleFaceCell64
