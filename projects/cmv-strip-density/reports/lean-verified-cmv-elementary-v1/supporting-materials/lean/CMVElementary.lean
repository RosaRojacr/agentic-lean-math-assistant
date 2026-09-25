/-
Copyright (c) 2026 author. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import GreatestLevelRoot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Corrected elementary CMV comparison: scalar contract

`auxiliary_claims` and `same_curvature_claims` prove the complete J/H and
same-curvature ingredient records. `scalar_identification_claims` identifies the
frozen formulas, and `three_arc_calculus_claims` transports their calculus.
The two printed Theorem 1 statements must read perimeter minus perimeter, not
area minus perimeter. `elementary_route` constructs the complete greatest-root
record, and `scalar_comparison` proves the strict quantitative scalar margin.

All formulas are total real functions. Their asserted domains below retain every
positive parameter and the scalar endpoint one. `jprime` is an explicit continuous
extension, not a claim about differentiating square roots at endpoints.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CMVElementary

def B (lam z : ℝ) : ℝ :=
  lam * Real.arccos (z / lam) + Real.arcsin z

def D (lam z : ℝ) : ℝ :=
  Real.sqrt (1 - z ^ 2 / lam ^ 2) - Real.sqrt (1 - z ^ 2)

def S (lam z : ℝ) : ℝ := B lam z - z * D lam z

def gamma (lam : ℝ) : ℝ :=
  lam * Real.arccos (1 / lam) - Real.sqrt (1 - lam ^ (-2 : ℤ))

def A3 (lam t : ℝ) : ℝ :=
  let q := 2 * t - 1
  (B lam q + Real.pi / 2 + (2 * t + 1) * D lam q) / t ^ 2

def P3 (lam t : ℝ) : ℝ :=
  let q := 2 * t - 1
  2 * (B lam q + Real.pi / 2 + D lam q) / t

def A4 (lam t : ℝ) : ℝ := 2 * (B lam t + t * D lam t) / t ^ 2

def P4 (lam t : ℝ) : ℝ := 4 * B lam t / t

def J (lam u : ℝ) : ℝ := 2 * S lam u - S lam (2 * u - 1) - Real.pi / 2

def jprime (lam u : ℝ) : ℝ := 4 * (D lam (2 * u - 1) - D lam u)

def H (lam u : ℝ) : ℝ := J lam u - u * jprime lam u

def Z (lam h epsilon : ℝ) : Set ℝ :=
  {t ∈ Icc epsilon h | A3 lam t = A4 lam h}

def Q (lam h t : ℝ) : ℝ := P3 lam t + t * (A4 lam h - A3 lam t)

/-- Exact contract type of `CMVElementary.scalar_comparison`. -/
def ScalarStatement : Prop :=
  ∀ lam : ℝ, 1 < lam →
    0 < gamma lam ∧
    ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ r : ℝ, 0 < r ∧ r < h ∧ A3 lam r = A4 lam h ∧
        gamma lam / h < P4 lam h - P3 lam r ∧ 0 < gamma lam / h

/-- Mandatory auxiliary-function claims. These are conclusions to prove from
`1 < lam`, never extra hypotheses of either comparison theorem. -/
structure AuxiliaryClaims (lam : ℝ) : Prop where
  d_continuous : ContinuousOn (D lam) (Icc (-1) 1)
  d_even : ∀ z ∈ Icc (-1) 1, D lam (-z) = D lam z
  d_nonneg : ∀ z ∈ Icc (-1) 1, 0 ≤ D lam z
  d_strictMono : StrictMonoOn (D lam) (Icc 0 1)
  s_deriv : ∀ z ∈ Ioo (-1) 1, HasDerivAt (S lam) (-2 * D lam z) z
  s_reflection : ∀ z ∈ Icc (-1) 1, S lam (-z) = lam * Real.pi - S lam z
  gamma_pos : 0 < gamma lam
  j_continuous : ContinuousOn (J lam) (Icc 0 1)
  jprime_continuous : ContinuousOn (jprime lam) (Icc 0 1)
  j_zero : J lam 0 = gamma lam
  j_one : J lam 1 = gamma lam
  j_deriv : ∀ u ∈ Ioo 0 1, HasDerivAt (J lam) (jprime lam u) u
  j_lower : ∀ u ∈ Ioc 0 1, gamma lam ≤ J lam u
  h_lower : ∀ u ∈ Ioc 0 1, gamma lam ≤ H lam u
  jprime_pos : ∀ u ∈ Ioo 0 (1 / 3), 0 < jprime lam u
  jprime_third : jprime lam (1 / 3) = 0
  jprime_neg : ∀ u ∈ Ioo (1 / 3) 1, jprime lam u < 0
  h_ge_j : ∀ u ∈ Icc (1 / 3) 1, J lam u ≤ H lam u
  d_differentiable : DifferentiableOn ℝ (D lam) (Ioo (-1) 1)
  jprime_deriv : ∀ u ∈ Ioo 0 (1 / 3), HasDerivAt (jprime lam)
    (8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u) u
  jprime_deriv_neg : ∀ u ∈ Ioo 0 (1 / 3),
    8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u < 0
  h_deriv : ∀ u ∈ Ioo 0 (1 / 3), HasDerivAt (H lam)
    (-u * (8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u)) u
  h_deriv_pos : ∀ u ∈ Ioo 0 (1 / 3), 0 < deriv (H lam) u
  h_limit_zero : Tendsto (H lam) (𝓝[>] (0 : ℝ)) (𝓝 (gamma lam))

structure SameCurvatureClaims (lam : ℝ) : Prop where
  support_identity : ∀ h ∈ Ioc 0 1,
    h * ((P4 lam h - h * A4 lam h) - (P3 lam h - h * A3 lam h)) = J lam h
  area_identity : ∀ h ∈ Ioc 0 1,
    h ^ 2 * (A4 lam h - A3 lam h) = J lam h - h * jprime lam h
  area_gap : ∀ h ∈ Ioc 0 1,
    gamma lam / h ^ 2 ≤ A4 lam h - A3 lam h ∧ 0 < gamma lam / h ^ 2
  support_gap : ∀ h ∈ Ioc 0 1,
    gamma lam / h ≤ (P4 lam h - h * A4 lam h) - (P3 lam h - h * A3 lam h) ∧
      0 < gamma lam / h

structure ThreeArcCalculusClaims (lam : ℝ) : Prop where
  area_continuous : ContinuousOn (A3 lam) (Ioc 0 1)
  perimeter_continuous : ContinuousOn (P3 lam) (Ioc 0 1)
  area_differentiable : DifferentiableOn ℝ (A3 lam) (Ioo 0 1)
  perimeter_differentiable : DifferentiableOn ℝ (P3 lam) (Ioo 0 1)
  area_limit_zero : Tendsto (A3 lam) (𝓝[>] (0 : ℝ)) atTop
  variational_identity : ∀ t ∈ Ioo 0 1,
    HasDerivAt (P3 lam) (t * deriv (A3 lam) t) t

/-- The selected root and its strict barrier; no uniqueness or global area
monotonicity is required. Differentiation stays inside `(r,h)`, even for `h=1`. -/
structure GreatestRootClaims (lam h epsilon r : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  epsilon_lt_r : epsilon < r
  r_lt_h : r < h
  epsilon_above : A4 lam h < A3 lam epsilon
  level_nonempty : (Z lam h epsilon).Nonempty
  level_compact : IsCompact (Z lam h epsilon)
  greatest : IsGreatest (Z lam h epsilon) r
  equal_area : A3 lam r = A4 lam h
  barrier : ∀ t ∈ Ioc r h, A3 lam t < A4 lam h
  q_continuous : ContinuousOn (Q lam h) (Icc r h)
  q_deriv : ∀ t ∈ Ioo r h, HasDerivAt (Q lam h) (A4 lam h - A3 lam t) t
  q_deriv_pos : ∀ t ∈ Ioo r h, 0 < A4 lam h - A3 lam t
  q_strict : Q lam h r < Q lam h h

/-- Required identification when reusing the frozen scalar library. -/
structure ScalarIdentificationClaims (lam : ℝ) : Prop where
  sqrt_normalization : ∀ z ∈ Icc (-1) 1,
    Real.sqrt (lam ^ 2 - z ^ 2) / lam = Real.sqrt (1 - z ^ 2 / lam ^ 2)
  delta_three : ∀ t ∈ Ioc 0 1,
    LeanSuffixAnalytic.typeThreeDelta lam t = D lam (2 * t - 1)
  delta_four : ∀ t ∈ Ioc 0 1, LeanSuffixAnalytic.typeFourDelta lam t = D lam t
  area_three : ∀ t ∈ Ioc 0 1, LeanSuffixAnalytic.typeThreeArea lam t = A3 lam t
  perimeter_three : ∀ t ∈ Ioc 0 1,
    LeanSuffixAnalytic.typeThreePerimeter lam t = P3 lam t
  area_four : ∀ t ∈ Ioc 0 1, LeanSuffixAnalytic.typeFourArea lam t = A4 lam t
  perimeter_four : ∀ t ∈ Ioc 0 1, LeanSuffixAnalytic.typeFourPerimeter lam t = P4 lam t

/-- Proof-route obligations, not an assumption allowing either root to bypass
its elementary argument. The retained dependency audit inspects proof terms. -/
structure ElementaryRoute (lam : ℝ) : Prop where
  auxiliary : AuxiliaryClaims lam
  same_curvature : SameCurvatureClaims lam
  three_arc_calculus : ThreeArcCalculusClaims lam
  scalar_identification : ScalarIdentificationClaims lam
  greatest_root : ∀ h ∈ Ioc 0 1, ∃ epsilon r : ℝ, GreatestRootClaims lam h epsilon r

namespace DerivativePilot

/-- Positive-lambda normalization holds even outside the geometric domain. -/
theorem sqrt_normalization {lam : ℝ} (hlam : 0 < lam) (z : ℝ) :
    Real.sqrt (lam ^ 2 - z ^ 2) / lam = Real.sqrt (1 - z ^ 2 / lam ^ 2) := by
  have heq : 1 - z ^ 2 / lam ^ 2 = (lam ^ 2 - z ^ 2) / lam ^ 2 := by
    field_simp
  rw [heq, Real.sqrt_div' _ (sq_nonneg lam), Real.sqrt_sq_eq_abs, abs_of_pos hlam]

theorem D_normalization {lam : ℝ} (hlam : 0 < lam) :
    D lam = fun z => Real.sqrt (lam ^ 2 - z ^ 2) / lam - Real.sqrt (1 - z ^ 2) := by
  funext z
  rw [D, sqrt_normalization hlam]

/-- Every radical and denominator used in the interior derivative is positive. -/
theorem radical_denominators {lam z : ℝ} (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    0 < 1 - z ^ 2 ∧ 0 < lam ^ 2 - z ^ 2 ∧
    0 < Real.sqrt (1 - z ^ 2) ∧
    0 < lam * Real.sqrt (lam ^ 2 - z ^ 2) := by
  have hl : 0 < lam := by linarith
  have hi : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have ho : 0 < lam ^ 2 - z ^ 2 := by nlinarith
  exact ⟨hi, ho, Real.sqrt_pos.2 hi, mul_pos hl (Real.sqrt_pos.2 ho)⟩

/-- The exact derivative, valid for negative, zero, and positive interior arguments. -/
theorem hasDerivAt_D {lam z : ℝ} (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    HasDerivAt (D lam)
      (z * (1 / Real.sqrt (1 - z ^ 2) -
        1 / (lam * Real.sqrt (lam ^ 2 - z ^ 2)))) z := by
  have hl : 0 < lam := by linarith
  obtain ⟨hi, ho, hsi, hso⟩ := radical_denominators hlam hz
  have hsone : Real.sqrt (lam ^ 2 - z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ho)
  rw [D_normalization hl]
  have houter := ((((hasDerivAt_const z (lam ^ 2)).sub
    ((hasDerivAt_id z).pow 2)).sqrt (ne_of_gt ho)).div_const lam)
  have hinner := (((hasDerivAt_const z 1).sub
    ((hasDerivAt_id z).pow 2)).sqrt (ne_of_gt hi))
  simpa only [id_eq] using! (houter.sub hinner).congr_deriv (by
    norm_num [id_eq, Pi.sub_apply, Pi.pow_apply]
    field_simp [ne_of_gt hl, ne_of_gt hsi, hsone]
    ring)

theorem deriv_D {lam z : ℝ} (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    deriv (D lam) z = z * (1 / Real.sqrt (1 - z ^ 2) -
      1 / (lam * Real.sqrt (lam ^ 2 - z ^ 2))) :=
  (hasDerivAt_D hlam hz).deriv

/-- Strict positivity of the coefficient does not require z to be nonzero. -/
theorem derivative_coefficient_pos {lam z : ℝ}
    (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    0 < 1 / Real.sqrt (1 - z ^ 2) -
      1 / (lam * Real.sqrt (lam ^ 2 - z ^ 2)) := by
  obtain ⟨hi, ho, hsi, hso⟩ := radical_denominators hlam hz
  have hs : Real.sqrt (1 - z ^ 2) < Real.sqrt (lam ^ 2 - z ^ 2) :=
    Real.sqrt_lt_sqrt hi.le (by nlinarith)
  have hscale : Real.sqrt (lam ^ 2 - z ^ 2) <
      lam * Real.sqrt (lam ^ 2 - z ^ 2) := by
    nlinarith [Real.sqrt_pos.2 ho]
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hsi (hs.trans hscale))

theorem deriv_D_neg {lam z : ℝ} (hlam : 1 < lam)
    (hz : z ∈ Ioo (-1) 0) : deriv (D lam) z < 0 := by
  have hdomain : z ∈ Ioo (-1) 1 := ⟨hz.1, by linarith [hz.2]⟩
  rw [deriv_D hlam hdomain]
  exact mul_neg_of_neg_of_pos hz.2 (derivative_coefficient_pos hlam hdomain)

theorem deriv_D_pos {lam z : ℝ} (hlam : 1 < lam)
    (hz : z ∈ Ioo 0 1) : 0 < deriv (D lam) z := by
  have hdomain : z ∈ Ioo (-1) 1 := ⟨by linarith [hz.1], hz.2⟩
  rw [deriv_D hlam hdomain]
  exact mul_pos hz.1 (derivative_coefficient_pos hlam hdomain)

theorem D_differentiableOn {lam : ℝ} (hlam : 1 < lam) :
    DifferentiableOn ℝ (D lam) (Ioo (-1) 1) := by
  intro z hz
  exact (hasDerivAt_D hlam hz).differentiableAt.differentiableWithinAt

/-- On the lower third the two arguments have opposite strict signs. -/
theorem lower_third_signed_arguments {u : ℝ} (hu : u ∈ Ioo 0 (1 / 3)) :
    2 * u - 1 ∈ Ioo (-1) 0 ∧ u ∈ Ioo 0 1 := by
  constructor <;> constructor <;> linarith [hu.1, hu.2]

theorem jprime_deriv_neg {lam u : ℝ} (hlam : 1 < lam)
    (hu : u ∈ Ioo 0 (1 / 3)) :
    8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u < 0 := by
  obtain ⟨hq, hpos⟩ := lower_third_signed_arguments hu
  have hn := deriv_D_neg hlam hq
  have hp := deriv_D_pos hlam hpos
  linarith

/-- Chain rule; no derivative at u=0 or u=1 is asserted. -/
theorem hasDerivAt_jprime {lam u : ℝ} (hlam : 1 < lam)
    (hu : u ∈ Ioo 0 1) :
    HasDerivAt (jprime lam)
      (8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u) u := by
  have hq : 2 * u - 1 ∈ Ioo (-1) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hdq := (hasDerivAt_D hlam hq).differentiableAt.hasDerivAt
  have hdu := (hasDerivAt_D hlam ⟨by linarith [hu.1], hu.2⟩).differentiableAt.hasDerivAt
  have ha : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul 2).sub_const 1
  simpa only [jprime, Function.comp_def] using!
    (((hdq.comp u ha).sub hdu).const_mul 4).congr_deriv (by ring)

/-- Product-rule interface; the record constructor supplies `hasDerivAt_J`. -/
theorem hasDerivAt_H_of_J {lam u : ℝ} (hlam : 1 < lam)
    (hu : u ∈ Ioo 0 (1 / 3))
    (hJ : HasDerivAt (J lam) (jprime lam u) u) :
    HasDerivAt (H lam)
      (-u * (8 * deriv (D lam) (2 * u - 1) - 4 * deriv (D lam) u)) u := by
  have hdu := hasDerivAt_jprime hlam (lower_third_signed_arguments hu).2
  simpa only [H] using! (hJ.sub ((hasDerivAt_id u).mul hdu)).congr_deriv (by
    simp only [id_eq]
    ring)

theorem deriv_H_pos_of_J {lam u : ℝ} (hlam : 1 < lam)
    (hu : u ∈ Ioo 0 (1 / 3))
    (hJ : HasDerivAt (J lam) (jprime lam u) u) : 0 < deriv (H lam) u := by
  rw [(hasDerivAt_H_of_J hlam hu hJ).deriv]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hu.1) (jprime_deriv_neg hlam hu)

/-- Continuity, unlike differentiability, is valid at the radical endpoints. -/
theorem D_continuous (lam : ℝ) : Continuous (D lam) := by
  unfold D
  fun_prop

theorem jprime_continuous (lam : ℝ) : Continuous (jprime lam) := by
  unfold jprime
  exact ((D_continuous lam).comp (by fun_prop) |>.sub (D_continuous lam)).const_mul 4

theorem H_continuous (lam : ℝ) : Continuous (H lam) := by
  unfold H J S B jprime D
  fun_prop

theorem J_zero (lam : ℝ) : J lam 0 = gamma lam := by
  norm_num [J, S, B, D, gamma, zpow_neg, neg_div, Real.arccos_neg]
  ring

/-- This is a continuity limit, not a derivative at zero. -/
theorem H_limit_zero (lam : ℝ) :
    Tendsto (H lam) (𝓝[>] (0 : ℝ)) (𝓝 (gamma lam)) := by
  have heq : H lam 0 = gamma lam := by simpa [H] using J_zero lam
  rw [← heq]
  exact (H_continuous lam).continuousAt.continuousWithinAt

end DerivativePilot

namespace MonotoneTangent

/-- A decreasing specified derivative places the left endpoint below the tangent
at the right endpoint. Only continuity, not differentiability, is needed at zero.
The specified derivative need not itself be continuous or differentiable. -/
theorem endpoint_tangent
    {F g : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hcont : ContinuousOn F (Icc 0 u))
    (hderiv : ∀ t ∈ Ioo 0 u, HasDerivAt F (g t) t)
    (hanti : AntitoneOn g (Icc 0 u)) :
    F 0 ≤ F u - u * g u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F g hu hcont hderiv
  have hgc : g u ≤ g c :=
    hanti ⟨hc.1.le, hc.2.le⟩ ⟨hu.le, le_rfl⟩ hc.2.le
  have hbound : g u * u ≤ F u - F 0 := by
    apply (le_div_iff₀ hu).mp
    simpa only [sub_zero] using hgc.trans_eq hslope
  nlinarith

/-- The reflected expression is antitone by order alone: its first argument
falls and its second argument rises. Strict increase is more than sufficient. -/
theorem reflected_difference_antitone
    {d : ℝ → ℝ} (hmono : StrictMonoOn d (Icc 0 1)) :
    AntitoneOn (fun t : ℝ => 4 * (d (1 - 2 * t) - d t)) (Icc 0 (1 / 3)) := by
  intro x hx y hy hxy
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
  have hxr : 1 - 2 * x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hyr : 1 - 2 * y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hfirst := hmono.monotoneOn hyr hxr (by linarith : 1 - 2 * y ≤ 1 - 2 * x)
  have hsecond := hmono.monotoneOn hx01 hy01 hxy
  linarith

/-- Evenness identifies the negative-side argument with the reflected one.
No assertion about d' or d'' is involved, including at the endpoint -1. -/
theorem even_difference_antitone
    {d : ℝ → ℝ}
    (heven : ∀ z ∈ Icc (-1 : ℝ) 1, d (-z) = d z)
    (hmono : StrictMonoOn d (Icc 0 1)) :
    AntitoneOn (fun t : ℝ => 4 * (d (2 * t - 1) - d t)) (Icc 0 (1 / 3)) := by
  have hreflect (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1 / 3)) :
      d (2 * t - 1) = d (1 - 2 * t) := by
    have hz : 1 - 2 * t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [show 2 * t - 1 = -(1 - 2 * t) by ring]
    exact heven (1 - 2 * t) hz
  intro x hx y hy hxy
  change 4 * (d (2 * y - 1) - d y) ≤ 4 * (d (2 * x - 1) - d x)
  rw [hreflect x hx, hreflect y hy]
  exact reflected_difference_antitone hmono hx hy hxy

/-- Conditional CMV interface using only the two specified D properties. -/
theorem jprime_antitone_lower_third {lam : ℝ}
    (heven : ∀ z ∈ Icc (-1 : ℝ) 1, D lam (-z) = D lam z)
    (hmono : StrictMonoOn (D lam) (Icc 0 1)) :
    AntitoneOn (jprime lam) (Icc 0 (1 / 3)) :=
  even_difference_antitone heven hmono

/-- The actual CMV H bound on the closed lower third, conditional on five
independently required auxiliary properties, not on AuxiliaryClaims as a whole.
In particular this cannot use that record's h_lower field circularly. -/
theorem h_lower_third_of_monotone_tangent {lam : ℝ}
    (heven : ∀ z ∈ Icc (-1 : ℝ) 1, D lam (-z) = D lam z)
    (hmono : StrictMonoOn (D lam) (Icc 0 1))
    (hcont : ContinuousOn (J lam) (Icc 0 1))
    (hzero : J lam 0 = gamma lam)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (J lam) (jprime lam t) t)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 / 3)) :
    gamma lam ≤ H lam u := by
  have hsub : Icc (0 : ℝ) u ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2, hu.2]⟩
  have hsubthird : Icc (0 : ℝ) u ⊆ Icc 0 (1 / 3) := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hu.2⟩
  have htangent := endpoint_tangent hu.1 (hcont.mono hsub)
    (fun t ht => hderiv t ⟨ht.1, by linarith [ht.2, hu.2]⟩)
    ((jprime_antitone_lower_third heven hmono).mono hsubthird)
  simpa only [hzero, H] using htangent

end MonotoneTangent

 theorem D_even (lam z : ℝ) : D lam (-z) = D lam z := by
  simp [D]

 theorem D_nonneg {lam : ℝ} (hlam : 1 < lam) (z : ℝ) : 0 ≤ D lam z := by
  unfold D
  apply sub_nonneg.mpr
  apply Real.sqrt_le_sqrt
  have hsq : 1 ≤ lam ^ 2 := by nlinarith
  have hd : z ^ 2 / lam ^ 2 ≤ z ^ 2 := div_le_self (sq_nonneg z) hsq
  linarith

/-- Interior strict positivity plus endpoint continuity gives closed-interval
strict increase. No square-root derivative at one is used. -/
 theorem D_strictMono {lam : ℝ} (hlam : 1 < lam) :
    StrictMonoOn (D lam) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (DerivativePilot.D_continuous lam).continuousOn
  intro z hz
  exact DerivativePilot.deriv_D_pos hlam (by simpa only [interior_Icc] using hz)

 theorem S_reflection (lam z : ℝ) : S lam (-z) = lam * Real.pi - S lam z := by
  simp only [S, B, neg_div, Real.arccos_neg, Real.arcsin_neg, D_even]
  ring

 theorem hasDerivAt_B {lam z : ℝ} (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    HasDerivAt (B lam)
      (1 / Real.sqrt (1 - z ^ 2) - lam / Real.sqrt (lam ^ 2 - z ^ 2)) z := by
  have hl : 0 < lam := by linarith
  have hrlo : -1 < z / lam := (lt_div_iff₀ hl).mpr (by linarith [hz.1])
  have hrhi : z / lam < 1 := (div_lt_one hl).mpr (by linarith [hz.2])
  have hs : Real.sqrt (1 - (z / lam) ^ 2) = Real.sqrt (lam ^ 2 - z ^ 2) / lam := by
    simpa only [div_pow] using (DerivativePilot.sqrt_normalization hl z).symm
  have ho := (DerivativePilot.radical_denominators hlam hz).2.1
  have hc := (Real.hasDerivAt_arccos (ne_of_gt hrlo) (ne_of_lt hrhi)).comp z
    ((hasDerivAt_id z).div_const lam)
  have ha := Real.hasDerivAt_arcsin (ne_of_gt hz.1) (ne_of_lt hz.2)
  simpa only [B, Function.comp_def, id_eq] using!
    ((hc.const_mul lam).add ha).congr_deriv (by
      rw [hs]
      field_simp [ne_of_gt hl, ne_of_gt (Real.sqrt_pos.mpr ho)]
      ring)

 theorem hasDerivAt_S {lam z : ℝ} (hlam : 1 < lam) (hz : z ∈ Ioo (-1) 1) :
    HasDerivAt (S lam) (-2 * D lam z) z := by
  have hl : 0 < lam := by linarith
  obtain ⟨hi, ho, hsi, hso⟩ := DerivativePilot.radical_denominators hlam hz
  have hsout : Real.sqrt (lam ^ 2 - z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ho)
  have hraw := (hasDerivAt_B hlam hz).sub ((hasDerivAt_id z).mul (DerivativePilot.hasDerivAt_D hlam hz))
  simpa only [S] using! hraw.congr_deriv (by
    simp only [id_eq, one_mul]
    rw [DerivativePilot.D_normalization hl]
    dsimp
    field_simp [ne_of_gt hl, ne_of_gt hsi, hsout]
    nlinarith [Real.sq_sqrt hi.le, Real.sq_sqrt ho.le])

/-- With `alpha = arccos (1/lam) > 0`, use `sin alpha ≤ alpha < lam*alpha`. -/
 theorem gamma_pos {lam : ℝ} (hlam : 1 < lam) : 0 < gamma lam := by
  have hl : 0 < lam := by linarith
  have ha : 0 < Real.arccos (1 / lam) := Real.arccos_pos.mpr ((div_lt_one hl).mpr hlam)
  have hs := Real.sin_le ha.le
  rw [Real.sin_arccos] at hs
  have heq : lam ^ (-2 : ℤ) = (1 / lam) ^ 2 := by simp [zpow_neg]
  unfold gamma
  rw [heq]
  nlinarith

 theorem J_continuous (lam : ℝ) : Continuous (J lam) := by
  unfold J S B D
  fun_prop

 theorem J_one (lam : ℝ) : J lam 1 = gamma lam := by
  norm_num [J, S, B, D, gamma, zpow_neg]
  ring

 theorem hasDerivAt_J {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (J lam) (jprime lam u) u := by
  have hq : 2 * u - 1 ∈ Ioo (-1) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hu' : u ∈ Ioo (-1) 1 := ⟨by linarith [hu.1], hu.2⟩
  have ha : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul 2).sub_const 1
  simpa only [J, Function.comp_def] using!
    ((((hasDerivAt_S hlam hu').const_mul 2).sub ((hasDerivAt_S hlam hq).comp u ha)).sub_const
      (Real.pi / 2)).congr_deriv (by unfold jprime; ring)

 theorem D_abs (lam z : ℝ) : D lam |z| = D lam z := by
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz]
  · rw [abs_of_neg hz, D_even]

 theorem jprime_pos {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Ioo 0 (1 / 3)) :
    0 < jprime lam u := by
  have hdu : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, by linarith [hu.2]⟩
  have hdr : 1 - 2 * u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hd := D_strictMono hlam hdu hdr (by linarith [hu.2] : u < 1 - 2 * u)
  unfold jprime
  rw [show 2 * u - 1 = -(1 - 2 * u) by ring, D_even]
  linarith

 theorem jprime_third (lam : ℝ) : jprime lam (1 / 3) = 0 := by
  unfold jprime
  rw [show (2 * (1 / 3) - 1 : ℝ) = -(1 / 3) by norm_num, D_even]
  ring

 theorem jprime_neg {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Ioo (1 / 3) 1) :
    jprime lam u < 0 := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have ha : |2 * u - 1| < u := abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hd := D_strictMono hlam ⟨abs_nonneg _, ha.le.trans hu.2.le⟩ ⟨hu0, hu.2.le⟩ ha
  rw [D_abs] at hd
  unfold jprime
  linarith

 theorem H_ge_J {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Icc (1 / 3) 1) :
    J lam u ≤ H lam u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have ha : |2 * u - 1| ≤ u := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hd := (D_strictMono hlam).monotoneOn ⟨abs_nonneg _, ha.trans hu.2⟩ ⟨hu0, hu.2⟩ ha
  rw [D_abs] at hd
  have hj : jprime lam u ≤ 0 := by unfold jprime; linarith
  unfold H
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hu0 hj]

/-- J rises to one third and falls thereafter, with both endpoint values gamma. -/
 theorem J_lower {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Icc 0 1) :
    gamma lam ≤ J lam u := by
  by_cases hut : u ≤ 1 / 3
  · have hm : StrictMonoOn (J lam) (Icc 0 (1 / 3)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (J_continuous lam).continuousOn
      intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_J hlam ⟨ht.1, by linarith [ht.2]⟩).deriv]
      exact jprime_pos hlam ht
    simpa only [DerivativePilot.J_zero] using
      hm.monotoneOn (show (0 : ℝ) ∈ Icc 0 (1 / 3) by norm_num) ⟨hu.1, hut⟩ hu.1
  · have hm : StrictAntiOn (J lam) (Icc (1 / 3) 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (J_continuous lam).continuousOn
      intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_J hlam ⟨by linarith [ht.1], ht.2⟩).deriv]
      exact jprime_neg hlam ht
    simpa only [J_one] using
      hm.antitoneOn ⟨(not_le.mp hut).le, hu.2⟩ (show (1 : ℝ) ∈ Icc (1 / 3) 1 by norm_num) hu.2

/-- The closed lower third uses the selected decreasing-derivative tangent
argument. The upper interval uses `H ≥ J ≥ gamma`, including one. -/
 theorem H_lower {lam u : ℝ} (hlam : 1 < lam) (hu : u ∈ Icc 0 1) :
    gamma lam ≤ H lam u := by
  by_cases hut : u ≤ 1 / 3
  · exact MonotoneTangent.h_lower_third_of_monotone_tangent
      (fun z _ => D_even lam z) (D_strictMono hlam) (J_continuous lam).continuousOn
      (DerivativePilot.J_zero lam) (fun t ht => hasDerivAt_J hlam ht) ⟨hu.1, hut⟩
  · exact (J_lower hlam hu).trans (H_ge_J hlam ⟨(not_le.mp hut).le, hu.2⟩)

/-- Every auxiliary field follows from `1 < lam`, including the separate
lower-third derivative identities and the continuous limit at zero. -/
 theorem auxiliary_claims {lam : ℝ} (hlam : 1 < lam) : AuxiliaryClaims lam where
  d_continuous := (DerivativePilot.D_continuous lam).continuousOn
  d_even := fun z _ => D_even lam z
  d_nonneg := fun z _ => D_nonneg hlam z
  d_strictMono := D_strictMono hlam
  s_deriv := fun _ hz => hasDerivAt_S hlam hz
  s_reflection := fun z _ => S_reflection lam z
  gamma_pos := gamma_pos hlam
  j_continuous := (J_continuous lam).continuousOn
  jprime_continuous := (DerivativePilot.jprime_continuous lam).continuousOn
  j_zero := DerivativePilot.J_zero lam
  j_one := J_one lam
  j_deriv := fun _ hu => hasDerivAt_J hlam hu
  j_lower := fun _ hu => J_lower hlam ⟨hu.1.le, hu.2⟩
  h_lower := fun _ hu => H_lower hlam ⟨hu.1.le, hu.2⟩
  jprime_pos := fun _ hu => jprime_pos hlam hu
  jprime_third := jprime_third lam
  jprime_neg := fun _ hu => jprime_neg hlam hu
  h_ge_j := fun _ hu => H_ge_J hlam hu
  d_differentiable := DerivativePilot.D_differentiableOn hlam
  jprime_deriv := fun _ hu => DerivativePilot.hasDerivAt_jprime hlam
    (DerivativePilot.lower_third_signed_arguments hu).2
  jprime_deriv_neg := fun _ hu => DerivativePilot.jprime_deriv_neg hlam hu
  h_deriv := fun _ hu => DerivativePilot.hasDerivAt_H_of_J hlam hu
    (hasDerivAt_J hlam (DerivativePilot.lower_third_signed_arguments hu).2)
  h_deriv_pos := fun _ hu => DerivativePilot.deriv_H_pos_of_J hlam hu
    (hasDerivAt_J hlam (DerivativePilot.lower_third_signed_arguments hu).2)
  h_limit_zero := DerivativePilot.H_limit_zero lam

 theorem support_identity {lam h : ℝ} (hh : h ≠ 0) :
    h * ((P4 lam h - h * A4 lam h) - (P3 lam h - h * A3 lam h)) = J lam h := by
  unfold P4 A4 P3 A3 J S
  field_simp [hh]
  ring

 theorem area_identity {lam h : ℝ} (hh : h ≠ 0) :
    h ^ 2 * (A4 lam h - A3 lam h) = J lam h - h * jprime lam h := by
  unfold A4 A3 J S jprime
  field_simp [hh]
  ring

/-- Exact scalar identities and both positive quantitative gaps, including h=1. -/
 theorem same_curvature_claims {lam : ℝ} (hlam : 1 < lam) : SameCurvatureClaims lam where
  support_identity := fun _ hh => support_identity (ne_of_gt hh.1)
  area_identity := fun _ hh => area_identity (ne_of_gt hh.1)
  area_gap := by
    intro h hh
    constructor
    · apply (div_le_iff₀ (sq_pos_of_pos hh.1)).mpr
      rw [mul_comm, area_identity (ne_of_gt hh.1)]
      exact H_lower hlam ⟨hh.1.le, hh.2⟩
    · exact div_pos (gamma_pos hlam) (sq_pos_of_pos hh.1)
  support_gap := by
    intro h hh
    constructor
    · apply (div_le_iff₀ hh.1).mpr
      rw [mul_comm, support_identity (ne_of_gt hh.1)]
      exact J_lower hlam ⟨hh.1.le, hh.2⟩
    · exact div_pos (gamma_pos hlam) hh.1

/-- Identification with the frozen normalization, including the scalar endpoint one. -/
theorem scalar_identification_claims {lam : ℝ} (hlam : 1 < lam) :
    ScalarIdentificationClaims lam := by
  have hl : 0 < lam := lt_trans zero_lt_one hlam
  have hthree (t : ℝ) :
      LeanSuffixAnalytic.typeThreeDelta lam t = D lam (2 * t - 1) := by
    unfold LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape D
    rw [DerivativePilot.sqrt_normalization hl]
  have hfour (t : ℝ) : LeanSuffixAnalytic.typeFourDelta lam t = D lam t := by
    unfold LeanSuffixAnalytic.typeFourDelta D
    rw [DerivativePilot.sqrt_normalization hl]
  refine ⟨fun z _ => DerivativePilot.sqrt_normalization hl z,
    fun t _ => hthree t, fun t _ => hfour t, ?_, ?_, ?_, ?_⟩
  · intro t _
    unfold LeanSuffixAnalytic.typeThreeArea A3
    rw [hthree]
    unfold LeanSuffixAnalytic.typeThreeAngle LeanSuffixAnalytic.typeThreeShape B
    ring
  · intro t _
    unfold LeanSuffixAnalytic.typeThreePerimeter P3
    rw [hthree]
    rfl
  · intro t _
    unfold LeanSuffixAnalytic.typeFourArea A4
    rw [hfour]
    rfl
  · intro t _
    rfl

/-- The closed right endpoint uses continuity of radicals and inverse trig functions,
not differentiability there. In fact continuity holds at every nonzero parameter. -/
theorem A3_continuousAt {lam t : ℝ} (ht : t ≠ 0) : ContinuousAt (A3 lam) t := by
  unfold A3 B D
  fun_prop (disch := positivity)

theorem P3_continuousAt {lam t : ℝ} (ht : t ≠ 0) : ContinuousAt (P3 lam) t := by
  unfold P3 B D
  fun_prop (disch := positivity)

/-- Local equality on an open neighborhood is what transports an ordinary derivative. -/
theorem three_arc_eventuallyEq {lam t : ℝ} (hlam : 1 < lam) (ht : t ∈ Ioo 0 1) :
    A3 lam =ᶠ[𝓝 t] LeanSuffixAnalytic.typeThreeArea lam ∧
      P3 lam =ᶠ[𝓝 t] LeanSuffixAnalytic.typeThreePerimeter lam := by
  have hid := scalar_identification_claims hlam
  have hn : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds ht.1 ht.2
  constructor
  · filter_upwards [hn] with s hs
    exact (hid.area_three s ⟨hs.1, hs.2.le⟩).symm
  · filter_upwards [hn] with s hs
    exact (hid.perimeter_three s ⟨hs.1, hs.2.le⟩).symm

/-- Transport of the frozen variational theorem stays strictly inside `(0,1)`. -/
theorem three_arc_variational_hasDerivAt {lam t : ℝ}
    (hlam : 1 < lam) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (A3 lam) (deriv (A3 lam) t) t ∧
      HasDerivAt (P3 lam) (t * deriv (A3 lam) t) t := by
  obtain ⟨ha, hp⟩ := three_arc_eventuallyEq hlam ht
  obtain ⟨hda, hdp⟩ := LeanSuffixAnalytic.typeThree_variational_hasDerivAt hlam ht.1 ht.2
  rw [ha.deriv_eq]
  exact ⟨hda.congr_of_eventuallyEq ha, hdp.congr_of_eventuallyEq hp⟩

/-- Equality eventually to the right of zero suffices for the divergence transport. -/
theorem A3_tendsto_atRight_zero {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (A3 lam) (𝓝[>] (0 : ℝ)) atTop := by
  have hid := scalar_identification_claims hlam
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono inf_le_left
  have heq : A3 lam =ᶠ[𝓝[>] (0 : ℝ)] LeanSuffixAnalytic.typeThreeArea lam := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
    exact (hid.area_three t ⟨ht, ht1.le⟩).symm
  exact (LeanSuffixAnalytic.typeThreeArea_tendsto_atRight_zero hlam).congr' heq.symm

/-- All calculus claims from the frozen variational identity and zero-end limit.
Continuity includes one; differentiability is asserted only on the open interval. -/
theorem three_arc_calculus_claims {lam : ℝ} (hlam : 1 < lam) :
    ThreeArcCalculusClaims lam where
  area_continuous := fun _ ht => (A3_continuousAt (ne_of_gt ht.1)).continuousWithinAt
  perimeter_continuous := fun _ ht => (P3_continuousAt (ne_of_gt ht.1)).continuousWithinAt
  area_differentiable := fun _ ht =>
    (three_arc_variational_hasDerivAt hlam ht).1.differentiableAt.differentiableWithinAt
  perimeter_differentiable := fun _ ht =>
    (three_arc_variational_hasDerivAt hlam ht).2.differentiableAt.differentiableWithinAt
  area_limit_zero := A3_tendsto_atRight_zero hlam
  variational_identity := fun _ ht => (three_arc_variational_hasDerivAt hlam ht).2

/-- Divergence supplies the left endpoint; the retained greatest-level lemma
selects the final crossing. The same witness is used for every Q claim. -/
theorem greatest_root_claims {lam h : ℝ} (hlam : 1 < lam) (hh : h ∈ Ioc 0 1) :
    ∃ epsilon r : ℝ, GreatestRootClaims lam h epsilon r := by
  have hc := three_arc_calculus_claims hlam
  have hg := same_curvature_claims hlam
  have hlarge := hc.area_limit_zero.eventually_gt_atTop (A4 lam h)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < h :=
    (eventually_lt_nhds hh.1).filter_mono inf_le_left
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨epsilon, heAbove, heh, hepos⟩ :=
    (hlarge.and (hsmall.and hpositive)).exists
  have hesub : Icc epsilon h ⊆ Ioc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hepos.trans_le ht.1, ht.2.trans hh.2⟩
  have hA := hc.area_continuous.mono hesub
  have hhbelow : A3 lam h < A4 lam h := by
    obtain ⟨hgap, hpos⟩ := hg.area_gap h hh
    linarith
  obtain ⟨r, hr, hequal, hgreatest, hbarrier⟩ :=
    exists_greatest_level_root heh hA heAbove hhbelow
  have hrpos : 0 < r := hepos.trans hr.1
  have hrsub : Icc r h ⊆ Ioc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hrpos.trans_le ht.1, ht.2.trans hh.2⟩
  have hAr := hc.area_continuous.mono hrsub
  have hPr := hc.perimeter_continuous.mono hrsub
  have hvar : ∀ t ∈ Ioo r h, ∃ d : ℝ,
      HasDerivAt (A3 lam) d t ∧ HasDerivAt (P3 lam) (t * d) t := by
    intro t ht
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨hrpos.trans ht.1, ht.2.trans_le hh.2⟩
    exact ⟨deriv (A3 lam) t,
      (hc.area_differentiable t ht01).differentiableAt
        (isOpen_Ioo.mem_nhds ht01) |>.hasDerivAt,
      hc.variational_identity t ht01⟩
  refine ⟨epsilon, r, {
    epsilon_pos := hepos
    epsilon_lt_r := hr.1
    r_lt_h := hr.2
    epsilon_above := heAbove
    level_nonempty := ⟨r, hgreatest.1⟩
    level_compact := ?_
    greatest := hgreatest
    equal_area := hequal
    barrier := hbarrier
    q_continuous := hPr.add (continuousOn_id.mul (continuousOn_const.sub hAr))
    q_deriv := ?_
    q_deriv_pos := fun t ht => sub_pos.mpr (hbarrier t ⟨ht.1, ht.2.le⟩)
    q_strict := ?_ }⟩
  · exact isCompact_Icc.of_isClosed_subset
      (hA.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  · intro t ht
    obtain ⟨d, hAd, hPd⟩ := hvar t ht
    simpa only [Q, id_eq] using!
      (hPd.add ((hasDerivAt_id t).mul
        ((hasDerivAt_const t (A4 lam h)).sub hAd))).congr_deriv (by
          simp only [id_eq, Pi.sub_apply]
          ring)
  · have hstrict := strict_support_comparison hr.2 hAr hPr hequal
      (fun t ht => hbarrier t ⟨ht.1, ht.2.le⟩) hvar
    simpa only [Q, hequal, sub_self, mul_zero, add_zero] using hstrict

/-- The complete elementary route, including the greatest root and strict Q
comparison, follows from the density hypothesis alone. -/
theorem elementary_route : ∀ lam : ℝ, 1 < lam → ElementaryRoute lam := by
  intro lam hlam
  exact {
    auxiliary := auxiliary_claims hlam
    same_curvature := same_curvature_claims hlam
    three_arc_calculus := three_arc_calculus_claims hlam
    scalar_identification := scalar_identification_claims hlam
    greatest_root := fun _ hh => greatest_root_claims hlam hh }

/-- Corrected perimeter-minus-perimeter comparison. The Q improvement is strict
and the same-curvature support bound supplies the explicit gamma/h margin. -/
theorem scalar_comparison : ScalarStatement := by
  intro lam hlam
  have route := elementary_route lam hlam
  refine ⟨route.auxiliary.gamma_pos, ?_⟩
  intro h hhpos hh1
  obtain ⟨epsilon, r, root⟩ := route.greatest_root h ⟨hhpos, hh1⟩
  obtain ⟨hgap, hmargin⟩ := route.same_curvature.support_gap h ⟨hhpos, hh1⟩
  refine ⟨r, root.epsilon_pos.trans root.epsilon_lt_r, root.r_lt_h,
    root.equal_area, ?_, hmargin⟩
  have hstrict := root.q_strict
  simp only [Q, root.equal_area, sub_self, mul_zero, add_zero] at hstrict
  linarith

end CMVElementary
