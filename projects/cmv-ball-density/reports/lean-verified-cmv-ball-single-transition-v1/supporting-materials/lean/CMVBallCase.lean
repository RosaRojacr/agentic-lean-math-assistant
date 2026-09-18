import CMVBallDefinitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

noncomputable section

namespace CMVBallCase

/-- Finite type-(B) candidates: the zero-radius endpoint is retained, while
`beta = 0` is excluded because it is only an infinite-radius degeneration. -/
def BAdmissible (lam beta : ℝ) : Prop :=
  0 < beta ∧ beta ≤ Real.pi - Real.arccos lam

/-- Finite type-(C) orthogonal-ball candidates.  Both angular endpoints are
excluded degenerations. -/
def CAdmissible (beta : ℝ) : Prop :=
  0 < beta ∧ beta < Real.pi / 2

/-- On the audited type-(C) angle domain, the orthogonal-ball radius is
strictly positive. -/
lemma typeCRadius_pos {beta : ℝ} (hbeta : CAdmissible beta) :
    0 < typeCRadius beta := by
  rw [typeCRadius]
  exact one_div_pos.mpr
    (Real.tan_pos_of_pos_of_lt_pi_div_two hbeta.1 hbeta.2)

/-- The type-(C) angle has no hidden radius branch: its radius is strictly
decreasing throughout the complete admissible open interval. -/
lemma typeCRadius_strictAntiOn :
    StrictAntiOn typeCRadius (Set.Ioo 0 (Real.pi / 2)) := by
  intro beta hbeta beta' hbeta' hlt
  rw [typeCRadius]
  exact one_div_lt_one_div_of_lt
    (Real.tan_pos_of_pos_of_lt_pi_div_two hbeta.1 hbeta.2)
    (Real.strictMonoOn_tan
      ⟨by linarith [hbeta.1, Real.pi_pos], hbeta.2⟩
      ⟨by linarith [hbeta'.1, Real.pi_pos], hbeta'.2⟩ hlt)

/-- Equality of admissible type-(C) radii forces equality of their angle
parameters; this is the branch-uniqueness fact used by radius parametrizations. -/
lemma typeCRadius_injective_on_admissible :
    Set.InjOn typeCRadius {beta | CAdmissible beta} := by
  change Set.InjOn typeCRadius (Set.Ioo 0 (Real.pi / 2))
  exact typeCRadius_strictAntiOn.injOn
/-- Positivity of the Snell-law square-root coefficient. -/
lemma sqrt_one_sub_sq_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    0 < Real.sqrt (1 - lam ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith

lemma sq_sqrt_one_sub_sq {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Real.sqrt (1 - lam ^ 2) ^ 2 = 1 - lam ^ 2 :=
  Real.sq_sqrt (by nlinarith)

/-- The type-(B) parameter has positive sine on its complete finite domain. -/
lemma typeB_sin_pos {lam beta : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hbeta : BAdmissible lam beta) :
    0 < Real.sin beta := by
  apply Real.sin_pos_of_pos_of_lt_pi hbeta.1
  have hacos : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
  linarith [hbeta.2]

/-- The exterior arc's source sine is nonnegative, including the
zero-radius endpoint where its angle is `π`. -/
lemma typeBAlpha_sin_nonneg {lam beta : ℝ}
    (hbeta : BAdmissible lam beta) :
    0 ≤ Real.sin (typeBAlpha lam beta) := by
  rw [typeBAlpha]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact add_nonneg hbeta.1.le (Real.arccos_nonneg lam)
  · linarith [hbeta.2]

/-- Snell's law puts the type-(B) radius on a cotangent chart. -/
lemma typeBRadius_eq_add_sqrt_mul_cot {lam beta : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hbeta : BAdmissible lam beta) :
    typeBRadius lam beta =
      lam + Real.sqrt (1 - lam ^ 2) * Real.cot beta := by
  have hsin : Real.sin beta ≠ 0 := (typeB_sin_pos hlam0 hlam1 hbeta).ne'
  rw [typeBRadius, typeBAlpha, Real.sin_add,
    Real.cos_arccos (by linarith) (by linarith), Real.sin_arccos,
    Real.cot_eq_cos_div_sin]
  field_simp [hsin] <;> ring

/-- Cotangent is strictly decreasing on the whole geometric angle interval. -/
lemma cot_strictAntiOn_Ioo_zero_pi :
    StrictAntiOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have htan : Real.tan (Real.pi / 2 - y) < Real.tan (Real.pi / 2 - x) :=
    Real.strictMonoOn_tan
      ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
      ⟨by linarith [hx.2, Real.pi_pos], by linarith [hx.1]⟩
      (by linarith)
  simpa only [Real.tan_pi_div_two_sub, Real.tan_inv_eq_cot] using htan

/-- Type-(B) radius is strictly decreasing; no hidden angular branch remains. -/
lemma typeBRadius_strictAntiOn {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictAntiOn (typeBRadius lam) {beta | BAdmissible lam beta} := by
  intro beta hbeta beta' hbeta' hlt
  have hbeta_pi : beta < Real.pi := by
    have hacos : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
    linarith [hbeta.2]
  have hbeta'_pi : beta' < Real.pi := by
    have hacos : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
    linarith [hbeta'.2]
  have hcot : Real.cot beta' < Real.cot beta :=
    cot_strictAntiOn_Ioo_zero_pi ⟨hbeta.1, hbeta_pi⟩
      ⟨hbeta'.1, hbeta'_pi⟩ hlt
  rw [typeBRadius_eq_add_sqrt_mul_cot hlam0 hlam1 hbeta,
    typeBRadius_eq_add_sqrt_mul_cot hlam0 hlam1 hbeta']
  nlinarith [sqrt_one_sub_sq_pos hlam0 hlam1]

/-- Equality of finite type-(B) radii forces equality of the source angle. -/
lemma typeBRadius_injective_on_admissible {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Set.InjOn (typeBRadius lam) {beta | BAdmissible lam beta} :=
  (typeBRadius_strictAntiOn hlam0 hlam1).injOn

/-- The branch-safe type-(B) inverse radius chart.  The single arctangent
formula lands above `π / 2` exactly when `R < λ`. -/
def betaAtRadius (lam R : ℝ) : ℝ :=
  Real.pi / 2 - Real.arctan ((R - lam) / Real.sqrt (1 - lam ^ 2))

/-- The branch-safe type-(C) inverse radius chart. -/
def bAtRadius (R : ℝ) : ℝ := Real.arctan (1 / R)

lemma betaAtRadius_pos {lam R : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    0 < betaAtRadius lam R := by
  unfold betaAtRadius
  linarith [Real.arctan_lt_pi_div_two
    ((R - lam) / Real.sqrt (1 - lam ^ 2))]

lemma betaAtRadius_gt_pi_div_two {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : R < lam) :
    Real.pi / 2 < betaAtRadius lam R := by
  unfold betaAtRadius
  have hsqrt : 0 < Real.sqrt (1 - lam ^ 2) := sqrt_one_sub_sq_pos hlam0 hlam1
  have hquot : (R - lam) / Real.sqrt (1 - lam ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hsqrt
  linarith [Real.arctan_lt_zero.2 hquot]

lemma betaAtRadius_le_pi_div_two {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam ≤ R) :
    betaAtRadius lam R ≤ Real.pi / 2 := by
  unfold betaAtRadius
  have hsqrt : 0 < Real.sqrt (1 - lam ^ 2) := sqrt_one_sub_sq_pos hlam0 hlam1
  have hquot : 0 ≤ (R - lam) / Real.sqrt (1 - lam ^ 2) :=
    div_nonneg (by linarith) hsqrt.le
  linarith [Real.arctan_nonneg.2 hquot]

lemma cot_betaAtRadius {lam R : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Real.cot (betaAtRadius lam R) =
      (R - lam) / Real.sqrt (1 - lam ^ 2) := by
  rw [betaAtRadius, ← Real.tan_inv_eq_cot, ← Real.tan_pi_div_two_sub]
  convert Real.tan_arctan ((R - lam) / Real.sqrt (1 - lam ^ 2)) using 1 <;> ring

lemma arctan_neg_lam_div_sqrt_eq_arccos_sub_pi_div_two {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Real.arctan (-lam / Real.sqrt (1 - lam ^ 2)) =
      Real.arccos lam - Real.pi / 2 := by
  have hsqrt : 0 < Real.sqrt (1 - lam ^ 2) := sqrt_one_sub_sq_pos hlam0 hlam1
  have hangle_lower : -(Real.pi / 2) < Real.arccos lam - Real.pi / 2 := by
    have hacos : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
    linarith
  have hangle_upper : Real.arccos lam - Real.pi / 2 < Real.pi / 2 := by
    have hacos : Real.arccos lam < Real.pi / 2 :=
      Real.arccos_lt_pi_div_two.2 hlam0
    linarith
  have htan : Real.tan (Real.arccos lam - Real.pi / 2) =
      -lam / Real.sqrt (1 - lam ^ 2) := by
    rw [show Real.arccos lam - Real.pi / 2 =
        -(Real.pi / 2 - Real.arccos lam) by ring, Real.tan_neg,
        Real.tan_pi_div_two_sub, Real.tan_arccos, inv_div] <;>
      field_simp [hsqrt.ne'] <;> ring
  rw [← htan, Real.arctan_tan hangle_lower hangle_upper]

lemma betaAtRadius_admissible {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 ≤ R) :
    BAdmissible lam (betaAtRadius lam R) := by
  constructor
  · exact betaAtRadius_pos hlam0 hlam1
  · have hsqrt : 0 < Real.sqrt (1 - lam ^ 2) := sqrt_one_sub_sq_pos hlam0 hlam1
    have hquot : -lam / Real.sqrt (1 - lam ^ 2) ≤
        (R - lam) / Real.sqrt (1 - lam ^ 2) := by
      apply (div_le_div_iff_of_pos_right hsqrt).2
      linarith
    have hatan : Real.arctan (-lam / Real.sqrt (1 - lam ^ 2)) ≤
        Real.arctan ((R - lam) / Real.sqrt (1 - lam ^ 2)) :=
      Real.arctan_strictMono.monotone hquot
    rw [arctan_neg_lam_div_sqrt_eq_arccos_sub_pi_div_two hlam0 hlam1] at hatan
    unfold betaAtRadius
    linarith

lemma typeBRadius_betaAtRadius {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 ≤ R) :
    typeBRadius lam (betaAtRadius lam R) = R := by
  rw [typeBRadius_eq_add_sqrt_mul_cot hlam0 hlam1
    (betaAtRadius_admissible hlam0 hlam1 hR), cot_betaAtRadius hlam0 hlam1]
  have hsqrt : Real.sqrt (1 - lam ^ 2) ≠ 0 :=
    (sqrt_one_sub_sq_pos hlam0 hlam1).ne'
  field_simp [hsqrt] <;> ring


/-- The inverse chart validates the `R < λ` quadrant without a selected
fallback branch. -/
lemma betaAtRadius_lt_branch {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR0 : 0 ≤ R) (hR : R < lam) :
    BAdmissible lam (betaAtRadius lam R) ∧
      Real.pi / 2 < betaAtRadius lam R ∧
      typeBRadius lam (betaAtRadius lam R) = R :=
  ⟨betaAtRadius_admissible hlam0 hlam1 hR0,
    betaAtRadius_gt_pi_div_two hlam0 hlam1 hR,
    typeBRadius_betaAtRadius hlam0 hlam1 hR0⟩

/-- The inverse chart validates the `R ≥ λ` quadrant without identifying it
with the geometrically distinct `R < λ` branch. -/
lemma betaAtRadius_ge_branch {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR0 : 0 ≤ R) (hR : lam ≤ R) :
    BAdmissible lam (betaAtRadius lam R) ∧
      betaAtRadius lam R ≤ Real.pi / 2 ∧
      typeBRadius lam (betaAtRadius lam R) = R :=
  ⟨betaAtRadius_admissible hlam0 hlam1 hR0,
    betaAtRadius_le_pi_div_two hlam0 hlam1 hR,
    typeBRadius_betaAtRadius hlam0 hlam1 hR0⟩
/-- Every finite type-(B) candidate has a nonnegative exterior radius. -/
lemma typeBRadius_nonneg {lam beta : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hbeta : BAdmissible lam beta) :
    0 ≤ typeBRadius lam beta := by
  rw [typeBRadius]
  exact div_nonneg (typeBAlpha_sin_nonneg hbeta)
    (typeB_sin_pos hlam0 hlam1 hbeta).le

/-- The complete nonnegative type-(B) radius range, including its zero-radius
endpoint. -/
lemma typeBRadius_surjective_nonnegative {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Set.SurjOn (typeBRadius lam) {beta | BAdmissible lam beta} (Set.Ici 0) := by
  intro R hR
  exact ⟨betaAtRadius lam R, betaAtRadius_admissible hlam0 hlam1 hR,
    typeBRadius_betaAtRadius hlam0 hlam1 hR⟩

/-- The B inverse is a genuine inverse on all finite admissible candidates. -/
lemma betaAtRadius_typeBRadius {lam beta : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hbeta : BAdmissible lam beta) :
    betaAtRadius lam (typeBRadius lam beta) = beta := by
  apply typeBRadius_injective_on_admissible hlam0 hlam1
    (betaAtRadius_admissible hlam0 hlam1 (typeBRadius_nonneg hlam0 hlam1 hbeta))
    hbeta
  rw [typeBRadius_betaAtRadius hlam0 hlam1
    (typeBRadius_nonneg hlam0 hlam1 hbeta)]


/-- The B chart has exactly the audited nonnegative radius range. -/
lemma typeBRadius_image_admissible_eq_Ici {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    typeBRadius lam '' {beta | BAdmissible lam beta} = Set.Ici 0 := by
  ext R
  constructor
  · rintro ⟨beta, hbeta, rfl⟩
    exact typeBRadius_nonneg hlam0 hlam1 hbeta
  · intro hR
    exact typeBRadius_surjective_nonnegative hlam0 hlam1 hR

/-- The zero-radius endpoint is the printed angular endpoint, not a default
inverse value. -/
lemma betaAtRadius_zero {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    betaAtRadius lam 0 = Real.pi - Real.arccos lam := by
  rw [betaAtRadius, zero_sub,
    arctan_neg_lam_div_sqrt_eq_arccos_sub_pi_div_two hlam0 hlam1]
  ring

lemma typeBRadius_endpoint_zero {lam : ℝ} :
    typeBRadius lam (Real.pi - Real.arccos lam) = 0 := by
  rw [typeBRadius, typeBAlpha,
    show Real.pi - Real.arccos lam + Real.arccos lam = Real.pi by ring,
    Real.sin_pi, zero_div]

lemma bAtRadius_admissible {R : ℝ} (hR : 0 < R) :
    CAdmissible (bAtRadius R) := by
  constructor
  · exact Real.arctan_pos.2 (one_div_pos.mpr hR)
  · exact Real.arctan_lt_pi_div_two _

lemma typeCRadius_bAtRadius {R : ℝ} (hR : 0 < R) :
    typeCRadius (bAtRadius R) = R := by
  rw [typeCRadius, bAtRadius, Real.tan_arctan]
  field_simp [hR.ne']

/-- The C inverse is a genuine inverse on its complete finite angular domain. -/
lemma bAtRadius_typeCRadius {beta : ℝ} (hbeta : CAdmissible beta) :
    bAtRadius (typeCRadius beta) = beta := by
  apply typeCRadius_injective_on_admissible
    (bAtRadius_admissible (typeCRadius_pos hbeta)) hbeta
  rw [typeCRadius_bAtRadius (typeCRadius_pos hbeta)]

/-- The complete positive type-(C) radius range. -/

lemma typeCRadius_surjective_positive :
    Set.SurjOn typeCRadius {beta | CAdmissible beta} (Set.Ioi 0) := by
  intro R hR
  exact ⟨bAtRadius R, bAtRadius_admissible hR,
    typeCRadius_bAtRadius hR⟩

/-- The C chart has exactly the audited positive radius range. -/
lemma typeCRadius_image_admissible_eq_Ioi :
    typeCRadius '' {beta | CAdmissible beta} = Set.Ioi 0 := by
  ext R
  constructor
  · rintro ⟨beta, hbeta, rfl⟩
    exact typeCRadius_pos hbeta
  · intro hR
    exact typeCRadius_surjective_positive hR

/-- Type-(B) weighted perimeter in the global radius chart. -/
def typeBPerimeterAtRadius (lam R : ℝ) : ℝ :=
  2 * ((Real.pi - betaAtRadius lam R) * R +
    lam * (betaAtRadius lam R + Real.arccos lam))

/-- Type-(B) weighted area in the global radius chart. -/
def typeBAreaAtRadius (lam R : ℝ) : ℝ :=
  R ^ 2 * (Real.pi - betaAtRadius lam R +
      Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R)) +
    (betaAtRadius lam R + Real.arccos lam -
      Real.sin (betaAtRadius lam R + Real.arccos lam) *
        Real.cos (betaAtRadius lam R + Real.arccos lam)) -
    (1 - lam) * Real.pi

/-- Type-(C) weighted perimeter in its positive-radius chart. -/
def typeCPerimeterAtRadius (lam R : ℝ) : ℝ :=
  2 * R * (Real.pi - (1 - lam) * bAtRadius R)

/-- Type-(C) weighted area in its positive-radius chart. -/
def typeCAreaAtRadius (lam R : ℝ) : ℝ :=
  R ^ 2 * (Real.pi - (1 - lam) *
      (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R))) -
    (1 - lam) * (Real.pi / 2 - bAtRadius R -
      Real.sin (bAtRadius R) * Real.cos (bAtRadius R))

lemma typeBPerimeterAtRadius_agrees {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 ≤ R) :
    typeBPerimeterAtRadius lam R =
      typeBPerimeter lam (betaAtRadius lam R) := by
  rw [typeBPerimeterAtRadius, typeBPerimeter, typeBAlpha,
    typeBRadius_betaAtRadius hlam0 hlam1 hR]

lemma typeBAreaAtRadius_agrees {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 ≤ R) :
    typeBAreaAtRadius lam R = typeBArea lam (betaAtRadius lam R) := by
  rw [typeBAreaAtRadius, typeBArea, typeBAlpha,
    typeBRadius_betaAtRadius hlam0 hlam1 hR]

lemma typeCPerimeterAtRadius_agrees {lam R : ℝ} (hR : 0 < R) :
    typeCPerimeterAtRadius lam R =
      typeCPerimeter lam (bAtRadius R) := by
  rw [typeCPerimeterAtRadius, typeCPerimeter, div_eq_mul_inv]
  have hradius := typeCRadius_bAtRadius hR
  rw [typeCRadius, one_div] at hradius
  rw [hradius]
  ring

lemma typeCAreaAtRadius_agrees {lam R : ℝ} (hR : 0 < R) :
    typeCAreaAtRadius lam R = typeCArea lam (bAtRadius R) := by
  rw [typeCAreaAtRadius, typeCArea]
  have hradius := typeCRadius_bAtRadius hR
  rw [typeCRadius, one_div] at hradius
  have hden : (Real.tan (bAtRadius R) ^ 2)⁻¹ = R ^ 2 := by
    rw [← inv_pow, hradius]
  nth_rewrite 2 [div_eq_mul_inv]
  rw [hden]
  ring

lemma betaAtRadius_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (betaAtRadius lam)
      (-Real.sqrt (1 - lam ^ 2) /
        ((R - lam) ^ 2 + Real.sqrt (1 - lam ^ 2) ^ 2)) R := by
  have hs : Real.sqrt (1 - lam ^ 2) ≠ 0 :=
    (sqrt_one_sub_sq_pos hlam0 hlam1).ne'
  have hlin : HasDerivAt (fun x : ℝ => x - lam) 1 R := by
    simpa only [id_eq] using (hasDerivAt_id R).sub_const lam
  have hq := hlin.div_const (Real.sqrt (1 - lam ^ 2))
  have ha := hq.arctan
  have hb := (hasDerivAt_const R (Real.pi / 2)).sub ha
  convert hb using 1 <;>
    first | rfl | (field_simp [hs] <;> ring)

lemma bAtRadius_hasDerivAt {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt bAtRadius (-1 / (1 + R ^ 2)) R := by
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1 / R ^ 2) R := by
    convert (hasDerivAt_const R 1).div (hasDerivAt_id R) hR using 1 <;>
      first | rfl | simp only [id_eq, zero_mul, one_mul, zero_sub]
  have ha := hi.arctan
  unfold bAtRadius
  convert ha using 1 <;>
    first | rfl | (field_simp [hR] <;> ring)

lemma sin_betaAtRadius_mul_cos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R) =
      (R - lam) * Real.sqrt (1 - lam ^ 2) /
        ((R - lam) ^ 2 + Real.sqrt (1 - lam ^ 2) ^ 2) := by
  have hs : 0 < Real.sqrt (1 - lam ^ 2) :=
    sqrt_one_sub_sq_pos hlam0 hlam1
  let x := (R - lam) / Real.sqrt (1 - lam ^ 2)
  have hq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hq0 : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  rw [betaAtRadius, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.cos_arctan, Real.sin_arctan]
  change (1 / Real.sqrt (1 + x ^ 2)) *
      (x / Real.sqrt (1 + x ^ 2)) = _
  field_simp [hs.ne', hq0]
  rw [hq]
  dsimp [x]
  field_simp [hs.ne']
  ring

lemma sin_bAtRadius_mul_cos {R : ℝ} (hR : R ≠ 0) :
    Real.sin (bAtRadius R) * Real.cos (bAtRadius R) =
      R / (1 + R ^ 2) := by
  let q := Real.sqrt (1 + (1 / R) ^ 2)
  have hq : q ^ 2 = 1 + (1 / R) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hq0 : q ≠ 0 := by positivity
  rw [bAtRadius, Real.sin_arctan, Real.cos_arctan]
  change ((1 / R) / q) * (1 / q) = _
  calc
    ((1 / R) / q) * (1 / q) = (1 / R) / q ^ 2 := by
      field_simp [hq0]
    _ = R / (1 + R ^ 2) := by
      rw [hq]
      field_simp [hR]
      ring

lemma typeBPerimeterAtRadius_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (typeBPerimeterAtRadius lam)
      (2 * (Real.pi - betaAtRadius lam R +
        Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R))) R := by
  let db := -Real.sqrt (1 - lam ^ 2) /
    ((R - lam) ^ 2 + Real.sqrt (1 - lam ^ 2) ^ 2)
  have hb : HasDerivAt (betaAtRadius lam) db R :=
    betaAtRadius_hasDerivAt hlam0 hlam1
  have hraw := (((hasDerivAt_const R Real.pi).sub hb).mul
    (hasDerivAt_id R)).add
      ((hb.add_const (Real.arccos lam)).const_mul lam) |>.const_mul 2
  have hfun : HasDerivAt (typeBPerimeterAtRadius lam)
      (2 * ((0 - db) * R + (Real.pi - betaAtRadius lam R) * 1 +
        lam * db)) R := by
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => by
      simp [typeBPerimeterAtRadius, id]
  convert hfun using 1
  dsimp [db]
  rw [sin_betaAtRadius_mul_cos hlam0 hlam1]
  field_simp
  ring

lemma typeCPerimeterAtRadius_hasDerivAt {lam R : ℝ} (hR : 0 < R) :
    HasDerivAt (typeCPerimeterAtRadius lam)
      (2 * (Real.pi - (1 - lam) *
        (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R)))) R := by
  let db := -1 / (1 + R ^ 2)
  have hb : HasDerivAt bAtRadius db R := bAtRadius_hasDerivAt hR.ne'
  have hraw := ((hasDerivAt_id R).mul
    ((hasDerivAt_const R Real.pi).sub
      (hb.const_mul (1 - lam)))).const_mul 2
  have hfun : HasDerivAt (typeCPerimeterAtRadius lam)
      (2 * (1 * (Real.pi - (1 - lam) * bAtRadius R) +
        R * (0 - (1 - lam) * db))) R := by
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => by
      simp only [typeCPerimeterAtRadius, id_eq, Pi.mul_apply, Pi.sub_apply]
      ring
  convert hfun using 1
  dsimp [db]
  rw [sin_bAtRadius_mul_cos hR.ne']
  field_simp
  ring

/-- Twice the circular-segment area with unit radius. -/
def arcSegment (x : ℝ) : ℝ := x - Real.sin x * Real.cos x

lemma arcSegment_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => arcSegment (f y))
      (2 * Real.sin (f x) ^ 2 * f') x := by
  have hraw := hf.sub (hf.sin.mul hf.cos)
  have hfun : HasDerivAt
      (fun y => arcSegment (f y))
      (f' - (Real.cos (f x) * f' * Real.cos (f x) +
        Real.sin (f x) * (-Real.sin (f x) * f'))) x := by
    convert hraw using 1 <;>
      first | rfl | exact Subsingleton.elim _ _ | (funext y; rfl)
  have htrig := Real.sin_sq_add_cos_sq (f x)
  have hcos : Real.cos (f x) ^ 2 = 1 - Real.sin (f x) ^ 2 := by
    linarith
  have hcoef : 2 * Real.sin (f x) ^ 2 * f' =
      f' - (Real.cos (f x) * f' * Real.cos (f x) +
        Real.sin (f x) * (-Real.sin (f x) * f')) := by
    rw [show Real.cos (f x) * f' * Real.cos (f x) =
      Real.cos (f x) ^ 2 * f' by ring, hcos]
    ring
  rw [hcoef]
  exact hfun

lemma sin_typeBAlpha_betaAtRadius {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 ≤ R) :
    Real.sin (betaAtRadius lam R + Real.arccos lam) =
      R * Real.sin (betaAtRadius lam R) := by
  have hadm := betaAtRadius_admissible hlam0 hlam1 hR
  have hs : Real.sin (betaAtRadius lam R) ≠ 0 :=
    (typeB_sin_pos hlam0 hlam1 hadm).ne'
  have hr := typeBRadius_betaAtRadius hlam0 hlam1 hR
  rw [typeBRadius, typeBAlpha] at hr
  exact (div_eq_iff hs).mp hr

lemma cos_bAtRadius_eq_radius_mul_sin {R : ℝ} (hR : 0 < R) :
    Real.cos (bAtRadius R) = R * Real.sin (bAtRadius R) := by
  have hadm := bAtRadius_admissible hR
  have hs : Real.sin (bAtRadius R) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hadm.1 (by
      linarith [hadm.2, Real.pi_pos])).ne'
  have hr := typeCRadius_bAtRadius hR
  rw [typeCRadius, one_div, Real.tan_inv_eq_cot,
    Real.cot_eq_cos_div_sin] at hr
  exact (div_eq_iff hs).mp hr

lemma typeBAreaAtRadius_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    HasDerivAt (typeBAreaAtRadius lam)
      (R * (2 * (Real.pi - betaAtRadius lam R +
        Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R)))) R := by
  let db := -Real.sqrt (1 - lam ^ 2) /
    ((R - lam) ^ 2 + Real.sqrt (1 - lam ^ 2) ^ 2)
  have hb : HasDerivAt (betaAtRadius lam) db R :=
    betaAtRadius_hasDerivAt hlam0 hlam1
  have hsB := arcSegment_hasDerivAt hb
  have ha := hb.add_const (Real.arccos lam)
  have hsA := arcSegment_hasDerivAt ha
  have hq := (hasDerivAt_const R Real.pi).sub hsB
  have hr2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * R) R := by
    convert (hasDerivAt_id R).pow 2 using 1 <;>
      first | rfl | norm_num
  have hraw := (hr2.mul hq).add hsA |>.sub_const ((1 - lam) * Real.pi)
  have heq : typeBAreaAtRadius lam =ᶠ[nhds R]
      (fun x => x ^ 2 * (Real.pi - arcSegment (betaAtRadius lam x)) +
        arcSegment (betaAtRadius lam x + Real.arccos lam) -
        (1 - lam) * Real.pi) := by
    exact Filter.Eventually.of_forall fun x => by
      unfold typeBAreaAtRadius arcSegment
      ring
  have hfun := hraw.congr_of_eventuallyEq heq
  have hsin := sin_typeBAlpha_betaAtRadius hlam0 hlam1 hR.le
  have hcoef : R * (2 * (Real.pi - betaAtRadius lam R +
        Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R))) =
      2 * R * (Real.pi - arcSegment (betaAtRadius lam R)) +
        R ^ 2 * (0 - 2 * Real.sin (betaAtRadius lam R) ^ 2 * db) +
        2 * Real.sin (betaAtRadius lam R + Real.arccos lam) ^ 2 * db := by
    rw [hsin]
    simp only [arcSegment]
    ring
  rw [hcoef]
  exact hfun

lemma typeCAreaAtRadius_hasDerivAt {lam R : ℝ} (hR : 0 < R) :
    HasDerivAt (typeCAreaAtRadius lam)
      (R * (2 * (Real.pi - (1 - lam) *
        (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R))))) R := by
  let db := -1 / (1 + R ^ 2)
  have hb : HasDerivAt bAtRadius db R := bAtRadius_hasDerivAt hR.ne'
  have hsB := arcSegment_hasDerivAt hb
  have hq := (hasDerivAt_const R Real.pi).sub
    (hsB.const_mul (1 - lam))
  have hr2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * R) R := by
    convert (hasDerivAt_id R).pow 2 using 1 <;>
      first | rfl | norm_num
  have hg := (hasDerivAt_const R (Real.pi / 2)).sub hb
  have hsG := arcSegment_hasDerivAt hg
  have hraw := (hr2.mul hq).sub (hsG.const_mul (1 - lam))
  have heq : typeCAreaAtRadius lam =ᶠ[nhds R]
      (fun x => x ^ 2 * (Real.pi - (1 - lam) * arcSegment (bAtRadius x)) -
        (1 - lam) * arcSegment (Real.pi / 2 - bAtRadius x)) := by
    exact Filter.Eventually.of_forall fun x => by
      unfold typeCAreaAtRadius arcSegment
      simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring
  have hfun := hraw.congr_of_eventuallyEq heq
  have hcos := cos_bAtRadius_eq_radius_mul_sin hR
  have hcoef : R * (2 * (Real.pi - (1 - lam) *
        (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R)))) =
      2 * R * (Real.pi - (1 - lam) * arcSegment (bAtRadius R)) +
        R ^ 2 * (0 - (1 - lam) *
          (2 * Real.sin (bAtRadius R) ^ 2 * db)) -
        (1 - lam) * (2 * Real.sin (Real.pi / 2 - bAtRadius R) ^ 2 *
          (0 - db)) := by
    rw [Real.sin_pi_div_two_sub]
    simp only [arcSegment]
    simp_rw [hcos]
    ring
  rw [hcoef]
  exact hfun

lemma arcSegment_pos {x : ℝ} (hx0 : 0 < x) (hxpi : x < Real.pi) :
    0 < arcSegment x := by
  unfold arcSegment
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  by_cases hc : Real.cos x ≤ 0
  · have hp : Real.sin x * Real.cos x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.le hc
    linarith
  · have hc1 : Real.cos x ≤ 1 := Real.cos_le_one x
    have hp : Real.sin x * Real.cos x ≤ Real.sin x :=
      mul_le_of_le_one_right hs.le hc1
    linarith [Real.sin_lt hx0]

lemma typeB_perimeter_factor_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    0 < Real.pi - betaAtRadius lam R +
      Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R) := by
  have hadm := betaAtRadius_admissible hlam0 hlam1 hR.le
  have hstrict : betaAtRadius lam R < Real.pi - Real.arccos lam := by
    by_contra hn
    have heq : betaAtRadius lam R = Real.pi - Real.arccos lam :=
      le_antisymm hadm.2 (le_of_not_gt hn)
    have hr := typeBRadius_betaAtRadius hlam0 hlam1 hR.le
    rw [heq, typeBRadius_endpoint_zero] at hr
    linarith
  have ht0 : 0 < Real.pi - betaAtRadius lam R := by
    have hacos : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
    linarith
  have htpi : Real.pi - betaAtRadius lam R < Real.pi := by
    linarith [hadm.1]
  have hseg := arcSegment_pos ht0 htpi
  rw [arcSegment, Real.sin_pi_sub, Real.cos_pi_sub] at hseg
  linarith

lemma typeC_perimeter_factor_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    0 < Real.pi - (1 - lam) *
      (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R)) := by
  have hb := bAtRadius_admissible hR
  have hs : 0 < Real.sin (bAtRadius R) :=
    Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have hc : 0 < Real.cos (bAtRadius R) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1, Real.pi_pos], hb.2⟩
  have hseglt : arcSegment (bAtRadius R) < bAtRadius R := by
    unfold arcSegment
    nlinarith
  have hsegpos : 0 < arcSegment (bAtRadius R) :=
    arcSegment_pos hb.1 (by linarith [hb.2, Real.pi_pos])
  have hm : (1 - lam) * arcSegment (bAtRadius R) <
      arcSegment (bAtRadius R) := by nlinarith
  dsimp [arcSegment] at hseglt hm
  linarith [hb.2, Real.pi_pos]

lemma typeBAreaAtRadius_deriv_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    0 < deriv (typeBAreaAtRadius lam) R := by
  rw [(typeBAreaAtRadius_hasDerivAt hlam0 hlam1 hR).deriv]
  have hq := typeB_perimeter_factor_pos hlam0 hlam1 hR
  positivity

lemma typeCAreaAtRadius_deriv_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    0 < deriv (typeCAreaAtRadius lam) R := by
  rw [(typeCAreaAtRadius_hasDerivAt hR).deriv]
  have hq := typeC_perimeter_factor_pos hlam0 hlam1 hR
  positivity

lemma typeBPerimeterAtRadius_deriv_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    0 < R → 0 < deriv (typeBPerimeterAtRadius lam) R := by
  intro hR
  rw [(typeBPerimeterAtRadius_hasDerivAt hlam0 hlam1).deriv]
  have hq := typeB_perimeter_factor_pos hlam0 hlam1 hR
  positivity

lemma typeCPerimeterAtRadius_deriv_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    0 < R → 0 < deriv (typeCPerimeterAtRadius lam) R := by
  intro hR
  rw [(typeCPerimeterAtRadius_hasDerivAt hR).deriv]
  have hq := typeC_perimeter_factor_pos hlam0 hlam1 hR
  positivity

lemma typeBAreaAtRadius_continuous {lam : ℝ} :
    Continuous (typeBAreaAtRadius lam) := by
  unfold typeBAreaAtRadius betaAtRadius
  fun_prop

lemma typeBPerimeterAtRadius_continuous {lam : ℝ} :
    Continuous (typeBPerimeterAtRadius lam) := by
  unfold typeBPerimeterAtRadius betaAtRadius
  fun_prop

lemma typeCAreaAtRadius_continuousOn {lam : ℝ} :
    ContinuousOn (typeCAreaAtRadius lam) (Set.Ioi 0) := by
  intro R hR
  exact (typeCAreaAtRadius_hasDerivAt hR).continuousAt.continuousWithinAt

lemma typeCPerimeterAtRadius_continuousOn {lam : ℝ} :
    ContinuousOn (typeCPerimeterAtRadius lam) (Set.Ioi 0) := by
  intro R hR
  exact (typeCPerimeterAtRadius_hasDerivAt hR).continuousAt.continuousWithinAt

lemma typeBAreaAtRadius_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeBAreaAtRadius lam) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    typeBAreaAtRadius_continuous.continuousOn
  intro R hR
  rw [interior_Ici] at hR
  exact typeBAreaAtRadius_deriv_pos hlam0 hlam1 hR

lemma typeCAreaAtRadius_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeCAreaAtRadius lam) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    typeCAreaAtRadius_continuousOn
  intro R hR
  rw [interior_Ioi] at hR
  exact typeCAreaAtRadius_deriv_pos hlam0 hlam1 hR

lemma typeBPerimeterAtRadius_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeBPerimeterAtRadius lam) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    typeBPerimeterAtRadius_continuous.continuousOn
  intro R hR
  rw [interior_Ici] at hR
  exact typeBPerimeterAtRadius_deriv_pos hlam0 hlam1 hR

lemma typeCPerimeterAtRadius_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeCPerimeterAtRadius lam) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    typeCPerimeterAtRadius_continuousOn
  intro R hR
  rw [interior_Ioi] at hR
  exact typeCPerimeterAtRadius_deriv_pos hlam0 hlam1 hR

lemma typeBAreaAtRadius_zero {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    typeBAreaAtRadius lam 0 = lam * Real.pi := by
  rw [typeBAreaAtRadius_agrees hlam0 hlam1 (le_refl 0),
    betaAtRadius_zero hlam0 hlam1, typeBArea, typeBRadius_endpoint_zero,
    typeBAlpha]
  rw [show Real.pi - Real.arccos lam + Real.arccos lam = Real.pi by ring,
    Real.sin_pi]
  ring

lemma typeBPerimeterAtRadius_zero {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    typeBPerimeterAtRadius lam 0 = 2 * lam * Real.pi := by
  rw [typeBPerimeterAtRadius_agrees hlam0 hlam1 (le_refl 0),
    betaAtRadius_zero hlam0 hlam1, typeBPerimeter, typeBRadius_endpoint_zero,
    typeBAlpha]
  ring

lemma arcSegment_lt_self {x : ℝ} (hx0 : 0 < x) (hx2 : x < Real.pi / 2) :
    arcSegment x < x := by
  unfold arcSegment
  have hs := Real.sin_pos_of_pos_of_lt_pi hx0
    (by linarith [hx2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx0, Real.pi_pos], hx2⟩
  nlinarith

lemma arcSegment_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    0 ≤ arcSegment x := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · simp [arcSegment]
  rcases eq_or_lt_of_le hxpi with rfl | hxpi'
  · simp [arcSegment, Real.sin_pi, Real.pi_pos.le]
  exact (arcSegment_pos hx0' hxpi').le

lemma typeBAreaAtRadius_large_lower {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam ≤ R) :
    R ^ 2 * (Real.pi / 2) - Real.pi < typeBAreaAtRadius lam R := by
  have hR0 : 0 < R := lt_of_lt_of_le hlam0 hR
  have hb := betaAtRadius_admissible hlam0 hlam1 hR0.le
  have hb2 := betaAtRadius_le_pi_div_two hlam0 hlam1 hR
  have hs := Real.sin_pos_of_pos_of_lt_pi hb.1
    (by linarith [hb.2, Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hb.1, Real.pi_pos], hb2⟩
  have hsegB : arcSegment (betaAtRadius lam R) ≤ Real.pi / 2 := by
    unfold arcSegment
    nlinarith
  have ha0 : 0 ≤ betaAtRadius lam R + Real.arccos lam :=
    add_nonneg hb.1.le (Real.arccos_nonneg lam)
  have hapi : betaAtRadius lam R + Real.arccos lam ≤ Real.pi := by
    linarith [hb.2]
  have hsegA : 0 ≤ arcSegment
      (betaAtRadius lam R + Real.arccos lam) :=
    arcSegment_nonneg ha0 hapi
  have hq : Real.pi / 2 ≤ Real.pi - arcSegment (betaAtRadius lam R) := by
    linarith
  have hp : 0 < Real.pi := Real.pi_pos
  unfold typeBAreaAtRadius arcSegment at *
  nlinarith [sq_nonneg R]

lemma typeCAreaAtRadius_lt_full {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    typeCAreaAtRadius lam R < Real.pi * R ^ 2 := by
  rcases bAtRadius_admissible hR with ⟨hb0, hb2⟩
  have hsegB : 0 < arcSegment (bAtRadius R) :=
    arcSegment_pos hb0 (by linarith [hb2, Real.pi_pos])
  have hg0 : 0 < Real.pi / 2 - bAtRadius R := by linarith
  have hg2 : Real.pi / 2 - bAtRadius R < Real.pi / 2 := by linarith
  have hsegG : 0 < arcSegment (Real.pi / 2 - bAtRadius R) :=
    arcSegment_pos hg0 (by linarith [hg2, Real.pi_pos])
  have hlam : 0 < 1 - lam := by linarith
  rw [show typeCAreaAtRadius lam R =
    R ^ 2 * (Real.pi - (1 - lam) * arcSegment (bAtRadius R)) -
      (1 - lam) * arcSegment (Real.pi / 2 - bAtRadius R) by
        unfold typeCAreaAtRadius arcSegment
        rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
        ring]
  have hp : 0 < R ^ 2 * ((1 - lam) * arcSegment (bAtRadius R)) :=
    mul_pos (sq_pos_of_pos hR) (mul_pos hlam hsegB)
  have hg : 0 < (1 - lam) * arcSegment (Real.pi / 2 - bAtRadius R) :=
    mul_pos hlam hsegG
  nlinarith

lemma typeCAreaAtRadius_large_lower {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    lam * Real.pi * R ^ 2 - Real.pi / 2 < typeCAreaAtRadius lam R := by
  rcases bAtRadius_admissible hR with ⟨hb0, hb2⟩
  have hsegBpos : 0 < arcSegment (bAtRadius R) :=
    arcSegment_pos hb0 (by linarith [hb2, Real.pi_pos])
  have hsegBlt : arcSegment (bAtRadius R) < Real.pi / 2 :=
    (arcSegment_lt_self hb0 hb2).trans hb2
  have hg0 : 0 < Real.pi / 2 - bAtRadius R := by linarith
  have hg2 : Real.pi / 2 - bAtRadius R < Real.pi / 2 := by linarith
  have hsegGpos : 0 < arcSegment (Real.pi / 2 - bAtRadius R) :=
    arcSegment_pos hg0 (by linarith [hg2, Real.pi_pos])
  have hsegGlt : arcSegment (Real.pi / 2 - bAtRadius R) < Real.pi / 2 :=
    (arcSegment_lt_self hg0 hg2).trans hg2
  have hlam : 0 < 1 - lam := by linarith
  have hq : lam * Real.pi <
      Real.pi - (1 - lam) * arcSegment (bAtRadius R) := by
    nlinarith [Real.pi_pos]
  have hg : (1 - lam) * arcSegment (Real.pi / 2 - bAtRadius R) <
      Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  rw [show typeCAreaAtRadius lam R =
    R ^ 2 * (Real.pi - (1 - lam) * arcSegment (bAtRadius R)) -
      (1 - lam) * arcSegment (Real.pi / 2 - bAtRadius R) by
        unfold typeCAreaAtRadius arcSegment
        rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
        ring]
  have hp0 := mul_lt_mul_of_pos_left hq (sq_pos_of_pos hR)
  have hp : lam * Real.pi * R ^ 2 <
      R ^ 2 * (Real.pi - (1 - lam) * arcSegment (bAtRadius R)) := by
    nlinarith
  linarith

lemma one_div_tendsto_atTop_at_zero_right :
    Filter.Tendsto (fun R : ℝ => 1 / R) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  by_cases hM : M ≤ 0
  · filter_upwards [self_mem_nhdsWithin] with R hR
    exact hM.trans (one_div_nonneg.mpr hR.le)
  · have hM0 : 0 < M := lt_of_not_ge hM
    have hInvM0 : 0 < 1 / M := one_div_pos.mpr hM0
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hInvM0)] with R hR hRlt
    apply (le_div_iff₀ hR).2
    have hmul : R * M < 1 := (lt_div_iff₀ hM0).mp hRlt
    nlinarith

lemma bAtRadius_tendsto_pi_div_two_at_zero_right :
    Filter.Tendsto bAtRadius (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
  have hinv := one_div_tendsto_atTop_at_zero_right
  have harctan : Filter.Tendsto Real.arctan Filter.atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1
  change Filter.Tendsto (fun R : ℝ => Real.arctan (1 / R))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2))
  exact harctan.comp hinv

lemma typeCAreaAtRadius_tendsto_zero_at_zero_right {lam : ℝ} :
    Filter.Tendsto (typeCAreaAtRadius lam) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hR : Filter.Tendsto (fun R : ℝ => R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hb := bAtRadius_tendsto_pi_div_two_at_zero_right
  have hsin : Filter.Tendsto (fun R : ℝ => Real.sin (bAtRadius R))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [Function.comp_def, Real.sin_pi_div_two] using
      (Real.continuous_sin.tendsto _).comp hb
  have hcos : Filter.Tendsto (fun R : ℝ => Real.cos (bAtRadius R))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_def, Real.cos_pi_div_two] using
      (Real.continuous_cos.tendsto _).comp hb
  have hprod := hsin.mul hcos
  have hq : Filter.Tendsto (fun R : ℝ => Real.pi - (1 - lam) *
      (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi - (1 - lam) * (Real.pi / 2))) := by
    simpa only [one_mul, mul_zero, sub_zero] using
      tendsto_const_nhds.sub ((hb.sub hprod).const_mul (1 - lam))
  have hg : Filter.Tendsto (fun R : ℝ => Real.pi / 2 - bAtRadius R -
      Real.sin (bAtRadius R) * Real.cos (bAtRadius R))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [sub_self, mul_zero, sub_zero] using
      (hb.const_sub (Real.pi / 2)).sub hprod
  have hmain := (hR.pow 2).mul hq
  have htail := hg.const_mul (1 - lam)
  unfold typeCAreaAtRadius
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, sub_zero] using hmain.sub htail

lemma typeCAreaAtRadius_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    0 < typeCAreaAtRadius lam R := by
  let f := typeCAreaAtRadius lam
  have hmono := typeCAreaAtRadius_strictMonoOn hlam0 hlam1
  have hlim := typeCAreaAtRadius_tendsto_zero_at_zero_right (lam := lam)
  have hT0 : 0 < R / 2 := by linarith
  have hTR : R / 2 < R := by linarith
  have hfT : f (R / 2) < f R := hmono hT0 hR hTR
  by_contra hn
  have hfR : f R ≤ 0 := le_of_not_gt hn
  have hfTneg : f (R / 2) < 0 := hfT.trans_le hfR
  have hgt : ∀ᶠ S in nhdsWithin 0 (Set.Ioi 0), f (R / 2) < f S :=
    hlim.eventually (eventually_gt_nhds hfTneg)
  have hsmall : ∀ᶠ S : ℝ in nhdsWithin 0 (Set.Ioi 0), S < R / 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT0)
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  have hboth := (hgt.and self_mem_nhdsWithin).and hsmall
  rcases hne.nonempty_of_mem hboth with ⟨S, ⟨hSgt, hS0⟩, hST⟩
  exact (not_lt_of_ge hSgt.le) (hmono hS0 hT0 hST)

lemma typeCAreaAtRadius_tendsto_atTop {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    Filter.Tendsto (typeCAreaAtRadius lam) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  let K := lam * Real.pi
  have hK : 0 < K := mul_pos hlam0 Real.pi_pos
  let R := max 1 ((M + Real.pi / 2 + 1) / K)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRfrac : (M + Real.pi / 2 + 1) / K ≤ R := le_max_right _ _
  have hRK : M + Real.pi / 2 + 1 ≤ R * K := by
    exact (div_le_iff₀ hK).mp hRfrac
  refine Filter.eventually_atTop.2 ⟨R, fun S hRS => ?_⟩
  have hS1 : 1 ≤ S := hR1.trans hRS
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hSq : R ≤ S ^ 2 := by nlinarith
  have hKSq : R * K ≤ K * S ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hSq hK.le]
  have hlarge := typeCAreaAtRadius_large_lower hlam0 hlam1 hS0
  dsimp [K] at hRK hKSq ⊢
  linarith

lemma exists_typeCRadius_at_positive_area {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hv : 0 < v) :
    ∃ R ∈ Set.Ioi 0, typeCAreaAtRadius lam R = v := by
  have hlim := typeCAreaAtRadius_tendsto_zero_at_zero_right (lam := lam)
  have hunb := typeCAreaAtRadius_tendsto_atTop hlam0 hlam1
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsGT_neBot 0
  have hbelow : ∀ᶠ L in nhdsWithin 0 (Set.Ioi 0), typeCAreaAtRadius lam L < v :=
    hlim.eventually (eventually_lt_nhds hv)
  rcases hne.nonempty_of_mem (hbelow.and self_mem_nhdsWithin) with ⟨L, hLv, hL0⟩
  have habove : ∀ᶠ U : ℝ in Filter.atTop, v ≤ typeCAreaAtRadius lam U :=
    hunb.eventually (Filter.eventually_atTop.2 ⟨v, fun y hy => hy⟩)
  have hfar : ∀ᶠ U : ℝ in Filter.atTop, L < U :=
    Filter.eventually_atTop.2 ⟨L + 1, fun U hU => by linarith⟩
  rcases (habove.and hfar).exists with ⟨U, hUv, hLU⟩
  have hcont : ContinuousOn (typeCAreaAtRadius lam) (Set.Icc L U) :=
    typeCAreaAtRadius_continuousOn.mono fun x hx => lt_of_lt_of_le hL0 hx.1
  have hvI : v ∈ Set.Icc (typeCAreaAtRadius lam L) (typeCAreaAtRadius lam U) :=
    ⟨hLv.le, hUv⟩
  rcases intermediate_value_Icc hLU.le hcont hvI with ⟨R, hRI, harea⟩
  exact ⟨R, lt_of_lt_of_le hL0 hRI.1, harea⟩

lemma typeCAreaAtRadius_image_Ioi_eq_Ioi {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    typeCAreaAtRadius lam '' Set.Ioi 0 = Set.Ioi 0 := by
  ext v
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact typeCAreaAtRadius_pos hlam0 hlam1 hR
  · intro hv
    exact exists_typeCRadius_at_positive_area hlam0 hlam1 hv

lemma exists_typeBRadius_at_area {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hv : lam * Real.pi < v) :
    ∃ R ∈ Set.Ioi 0, typeBAreaAtRadius lam R = v := by
  let M := v + Real.pi + 1
  have hv0 : 0 < v := lt_trans (mul_pos hlam0 Real.pi_pos) hv
  have hM0 : 0 < M := by dsimp [M]; positivity
  have hMlam : lam ≤ M := by dsimp [M]; linarith [Real.pi_pos]
  have hlower := typeBAreaAtRadius_large_lower hlam0 hlam1 hMlam
  have hpi2 : 1 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hM1 : 1 < M := by dsimp [M]; linarith [Real.pi_pos]
  have hsq : M < M ^ 2 := by nlinarith
  have hupper : v < typeBAreaAtRadius lam M := by nlinarith
  have hzero : typeBAreaAtRadius lam 0 = lam * Real.pi :=
    typeBAreaAtRadius_zero hlam0 hlam1
  have hvI : v ∈ Set.Icc (typeBAreaAtRadius lam 0)
      (typeBAreaAtRadius lam M) := by
    rw [hzero]
    exact ⟨hv.le, hupper.le⟩
  have him := intermediate_value_Icc hM0.le
    typeBAreaAtRadius_continuous.continuousOn hvI
  rcases him with ⟨R, hRI, harea⟩
  have hRpos : 0 < R := lt_of_le_of_ne hRI.1 fun hR0 => by
    subst R
    rw [hzero] at harea
    linarith
  exact ⟨R, hRpos, harea⟩

lemma exists_typeCRadius_at_area {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hv : lam * Real.pi < v) :
    ∃ R ∈ Set.Ioi 0, typeCAreaAtRadius lam R = v := by
  let M := (v + Real.pi + 1) / lam
  have hv0 : 0 < v := lt_trans (mul_pos hlam0 Real.pi_pos) hv
  have hnum0 : 0 < v + Real.pi + 1 := by positivity
  have hM0 : 0 < M := div_pos hnum0 hlam0
  have hlamSqOne : lam ^ 2 < 1 := by nlinarith
  have hlamM : lam < M := by
    dsimp [M]
    apply (lt_div_iff₀ hlam0).2
    nlinarith [Real.pi_pos]
  have hlower := typeCAreaAtRadius_large_lower hlam0 hlam1 hM0
  have hM1 : 1 < M := by
    dsimp [M]
    apply (lt_div_iff₀ hlam0).2
    linarith [Real.pi_pos]
  have hlamMval : lam * M = v + Real.pi + 1 := by
    dsimp [M]
    field_simp [hlam0.ne']
  have hpi1 : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hpiM : 1 < Real.pi * M := by
    nlinarith [mul_pos (sub_pos.mpr hpi1) (sub_pos.mpr hM1)]
  have hprod : v + Real.pi + 1 <
      (v + Real.pi + 1) * (Real.pi * M) := by
    simpa using mul_lt_mul_of_pos_left hpiM hnum0
  have hupper : v < typeCAreaAtRadius lam M := by
    have hrearr : lam * Real.pi * M ^ 2 =
        (lam * M) * (Real.pi * M) := by ring
    rw [hrearr, hlamMval] at hlower
    linarith
  have hlow := typeCAreaAtRadius_lt_full hlam0 hlam1 hlam0
  have hlamSq : Real.pi * lam ^ 2 < lam * Real.pi := by
    have hll : lam ^ 2 < lam := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hll Real.pi_pos]
  have hareaLam : typeCAreaAtRadius lam lam < v :=
    lt_trans hlow (lt_trans hlamSq hv)
  have hvI : v ∈ Set.Icc (typeCAreaAtRadius lam lam)
      (typeCAreaAtRadius lam M) := ⟨hareaLam.le, hupper.le⟩
  have hcont : ContinuousOn (typeCAreaAtRadius lam) (Set.Icc lam M) :=
    typeCAreaAtRadius_continuousOn.mono fun x hx =>
      lt_of_lt_of_le hlam0 hx.1
  have him := intermediate_value_Icc hlamM.le hcont hvI
  rcases him with ⟨R, hRI, harea⟩
  exact ⟨R, lt_of_lt_of_le hlam0 hRI.1, harea⟩

/-- Every type-(B) perimeter arising from an admissible candidate of exactly
weighted area `v`. -/
def typeBPerimeterValuesAtArea (lam v : ℝ) : Set ℝ :=
  { p | ∃ beta, BAdmissible lam beta ∧ typeBArea lam beta = v ∧
      typeBPerimeter lam beta = p }

/-- Every type-(C) perimeter arising from an admissible candidate of exactly
weighted area `v`. -/
def typeCPerimeterValuesAtArea (lam v : ℝ) : Set ℝ :=
  { p | ∃ beta, CAdmissible beta ∧ typeCArea lam beta = v ∧
      typeCPerimeter lam beta = p }

/-- The equal-area type-(B) profile.  On its geometric range the preceding
value set is proved to be a singleton, so this infimum is that unique value. -/
def typeBPerimeterAtArea (lam v : ℝ) : ℝ :=
  sInf (typeBPerimeterValuesAtArea lam v)

/-- The equal-area type-(C) profile.  On its geometric range the preceding
value set is proved to be a singleton, so this infimum is that unique value. -/
def typeCPerimeterAtArea (lam v : ℝ) : ℝ :=
  sInf (typeCPerimeterValuesAtArea lam v)

lemma typeBPerimeter_mem_values {lam v beta : ℝ}
    (hbeta : BAdmissible lam beta) (harea : typeBArea lam beta = v) :
    typeBPerimeter lam beta ∈ typeBPerimeterValuesAtArea lam v :=
  ⟨beta, hbeta, harea, rfl⟩

lemma typeCPerimeter_mem_values {lam v beta : ℝ}
    (hbeta : CAdmissible beta) (harea : typeCArea lam beta = v) :
    typeCPerimeter lam beta ∈ typeCPerimeterValuesAtArea lam v :=
  ⟨beta, hbeta, harea, rfl⟩

lemma typeB_values_eq_singleton {lam v beta : ℝ}
    (hbeta : BAdmissible lam beta) (harea : typeBArea lam beta = v)
    (hunique : ∀ beta', BAdmissible lam beta' → typeBArea lam beta' = v → beta' = beta) :
    typeBPerimeterValuesAtArea lam v = {typeBPerimeter lam beta} := by
  ext p
  constructor
  · rintro ⟨beta', hbeta', harea', rfl⟩
    simp [hunique beta' hbeta' harea']
  · intro hp
    have hp' : p = typeBPerimeter lam beta := by simpa using hp
    subst p
    exact typeBPerimeter_mem_values hbeta harea

lemma typeC_values_eq_singleton {lam v beta : ℝ}
    (hbeta : CAdmissible beta) (harea : typeCArea lam beta = v)
    (hunique : ∀ beta', CAdmissible beta' → typeCArea lam beta' = v → beta' = beta) :
    typeCPerimeterValuesAtArea lam v = {typeCPerimeter lam beta} := by
  ext p
  constructor
  · rintro ⟨beta', hbeta', harea', rfl⟩
    simp [hunique beta' hbeta' harea']
  · intro hp
    have hp' : p = typeCPerimeter lam beta := by simpa using hp
    subst p
    exact typeCPerimeter_mem_values hbeta harea

lemma typeBPerimeterAtArea_eq {lam v beta : ℝ}
    (hbeta : BAdmissible lam beta) (harea : typeBArea lam beta = v)
    (hunique : ∀ beta', BAdmissible lam beta' → typeBArea lam beta' = v → beta' = beta) :
    typeBPerimeterAtArea lam v = typeBPerimeter lam beta := by
  rw [typeBPerimeterAtArea, typeB_values_eq_singleton hbeta harea hunique]
  exact csInf_singleton _

lemma typeCPerimeterAtArea_eq {lam v beta : ℝ}
    (hbeta : CAdmissible beta) (harea : typeCArea lam beta = v)
    (hunique : ∀ beta', CAdmissible beta' → typeCArea lam beta' = v → beta' = beta) :
    typeCPerimeterAtArea lam v = typeCPerimeter lam beta := by
  rw [typeCPerimeterAtArea, typeC_values_eq_singleton hbeta harea hunique]
  exact csInf_singleton _

lemma existsUnique_typeBRadius_at_area {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hv : lam * Real.pi < v) :
    ∃! R, 0 < R ∧ typeBAreaAtRadius lam R = v := by
  rcases exists_typeBRadius_at_area hlam0 hlam1 hv with ⟨R, hR, harea⟩
  change 0 < R at hR
  refine ⟨R, ⟨hR, harea⟩, ?_⟩
  intro S hS
  have hSnonneg : S ∈ Set.Ici 0 := hS.1.le
  have hRnonneg : R ∈ Set.Ici 0 := hR.le
  apply (typeBAreaAtRadius_strictMonoOn hlam0 hlam1).injOn
    hSnonneg hRnonneg
  calc
    typeBAreaAtRadius lam S = v := hS.2
    _ = typeBAreaAtRadius lam R := harea.symm

lemma existsUnique_typeCRadius_at_area {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hv : lam * Real.pi < v) :
    ∃! R, 0 < R ∧ typeCAreaAtRadius lam R = v := by
  rcases exists_typeCRadius_at_area hlam0 hlam1 hv with ⟨R, hR, harea⟩
  change 0 < R at hR
  refine ⟨R, ⟨hR, harea⟩, ?_⟩
  intro S hS
  apply (typeCAreaAtRadius_strictMonoOn hlam0 hlam1).injOn hS.1 hR
  calc
    typeCAreaAtRadius lam S = v := hS.2
    _ = typeCAreaAtRadius lam R := harea.symm

lemma typeBPerimeterAtArea_eq_radius {lam v R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (harea : typeBAreaAtRadius lam R = v) :
    typeBPerimeterAtArea lam v = typeBPerimeterAtRadius lam R := by
  rw [typeBPerimeterAtArea_eq (betaAtRadius_admissible hlam0 hlam1 hR.le)
    ((typeBAreaAtRadius_agrees hlam0 hlam1 hR.le).symm.trans harea)]
  · exact (typeBPerimeterAtRadius_agrees hlam0 hlam1 hR.le).symm
  · intro beta' hbeta' harea'
    apply typeBRadius_injective_on_admissible hlam0 hlam1 hbeta'
      (betaAtRadius_admissible hlam0 hlam1 hR.le)
    have hR' := typeBRadius_nonneg hlam0 hlam1 hbeta'
    have hrEq : typeBRadius lam beta' = R := by
      apply (typeBAreaAtRadius_strictMonoOn hlam0 hlam1).injOn hR' hR.le
      rw [typeBAreaAtRadius_agrees hlam0 hlam1 hR',
        betaAtRadius_typeBRadius hlam0 hlam1 hbeta', harea', harea]
    rw [typeBRadius_betaAtRadius hlam0 hlam1 hR.le]
    exact hrEq

lemma typeCPerimeterAtArea_eq_radius {lam v R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (harea : typeCAreaAtRadius lam R = v) :
    typeCPerimeterAtArea lam v = typeCPerimeterAtRadius lam R := by
  rw [typeCPerimeterAtArea_eq (bAtRadius_admissible hR)
    ((typeCAreaAtRadius_agrees hR).symm.trans harea)]
  · exact (typeCPerimeterAtRadius_agrees hR).symm
  · intro beta' hbeta' harea'
    apply typeCRadius_injective_on_admissible hbeta'
      (bAtRadius_admissible hR)
    have hR' := typeCRadius_pos hbeta'
    have hrEq : typeCRadius beta' = R := by
      apply (typeCAreaAtRadius_strictMonoOn hlam0 hlam1).injOn hR' hR
      rw [typeCAreaAtRadius_agrees hR', bAtRadius_typeCRadius hbeta',
        harea', harea]
    rw [typeCRadius_bAtRadius hR]
    exact hrEq

lemma typeBPerimeterAtArea_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeBPerimeterAtArea lam) (Set.Ioi (lam * Real.pi)) := by
  intro v hv w hw hvw
  rcases exists_typeBRadius_at_area hlam0 hlam1 hv with ⟨R, hR, hareaR⟩
  rcases exists_typeBRadius_at_area hlam0 hlam1 hw with ⟨S, hS, hareaS⟩
  change 0 < R at hR
  change 0 < S at hS
  have hRS : R < S := by
    by_contra hn
    have hle : S ≤ R := le_of_not_gt hn
    have ha := (typeBAreaAtRadius_strictMonoOn hlam0 hlam1).monotoneOn
      hS.le hR.le hle
    rw [hareaS, hareaR] at ha
    linarith
  rw [typeBPerimeterAtArea_eq_radius hlam0 hlam1 hR hareaR,
    typeBPerimeterAtArea_eq_radius hlam0 hlam1 hS hareaS]
  exact typeBPerimeterAtRadius_strictMonoOn hlam0 hlam1 hR.le hS.le hRS

lemma typeCPerimeterAtArea_strictMonoOn {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictMonoOn (typeCPerimeterAtArea lam) (Set.Ioi (lam * Real.pi)) := by
  intro v hv w hw hvw
  rcases exists_typeCRadius_at_area hlam0 hlam1 hv with ⟨R, hR, hareaR⟩
  rcases exists_typeCRadius_at_area hlam0 hlam1 hw with ⟨S, hS, hareaS⟩
  change 0 < R at hR
  change 0 < S at hS
  have hRS : R < S := by
    by_contra hn
    have hle : S ≤ R := le_of_not_gt hn
    have ha := (typeCAreaAtRadius_strictMonoOn hlam0 hlam1).monotoneOn
      hS hR hle
    rw [hareaS, hareaR] at ha
    linarith
  rw [typeCPerimeterAtArea_eq_radius hlam0 hlam1 hR hareaR,
    typeCPerimeterAtArea_eq_radius hlam0 hlam1 hS hareaS]
  exact typeCPerimeterAtRadius_strictMonoOn hlam0 hlam1 hR hS hRS

/-- Half of the fixed-radius B-minus-C perimeter gap. -/
def fixedRadiusHalfGap (lam R : ℝ) : ℝ :=
  (lam - R) * betaAtRadius lam R + lam * Real.arccos lam +
    (1 - lam) * R * bAtRadius R

/-- The positive denominator in the density-ratio calculation. -/
def fixedRadiusD (lam R : ℝ) : ℝ :=
  (R - lam) ^ 2 + (1 - lam ^ 2)

/-- The derivative kernel used only on the nontrivial region `R > lam`. -/
def fixedRadiusL (lam R : ℝ) : ℝ :=
  betaAtRadius lam R - bAtRadius R -
    lam * Real.sqrt (1 - lam ^ 2) / fixedRadiusD lam R
/-- An exact counterexample to the false unrestricted sign assertion for
`fixedRadiusL`: its derivative kernel is positive in the `R < λ` branch. -/
lemma fixedRadiusL_positive_at_fifteen_sixteenths_half :
    0 < fixedRadiusL (15 / 16 : ℝ) (1 / 2 : ℝ) := by
  have hx0 : 0 < Real.sqrt (31 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hx_sq : Real.sqrt (31 : ℝ) ^ 2 = 31 :=
    Real.sq_sqrt (by norm_num)
  have hy0 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hy_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hx_gt : (7 : ℝ) / 2 < Real.sqrt 31 := by
    nlinarith [hx_sq]
  have hden : 0 < 2 * Real.sqrt 31 - 7 := by
    linarith
  have hx_lt_six : Real.sqrt 31 < 6 := by
    nlinarith [hx_sq]
  have hy_lt_two : Real.sqrt 3 < 2 := by
    nlinarith [hy_sq]
  have hsqrt :
      Real.sqrt (1 - (15 / 16 : ℝ) ^ 2) = Real.sqrt 31 / 16 := by
    rw [show 1 - (15 / 16 : ℝ) ^ 2 = (31 : ℝ) / 256 by norm_num]
    calc
      Real.sqrt ((31 : ℝ) / 256) =
          Real.sqrt ((Real.sqrt 31 / 16) ^ 2) := by
            congr 1
            rw [div_pow, hx_sq]
            norm_num
      _ = |Real.sqrt 31 / 16| := Real.sqrt_sq_eq_abs _
      _ = Real.sqrt 31 / 16 := abs_of_nonneg (by positivity)
  have hbeta :
      betaAtRadius (15 / 16 : ℝ) (1 / 2 : ℝ) =
        Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) := by
    unfold betaAtRadius
    rw [hsqrt]
    have hxne : Real.sqrt (31 : ℝ) ≠ 0 := hx0.ne'
    rw [show ((1 / 2 : ℝ) - 15 / 16) / (Real.sqrt 31 / 16) =
        -(7 / Real.sqrt 31) by field_simp [hxne] <;> ring,
      Real.arctan_neg]
    ring
  have hratio_lt : 7 / Real.sqrt (31 : ℝ) < 2 := by
    rw [div_lt_iff₀ hx0]
    linarith
  have hnum : 0 < 2 - 7 / Real.sqrt (31 : ℝ) := by
    linarith
  have hatan_lt :
      Real.arctan (7 / Real.sqrt 31) < Real.arctan 2 :=
    Real.arctan_strictMono hratio_lt
  have htheta_pos :
      0 < Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) - Real.arctan 2 := by
    have hatan_pos : 0 < Real.arctan (7 / Real.sqrt 31) :=
      Real.arctan_pos.2 (by positivity)
    linarith [Real.arctan_lt_pi_div_two 2]
  have htheta_lt :
      Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) - Real.arctan 2 <
        Real.pi / 2 := by
    linarith
  have htan :
      Real.tan (Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) -
          Real.arctan 2) =
        (Real.sqrt 31 + 14) / (2 * Real.sqrt 31 - 7) := by
    rw [show Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) -
        Real.arctan 2 =
        Real.pi / 2 - (Real.arctan 2 - Real.arctan (7 / Real.sqrt 31)) by
          ring,
      Real.tan_pi_div_two_sub,
      Real.tan_sub' ⟨Real.arctan_ne_mul_pi_div_two,
        Real.arctan_ne_mul_pi_div_two⟩,
      Real.tan_arctan, Real.tan_arctan]
    field_simp [hx0.ne', hden.ne', hnum.ne'] <;> ring
  have hproduct :
      Real.sqrt 3 * (2 * Real.sqrt 31 - 7) < Real.sqrt 31 + 14 := by
    have hmul : 0 < (2 - Real.sqrt 3) * (2 * Real.sqrt 31 - 7) :=
      mul_pos (sub_pos.mpr hy_lt_two) hden
    nlinarith
  have hquot : Real.sqrt 3 <
      (Real.sqrt 31 + 14) / (2 * Real.sqrt 31 - 7) :=
    (lt_div_iff₀ hden).2 hproduct
  have htheta_pi_div_three :
      Real.pi / 3 <
        Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) - Real.arctan 2 := by
    have htan_lt :
        Real.tan (Real.pi / 3) <
          Real.tan (Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) -
            Real.arctan 2) := by
      rw [Real.tan_pi_div_three, htan]
      exact hquot
    have harctan_lt := Real.arctan_strictMono htan_lt
    simpa only [Real.arctan_tan (x := Real.pi / 3)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      Real.arctan_tan (x := Real.pi / 2 +
        Real.arctan (7 / Real.sqrt 31) - Real.arctan 2)
      (by linarith [htheta_pos, Real.pi_pos])
      (by linarith [htheta_lt])] using harctan_lt
  have hx_lt : Real.sqrt 31 < (279 : ℝ) / 50 := by
    nlinarith [hx_sq]
  have hcorrection : 3 * Real.sqrt 31 / 16 < Real.pi / 3 := by
    nlinarith [Real.pi_gt_d2]
  have hL :
      fixedRadiusL (15 / 16 : ℝ) (1 / 2 : ℝ) =
        (Real.pi / 2 + Real.arctan (7 / Real.sqrt 31) - Real.arctan 2) -
          3 * Real.sqrt 31 / 16 := by
    unfold fixedRadiusL fixedRadiusD bAtRadius
    rw [hbeta, hsqrt]
    norm_num
    ring
  rw [hL]
  linarith

/-- The polynomial controlling the density derivative of `fixedRadiusL`. -/
def fixedRadiusN (lam R : ℝ) : ℝ :=
  R ^ 3 - 4 * R ^ 2 * lam + 2 * R * lam ^ 2 + 3 * R - 2 * lam

lemma fixedRadiusD_pos {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    0 < fixedRadiusD lam R := by
  unfold fixedRadiusD
  nlinarith [sq_nonneg (R - lam)]

lemma fixedRadiusN_density_derivative_identity (lam R : ℝ) :
    HasDerivAt (fun c => fixedRadiusN c R)
      (-(4 * (R - 1 / 2) ^ 2 + 1 + 4 * R * (1 - lam))) lam := by
  unfold fixedRadiusN
  convert (((((hasDerivAt_const lam (R ^ 3)).sub
    ((hasDerivAt_id lam).const_mul (4 * R ^ 2))).add
      (((hasDerivAt_id lam).pow 2).const_mul (2 * R))).add_const
        (3 * R)).sub ((hasDerivAt_id lam).const_mul 2)) using 1 <;>
    first | rfl | (simp only [id_eq] <;> ring)

lemma perimeter_gap_eq_two_mul_halfGap (lam R : ℝ) :
    typeBPerimeterAtRadius lam R - typeCPerimeterAtRadius lam R =
      2 * fixedRadiusHalfGap lam R := by
  unfold typeBPerimeterAtRadius typeCPerimeterAtRadius fixedRadiusHalfGap
  ring

lemma fixedRadiusHalfGap_pos_of_le {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR0 : 0 < R) (hR : R ≤ lam) :
    0 < fixedRadiusHalfGap lam R := by
  have hb := betaAtRadius_pos (R := R) hlam0 hlam1
  have hc := (bAtRadius_admissible hR0).1
  have ha : 0 < Real.arccos lam := Real.arccos_pos.2 hlam1
  have h1 : 0 ≤ (lam - R) * betaAtRadius lam R :=
    mul_nonneg (sub_nonneg.mpr hR) hb.le
  have h2 : 0 < lam * Real.arccos lam := mul_pos hlam0 ha
  have h3 : 0 < (1 - lam) * R * bAtRadius R :=
    mul_pos (mul_pos (sub_pos.mpr hlam1) hR0) hc
  unfold fixedRadiusHalfGap
  linarith

lemma sameRadius_typeB_gt_typeC_of_le {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR0 : 0 < R) (hR : R ≤ lam) :
    typeCPerimeterAtRadius lam R < typeBPerimeterAtRadius lam R := by
  have hgap := fixedRadiusHalfGap_pos_of_le hlam0 hlam1 hR0 hR
  rw [← sub_pos, perimeter_gap_eq_two_mul_halfGap]
  positivity

lemma fixedRadiusN_density_derivative_neg {lam R : ℝ}
    (hlam1 : lam < 1) (hR : 0 < R) :
    -(4 * (R - 1 / 2) ^ 2 + 1 + 4 * R * (1 - lam)) < 0 := by
  have : 0 < R * (1 - lam) := mul_pos hR (sub_pos.mpr hlam1)
  nlinarith [sq_nonneg (R - 1 / 2)]

lemma fixedRadiusN_diagonal (R : ℝ) :
    fixedRadiusN R R = R * (1 - R ^ 2) := by
  unfold fixedRadiusN
  ring

lemma fixedRadiusN_strictAntiOn {R : ℝ} (hR : 0 < R) :
    StrictAntiOn (fun c => fixedRadiusN c R) (Set.Iic 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _)
  · unfold fixedRadiusN
    fun_prop
  · intro c hc
    rw [interior_Iic] at hc
    rw [(fixedRadiusN_density_derivative_identity c R).deriv]
    exact fixedRadiusN_density_derivative_neg hc hR

lemma sqrt_one_sub_sq_hasDerivAt {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (fun c : ℝ => Real.sqrt (1 - c ^ 2))
      (-lam / Real.sqrt (1 - lam ^ 2)) lam := by
  have h := ((hasDerivAt_const lam 1).sub ((hasDerivAt_id lam).pow 2)).sqrt
    (ne_of_gt (show 0 < 1 - lam ^ 2 by nlinarith))
  convert h using 1 <;> first | rfl |
    (simp only [Pi.sub_apply, Pi.pow_apply, id_eq]; ring)

lemma betaAtRadius_density_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (fun c => betaAtRadius c R)
      ((1 - lam * R) /
        (Real.sqrt (1 - lam ^ 2) * fixedRadiusD lam R)) lam := by
  have hs := sqrt_one_sub_sq_pos hlam0 hlam1
  have hs2 := sq_sqrt_one_sub_sq hlam0 hlam1
  have hd := fixedRadiusD_pos (R := R) hlam0 hlam1
  have hq := ((hasDerivAt_const lam R).sub (hasDerivAt_id lam)).div
    (sqrt_one_sub_sq_hasDerivAt hlam0 hlam1) hs.ne'
  have hb := (hasDerivAt_const lam (Real.pi / 2)).sub hq.arctan
  convert hb using 1 <;> try rfl
  simp only [Pi.sub_apply, Pi.div_apply, id_eq]
  field_simp [hs.ne', hd.ne']
  unfold fixedRadiusD
  rw [hs2]
  ring

lemma fixedRadiusD_density_hasDerivAt (lam R : ℝ) :
    HasDerivAt (fun c => fixedRadiusD c R) (-2 * R) lam := by
  unfold fixedRadiusD
  convert (((hasDerivAt_const lam R).sub (hasDerivAt_id lam)).pow 2).add
    ((hasDerivAt_const lam 1).sub ((hasDerivAt_id lam).pow 2)) using 1 <;>
    first | rfl | (simp only [Pi.sub_apply, id_eq]; ring)

lemma fixedRadiusL_density_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (fun c => fixedRadiusL c R)
      (-lam * fixedRadiusN lam R /
        (Real.sqrt (1 - lam ^ 2) * fixedRadiusD lam R ^ 2)) lam := by
  have hs := sqrt_one_sub_sq_pos hlam0 hlam1
  have hs2 := sq_sqrt_one_sub_sq hlam0 hlam1
  have hd := fixedRadiusD_pos (R := R) hlam0 hlam1
  have h := ((betaAtRadius_density_hasDerivAt (R := R) hlam0 hlam1).sub_const
    (bAtRadius R)).sub
      (((hasDerivAt_id lam).mul (sqrt_one_sub_sq_hasDerivAt hlam0 hlam1)).div
        (fixedRadiusD_density_hasDerivAt lam R) hd.ne')
  convert h using 1 <;> try rfl
  simp only [Pi.mul_apply, id_eq]
  field_simp [hs.ne', hd.ne']
  unfold fixedRadiusD fixedRadiusN
  nlinarith [hs2]

lemma fixedRadiusHalfGap_density_ratio_hasDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasDerivAt (fun c => fixedRadiusHalfGap c R / c)
      (R / lam ^ 2 * fixedRadiusL lam R) lam := by
  have hs := sqrt_one_sub_sq_pos hlam0 hlam1
  have hs2 := sq_sqrt_one_sub_sq hlam0 hlam1
  have hd := fixedRadiusD_pos (R := R) hlam0 hlam1
  have hb := betaAtRadius_density_hasDerivAt (R := R) hlam0 hlam1
  have ha := Real.hasDerivAt_arccos (x := lam) (by linarith) (by linarith)
  have h := ((((hasDerivAt_id lam).sub_const R).mul hb).add
    ((hasDerivAt_id lam).mul ha)).add
      ((((hasDerivAt_const lam 1).sub (hasDerivAt_id lam)).mul_const R).mul_const
        (bAtRadius R))
  have hq := h.div (hasDerivAt_id lam) hlam0.ne'
  convert hq using 1 <;> try rfl
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  unfold fixedRadiusL
  field_simp [hs.ne', hd.ne', hlam0.ne']
  unfold fixedRadiusD
  linear_combination -R * lam * hs2

lemma fixedRadiusL_zero {R : ℝ} (hR : 0 < R) :
    fixedRadiusL 0 R = 0 := by
  simp only [fixedRadiusL, betaAtRadius, zero_pow (by decide : 2 ≠ 0),
    sub_zero, Real.sqrt_one, div_one, zero_mul, zero_div]
  rw [bAtRadius, one_div, Real.arctan_inv_of_pos hR]
  ring

lemma betaAtRadius_eq_arctan_reciprocal {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam < R) :
    betaAtRadius lam R = Real.arctan (Real.sqrt (1 - lam ^ 2) / (R - lam)) := by
  rw [betaAtRadius, ← Real.arctan_inv_of_pos
    (div_pos (sub_pos.mpr hR) (sqrt_one_sub_sq_pos hlam0 hlam1)), inv_div]

/-- The zero-density endpoint is nonsingular for every positive radius. -/
lemma fixedRadiusL_continuousAt_zero {R : ℝ} (hR : 0 < R) :
    ContinuousAt (fun c => fixedRadiusL c R) 0 := by
  have hs : Real.sqrt (1 - (0 : ℝ) ^ 2) ≠ 0 := by norm_num
  have hd : fixedRadiusD 0 R ≠ 0 := by
    unfold fixedRadiusD
    positivity
  unfold fixedRadiusL betaAtRadius
  apply ContinuousAt.sub
  · exact ((continuousAt_const.sub
      (Real.continuous_arctan.continuousAt.comp
        ((continuousAt_const.sub continuousAt_id).div
          (Real.continuous_sqrt.continuousAt.comp
            (continuousAt_const.sub (continuousAt_id.pow 2))) hs)))).sub
      continuousAt_const
  · apply ContinuousAt.div
    · fun_prop
    · unfold fixedRadiusD
      fun_prop
    · exact hd

/-- For `R > 1` the reciprocal chart supplies the exact left endpoint at density one. -/
lemma fixedRadiusL_tendsto_one {R : ℝ} (hR : 1 < R) :
    Filter.Tendsto (fun c => fixedRadiusL c R) (nhdsWithin 1 (Set.Iio 1))
      (nhds (-bAtRadius R)) := by
  have hb : ContinuousAt
      (fun c : ℝ => Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c))) 1 := by
    apply Real.continuous_arctan.continuousAt.comp
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact sub_ne_zero.mpr (ne_of_gt hR)
  have hd : fixedRadiusD 1 R ≠ 0 := by
    simp only [fixedRadiusD, one_pow, sub_self, add_zero]
    exact pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hR))
  have hc : ContinuousAt (fun c => c * Real.sqrt (1 - c ^ 2) / fixedRadiusD c R) 1 := by
    apply ContinuousAt.div
    · fun_prop
    · unfold fixedRadiusD
      fun_prop
    · exact hd
  have ht : Filter.Tendsto
      (fun c => Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c)) -
        bAtRadius R - c * Real.sqrt (1 - c ^ 2) / fixedRadiusD c R)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-bAtRadius R)) := by
    convert ((hb.sub (continuousAt_const (y := bAtRadius R))).sub hc).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio 1)) using 1 <;> first | rfl | simp
  have he : (fun c => fixedRadiusL c R) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      (fun c => Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c)) -
        bAtRadius R - c * Real.sqrt (1 - c ^ 2) / fixedRadiusD c R) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with c hc hc0
    rw [fixedRadiusL, betaAtRadius_eq_arctan_reciprocal hc0 hc (hc.trans hR)]
  simpa using ht.congr' he.symm

/-- This includes the stationary locus `N = 0`: `N` is strictly positive
strictly to its left, so `L` has already decreased from its zero endpoint. -/
lemma fixedRadiusL_neg_of_N_nonneg {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam < R)
    (hN : 0 ≤ fixedRadiusN lam R) :
    fixedRadiusL lam R < 0 := by
  have hR0 := hlam0.trans hR
  have hm : StrictAntiOn (fun c => fixedRadiusL c R) (Set.Icc 0 lam) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro c hc
      rcases eq_or_lt_of_le hc.1 with h | h
      · subst c
        exact (fixedRadiusL_continuousAt_zero hR0).continuousWithinAt
      · exact (fixedRadiusL_density_hasDerivAt h (hc.2.trans_lt hlam1)).continuousAt.continuousWithinAt
    · intro c hc
      rw [interior_Icc] at hc
      have hN' : 0 < fixedRadiusN c R :=
        hN.trans_lt (fixedRadiusN_strictAntiOn hR0
          (hc.2.le.trans hlam1.le) hlam1.le hc.2)
      rw [(fixedRadiusL_density_hasDerivAt hc.1 (hc.2.trans hlam1)).deriv]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hc.1) hN')
        (mul_pos (sqrt_one_sub_sq_pos hc.1 (hc.2.trans hlam1))
          (sq_pos_of_pos (fixedRadiusD_pos hc.1 (hc.2.trans hlam1))))
  have h := hm ⟨le_rfl, hlam0.le⟩ ⟨hlam0.le, le_rfl⟩ hlam0
  simpa only [fixedRadiusL_zero hR0] using h

lemma fixedRadiusN_pos_of_radius_le_one {lam R : ℝ}
    (hlam0 : 0 < lam) (hR : lam < R) (hR1 : R ≤ 1) :
    0 < fixedRadiusN lam R := by
  have hR0 := hlam0.trans hR
  have hd : 0 ≤ fixedRadiusN R R := by
    rw [fixedRadiusN_diagonal]
    exact mul_nonneg hR0.le (by nlinarith)
  exact hd.trans_lt (fixedRadiusN_strictAntiOn hR0 (hR.le.trans hR1) hR1 hR)

lemma fixedRadiusL_neg_of_N_neg {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 1 < R)
    (hN : fixedRadiusN lam R < 0) :
    fixedRadiusL lam R < 0 := by
  have hm : StrictMonoOn (fun c => fixedRadiusL c R) (Set.Ico lam 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
    · intro c hc
      exact (fixedRadiusL_density_hasDerivAt (hlam0.trans_le hc.1) hc.2).continuousAt.continuousWithinAt
    · intro c hc
      rw [interior_Ico] at hc
      have hc0 := hlam0.trans hc.1
      have hNc : fixedRadiusN c R < 0 :=
        (fixedRadiusN_strictAntiOn (by linarith) hlam1.le hc.2.le hc.1).trans hN
      rw [(fixedRadiusL_density_hasDerivAt hc0 hc.2).deriv]
      exact div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hc0) hNc)
        (mul_pos (sqrt_one_sub_sq_pos hc0 hc.2)
          (sq_pos_of_pos (fixedRadiusD_pos hc0 hc.2)))
  have hle : fixedRadiusL lam R ≤ -bAtRadius R := by
    apply ge_of_tendsto (fixedRadiusL_tendsto_one hR)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds hlam1)] with c hc hcL
    exact (hm ⟨le_rfl, hlam1⟩ ⟨hcL.le, hc⟩ hcL).le
  exact hle.trans_lt (neg_neg_of_pos (bAtRadius_admissible (by linarith)).1)

/-- The sign is deliberately restricted to `R > lam`; the retained exact
counterexample rules out removing this hypothesis. -/
lemma fixedRadiusL_neg {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam < R) :
    fixedRadiusL lam R < 0 := by
  by_cases hR1 : R ≤ 1
  · exact fixedRadiusL_neg_of_N_nonneg hlam0 hlam1 hR
      (fixedRadiusN_pos_of_radius_le_one hlam0 hR hR1).le
  · rcases le_or_gt 0 (fixedRadiusN lam R) with hN | hN
    · exact fixedRadiusL_neg_of_N_nonneg hlam0 hlam1 hR hN
    · exact fixedRadiusL_neg_of_N_neg hlam0 hlam1 (lt_of_not_ge hR1) hN

lemma fixedRadiusHalfGap_density_ratio_strictAntiOn {R : ℝ} (hR : 0 < R) :
    StrictAntiOn (fun c => fixedRadiusHalfGap c R / c) (Set.Ioo 0 (min 1 R)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro c hc
    exact (fixedRadiusHalfGap_density_ratio_hasDerivAt hc.1
      (hc.2.trans_le (min_le_left _ _))).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioo] at hc
    have hc1 := hc.2.trans_le (min_le_left 1 R)
    have hcR := hc.2.trans_le (min_le_right 1 R)
    rw [(fixedRadiusHalfGap_density_ratio_hasDerivAt hc.1 hc1).deriv]
    exact mul_neg_of_pos_of_neg (div_pos hR (sq_pos_of_pos hc.1))
      (fixedRadiusL_neg hc.1 hc1 hcR)

/-- The finite endpoint `c = R < 1` has a strictly positive gap. -/
lemma fixedRadiusHalfGap_diagonal (R : ℝ) :
    fixedRadiusHalfGap R R =
      R * Real.arccos R + (1 - R) * R * bAtRadius R := by
  simp [fixedRadiusHalfGap]

lemma fixedRadiusHalfGap_density_ratio_continuousAt {c R : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) :
    ContinuousAt (fun x => fixedRadiusHalfGap x R / x) c :=
  (fixedRadiusHalfGap_density_ratio_hasDerivAt hc0 hc1).continuousAt

lemma fixedRadiusHalfGap_density_ratio_tendsto_one_of_gt {R : ℝ} (hR : 1 < R) :
    Filter.Tendsto (fun c => fixedRadiusHalfGap c R / c)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hb : ContinuousAt
      (fun c : ℝ => Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c))) 1 := by
    apply Real.continuous_arctan.continuousAt.comp
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact sub_ne_zero.mpr (ne_of_gt hR)
  have ht : ContinuousAt (fun c : ℝ =>
      ((c - R) * Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c)) +
        c * Real.arccos c + (1 - c) * R * bAtRadius R) / c) 1 := by
    apply ContinuousAt.div
    · exact (((continuousAt_id.sub continuousAt_const).mul hb).add
        (continuousAt_id.mul Real.continuous_arccos.continuousAt)).add
        (((continuousAt_const.sub continuousAt_id).mul continuousAt_const).mul continuousAt_const)
    · exact continuousAt_id
    · norm_num
  have he : (fun c => fixedRadiusHalfGap c R / c) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      (fun c => ((c - R) * Real.arctan (Real.sqrt (1 - c ^ 2) / (R - c)) +
        c * Real.arccos c + (1 - c) * R * bAtRadius R) / c) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with c hc hc0
    rw [fixedRadiusHalfGap, betaAtRadius_eq_arctan_reciprocal hc0 hc (hc.trans hR)]
  have ht' := ht.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  simpa using ht'.congr' he.symm

/-- At the singular corner `R = 1`, the bounded angle is multiplied by
`1 - c`. Squeezing this product avoids assigning a spurious endpoint angle. -/
lemma fixedRadiusHalfGap_density_ratio_tendsto_one_at_one :
    Filter.Tendsto (fun c => fixedRadiusHalfGap c 1 / c)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  have hi : Filter.Tendsto (fun c : ℝ => c)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := nhdsWithin_le_nhds
  have hp : Filter.Tendsto (fun c => (1 - c) * betaAtRadius c 1)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    apply squeeze_zero' (g := fun c : ℝ => (1 - c) * (Real.pi / 2))
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with c hc hc0
      exact mul_nonneg (sub_nonneg.mpr hc.le) (betaAtRadius_pos hc0 hc).le
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with c hc hc0
      exact mul_le_mul_of_nonneg_left (betaAtRadius_le_pi_div_two hc0 hc hc.le)
        (sub_nonneg.mpr hc.le)
    · convert (tendsto_const_nhds.sub hi).mul_const (Real.pi / 2) using 1 <;>
        first | rfl | norm_num
  have ha : Filter.Tendsto (fun c : ℝ => Real.arccos c)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    convert Real.continuous_arccos.continuousAt.tendsto.comp hi using 1 <;>
      first | rfl | simp
  have ht := ((hp.neg.add (hi.mul ha)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hi).mul_const (bAtRadius 1))).div hi
      (by norm_num)
  convert ht using 1
  · funext c
    unfold fixedRadiusHalfGap
    simp only [Pi.div_apply]
    ring
  · norm_num

lemma fixedRadiusHalfGap_density_ratio_tendsto_one {R : ℝ} (hR : 1 ≤ R) :
    Filter.Tendsto (fun c => fixedRadiusHalfGap c R / c)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
  rcases eq_or_lt_of_le hR with h | h
  · subst R
    exact fixedRadiusHalfGap_density_ratio_tendsto_one_at_one
  · exact fixedRadiusHalfGap_density_ratio_tendsto_one_of_gt h

lemma fixedRadiusHalfGap_pos_of_lt_radius_lt_one {lam R : ℝ}
    (hlam0 : 0 < lam) (hR : lam < R) (hR1 : R < 1) :
    0 < fixedRadiusHalfGap lam R := by
  have hR0 := hlam0.trans hR
  have hm : StrictAntiOn (fun c => fixedRadiusHalfGap c R / c) (Set.Ioc 0 R) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
    · intro c hc
      exact (fixedRadiusHalfGap_density_ratio_continuousAt hc.1
        (hc.2.trans_lt hR1)).continuousWithinAt
    · intro c hc
      rw [interior_Ioc] at hc
      have hc1 := hc.2.trans hR1
      rw [(fixedRadiusHalfGap_density_ratio_hasDerivAt hc.1 hc1).deriv]
      exact mul_neg_of_pos_of_neg (div_pos hR0 (sq_pos_of_pos hc.1))
        (fixedRadiusL_neg hc.1 hc1 hc.2)
  have hpos : 0 < fixedRadiusHalfGap R R / R :=
    div_pos (fixedRadiusHalfGap_pos_of_le hR0 hR1 hR0 le_rfl) hR0
  have hlt := hm ⟨hlam0, hR.le⟩ ⟨hR0, le_rfl⟩ hR
  exact (div_pos_iff_of_pos_right hlam0).mp (hpos.trans hlt)

lemma fixedRadiusHalfGap_pos_of_one_le_radius {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 1 ≤ R) :
    0 < fixedRadiusHalfGap lam R := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hm : StrictAntiOn (fun c => fixedRadiusHalfGap c R / c) (Set.Ioo 0 1) := by
    simpa only [min_eq_left hR] using fixedRadiusHalfGap_density_ratio_strictAntiOn hR0
  obtain ⟨c, hlc, hc1⟩ := exists_between hlam1
  have hc0 := hlam0.trans hlc
  have hnonneg : 0 ≤ fixedRadiusHalfGap c R / c := by
    apply le_of_tendsto (fixedRadiusHalfGap_density_ratio_tendsto_one hR)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds hc1)] with x hx hcx
    exact (hm ⟨hc0, hc1⟩ ⟨hc0.trans hcx, hx⟩ hcx).le
  have hlt := hm ⟨hlam0, hlam1⟩ ⟨hc0, hc1⟩ hlc
  exact (div_pos_iff_of_pos_right hlam0).mp (hnonneg.trans_lt hlt)

/-- The hard fixed-radius inequality, proved through the density ratio.
The endpoint split covers radii arbitrarily close to `lam`, `R = 1`,
and all `R > 1`, without a uniform margin assumption. -/
lemma fixedRadiusHalfGap_pos_of_gt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : lam < R) :
    0 < fixedRadiusHalfGap lam R := by
  rcases lt_or_ge R 1 with h | h
  · exact fixedRadiusHalfGap_pos_of_lt_radius_lt_one hlam0 hR h
  · exact fixedRadiusHalfGap_pos_of_one_le_radius hlam0 hlam1 h

/-- Global comparison of the faithful radius-coordinate candidates.
This is an analytic perimeter theorem; no finite-perimeter classification
or equal-area profile-transfer premise is used. -/
theorem sameRadius_typeB_gt_typeC {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    typeCPerimeterAtRadius lam R < typeBPerimeterAtRadius lam R := by
  rcases le_or_gt R lam with h | h
  · exact sameRadius_typeB_gt_typeC_of_le hlam0 hlam1 hR h
  · rw [← sub_pos, perimeter_gap_eq_two_mul_halfGap]
    exact mul_pos (by norm_num) (fixedRadiusHalfGap_pos_of_gt hlam0 hlam1 h)





/-- The exact common-perimeter differential mechanism.  If `radiusB p` and
`radiusC p` are the radii realizing the same perimeter `p`, the first
variation identities make the derivative of the area gap equal to their
difference.  A strict radius order therefore makes that gap strictly
decreasing, by the kernel-checked mean-value theorem. -/
lemma commonPerimeterGap_strictAnti
    {areaB areaC radiusB radiusC : ℝ → ℝ}
    (hderiv : ∀ p, HasDerivAt
      (fun q => areaB (radiusB q) - areaC (radiusC q))
      (radiusB p - radiusC p) p)
    (hradius : ∀ p, radiusB p < radiusC p) :
    StrictAnti (fun p => areaB (radiusB p) - areaC (radiusC p)) :=
  strictAnti_of_hasDerivAt_neg hderiv fun p => by
    linarith [hradius p]

/-- Converts a strictly decreasing common-perimeter area gap into the strict
profile conclusion.  The two bridge hypotheses are the only family-specific
steps: they identify the profile comparison with the common-perimeter area
gap and convert a negative gap back to a perimeter comparison. -/
lemma profile_persistence_of_commonPerimeter
    {profileB profileC gap : ℝ → ℝ}
    (hB : StrictMono profileB)
    (hgap : StrictAnti gap)
    (gap_at_initial_of_profile_le :
      ∀ v₀, profileC v₀ ≤ profileB v₀ → gap (profileB v₀) ≤ 0)
    (profile_lt_of_gap_neg :
      ∀ v, gap (profileB v) < 0 → profileC v < profileB v)
    {v₀ v : ℝ} (hv : v₀ < v)
    (hinitial : profileC v₀ ≤ profileB v₀) :
    profileC v < profileB v := by
  have hp : profileB v₀ < profileB v := hB hv
  have hgap_lt : gap (profileB v) < gap (profileB v₀) := hgap hp
  have hgap_nonpos : gap (profileB v₀) ≤ 0 :=
    gap_at_initial_of_profile_le v₀ hinitial
  exact profile_lt_of_gap_neg v (lt_of_lt_of_le hgap_lt hgap_nonpos)
/-- The open common-perimeter domain.  Its subtype excludes the degenerate
endpoint instead of assigning an inverse radius there. -/
def CommonPerimeter (lam : ℝ) : Type :=
  {p : ℝ // 2 * lam * Real.pi < p}

instance commonPerimeterLinearOrder (lam : ℝ) :
    LinearOrder (CommonPerimeter lam) :=
  inferInstanceAs (LinearOrder {p : ℝ // 2 * lam * Real.pi < p})

/-- Every positive type-(C) radius has perimeter strictly larger than `π R`.
This supplies the unbounded endpoint needed for the common-perimeter inverse. -/
lemma typeCPerimeterAtRadius_gt_pi_mul_radius {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    Real.pi * R < typeCPerimeterAtRadius lam R := by
  rw [typeCPerimeterAtRadius]
  have hb := bAtRadius_admissible hR
  have hfactor : Real.pi / 2 < Real.pi - (1 - lam) * bAtRadius R := by
    have hweight : (1 - lam) * bAtRadius R < Real.pi / 2 := by
      nlinarith [hb.2, hlam0, hlam1, Real.pi_pos]
    linarith
  nlinarith

/-- A type-(B) radius exists uniquely at every genuine common perimeter. -/
lemma existsUnique_typeBRadius_at_perimeter {lam p : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hp : 2 * lam * Real.pi < p) :
    ∃! R, 0 < R ∧ typeBPerimeterAtRadius lam R = p := by
  have hp0 : 0 < p := by nlinarith [Real.pi_pos]
  let M := p / Real.pi
  have hM0 : 0 < M := div_pos hp0 Real.pi_pos
  have hBM : p < typeBPerimeterAtRadius lam M := by
    have hC := typeCPerimeterAtRadius_gt_pi_mul_radius hlam0 hlam1 hM0
    have hBC := sameRadius_typeB_gt_typeC hlam0 hlam1 hM0
    dsimp [M] at hC hBC ⊢
    have hpi : Real.pi * (p / Real.pi) = p := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hpi] at hC
    exact hC.trans hBC
  have hB0 : typeBPerimeterAtRadius lam 0 < p := by
    rw [typeBPerimeterAtRadius_zero hlam0 hlam1]
    exact hp
  have hvalue : p ∈ Set.Icc (typeBPerimeterAtRadius lam 0)
      (typeBPerimeterAtRadius lam M) := ⟨hB0.le, hBM.le⟩
  rcases intermediate_value_Icc hM0.le
      typeBPerimeterAtRadius_continuous.continuousOn hvalue with ⟨R, hR, hperim⟩
  have hR0 : 0 < R := by
    rcases hR.1.eq_or_lt with hzero | hpos
    · rw [← hzero, typeBPerimeterAtRadius_zero hlam0 hlam1] at hperim
      linarith
    · exact hpos
  refine ⟨R, ⟨hR0, hperim⟩, ?_⟩
  intro S hS
  apply (typeBPerimeterAtRadius_strictMonoOn hlam0 hlam1).injOn hS.1.le hR0.le
  rw [hS.2, hperim]

/-- A type-(C) radius exists uniquely at every genuine common perimeter. -/
lemma existsUnique_typeCRadius_at_perimeter {lam p : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hp : 2 * lam * Real.pi < p) :
    ∃! R, 0 < R ∧ typeCPerimeterAtRadius lam R = p := by
  have hp0 : 0 < p := by nlinarith [Real.pi_pos]
  let M := p / Real.pi
  have hM0 : 0 < M := div_pos hp0 Real.pi_pos
  have hCM : p < typeCPerimeterAtRadius lam M := by
    have hC := typeCPerimeterAtRadius_gt_pi_mul_radius hlam0 hlam1 hM0
    dsimp [M] at hC ⊢
    have hpi : Real.pi * (p / Real.pi) = p := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hpi] at hC
    exact hC
  have hCl : typeCPerimeterAtRadius lam lam < p := by
    rw [typeCPerimeterAtRadius]
    have hb := bAtRadius_admissible hlam0
    have hfactor : Real.pi - (1 - lam) * bAtRadius lam < Real.pi := by
      have hpositive : 0 < (1 - lam) * bAtRadius lam :=
        mul_pos (by linarith) hb.1
      linarith
    nlinarith
  have hMl : lam < M := by
    dsimp [M]
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_pos]
  have hvalue : p ∈ Set.Icc (typeCPerimeterAtRadius lam lam)
      (typeCPerimeterAtRadius lam M) := ⟨hCl.le, hCM.le⟩
  have hcont : ContinuousOn (typeCPerimeterAtRadius lam) (Set.Icc lam M) :=
    typeCPerimeterAtRadius_continuousOn.mono fun x hx => hlam0.trans_le hx.1
  rcases intermediate_value_Icc hMl.le hcont hvalue with ⟨R, hR, hperim⟩
  have hR0 : 0 < R := hlam0.trans_le hR.1
  refine ⟨R, ⟨hR0, hperim⟩, ?_⟩
  intro S hS
  apply (typeCPerimeterAtRadius_strictMonoOn hlam0 hlam1).injOn hS.1 hR0
  rw [hS.2, hperim]

/-- The type-(B) common-perimeter inverse carries both positivity and its
defining equation in its codomain; there is no value outside the open domain. -/
def typeBRadiusAtPerimeter {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) :
    {R : ℝ // 0 < R ∧ typeBPerimeterAtRadius lam R = p.1} :=
  ⟨(existsUnique_typeBRadius_at_perimeter hlam.1 hlam.2 p.2).choose,
    (existsUnique_typeBRadius_at_perimeter hlam.1 hlam.2 p.2).choose_spec.1⟩

/-- The type-(C) common-perimeter inverse carries both positivity and its
defining equation in its codomain; there is no value outside the open domain. -/
def typeCRadiusAtPerimeter {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) :
    {R : ℝ // 0 < R ∧ typeCPerimeterAtRadius lam R = p.1} :=
  ⟨(existsUnique_typeCRadius_at_perimeter hlam.1 hlam.2 p.2).choose,
    (existsUnique_typeCRadius_at_perimeter hlam.1 hlam.2 p.2).choose_spec.1⟩

lemma typeBRadiusAtPerimeter_pos {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) :
    0 < (typeBRadiusAtPerimeter hlam p).1 :=
  (typeBRadiusAtPerimeter hlam p).2.1

lemma typeCRadiusAtPerimeter_pos {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) :
    0 < (typeCRadiusAtPerimeter hlam p).1 :=
  (typeCRadiusAtPerimeter hlam p).2.1

lemma typeBPerimeterAt_typeBRadiusAtPerimeter {lam : ℝ}
    (hlam : AdmissibleDensity lam) (p : CommonPerimeter lam) :
    typeBPerimeterAtRadius lam (typeBRadiusAtPerimeter hlam p) = p.1 :=
  (typeBRadiusAtPerimeter hlam p).2.2

lemma typeCPerimeterAt_typeCRadiusAtPerimeter {lam : ℝ}
    (hlam : AdmissibleDensity lam) (p : CommonPerimeter lam) :
    typeCPerimeterAtRadius lam (typeCRadiusAtPerimeter hlam p) = p.1 :=
  (typeCRadiusAtPerimeter hlam p).2.2

/-- Right uniqueness of the B inverse on its positive radius chart. -/
lemma typeBRadiusAtPerimeter_unique {lam R : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) (hR : 0 < R)
    (hperim : typeBPerimeterAtRadius lam R = p.1) :
    (typeBRadiusAtPerimeter hlam p).1 = R :=
  (existsUnique_typeBRadius_at_perimeter hlam.1 hlam.2 p.2).unique
    (typeBRadiusAtPerimeter hlam p).2 ⟨hR, hperim⟩

/-- Right uniqueness of the C inverse on its positive radius chart. -/
lemma typeCRadiusAtPerimeter_unique {lam R : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) (hR : 0 < R)
    (hperim : typeCPerimeterAtRadius lam R = p.1) :
    (typeCRadiusAtPerimeter hlam p).1 = R :=
  (existsUnique_typeCRadius_at_perimeter hlam.1 hlam.2 p.2).unique
    (typeCRadiusAtPerimeter hlam p).2 ⟨hR, hperim⟩

/-- At common perimeter, the global same-radius inequality forces the B
radius strictly below the C radius. -/
theorem typeBRadiusAtPerimeter_lt_typeCRadiusAtPerimeter {lam : ℝ}
    (hlam : AdmissibleDensity lam) (p : CommonPerimeter lam) :
    (typeBRadiusAtPerimeter hlam p).1 < (typeCRadiusAtPerimeter hlam p).1 := by
  by_contra hnot
  have hle : (typeCRadiusAtPerimeter hlam p).1 ≤
      (typeBRadiusAtPerimeter hlam p).1 := le_of_not_gt hnot
  have hmono := (typeCPerimeterAtRadius_strictMonoOn hlam.1 hlam.2).monotoneOn
  have hperim_le : typeCPerimeterAtRadius lam (typeCRadiusAtPerimeter hlam p) ≤
      typeCPerimeterAtRadius lam (typeBRadiusAtPerimeter hlam p) :=
    hmono (typeCRadiusAtPerimeter_pos hlam p) (typeBRadiusAtPerimeter_pos hlam p) hle
  rw [typeCPerimeterAt_typeCRadiusAtPerimeter hlam p] at hperim_le
  have hgap := sameRadius_typeB_gt_typeC hlam.1 hlam.2
    (typeBRadiusAtPerimeter_pos hlam p)
  rw [typeBPerimeterAt_typeBRadiusAtPerimeter hlam p] at hgap
  linarith

/-- Both common-perimeter inverse radii strictly increase with the perimeter. -/
lemma typeBRadiusAtPerimeter_strictMono {lam : ℝ} (hlam : AdmissibleDensity lam) :
    StrictMono fun p : CommonPerimeter lam => (typeBRadiusAtPerimeter hlam p).1 := by
  intro p q hpq
  have hpq' : p.1 < q.1 := hpq
  by_contra hnot
  have hle : (typeBRadiusAtPerimeter hlam q).1 ≤
      (typeBRadiusAtPerimeter hlam p).1 := le_of_not_gt hnot
  have hmono := (typeBPerimeterAtRadius_strictMonoOn hlam.1 hlam.2).monotoneOn
  have hperim : typeBPerimeterAtRadius lam (typeBRadiusAtPerimeter hlam q) ≤
      typeBPerimeterAtRadius lam (typeBRadiusAtPerimeter hlam p) :=
    hmono (typeBRadiusAtPerimeter_pos hlam q).le
      (typeBRadiusAtPerimeter_pos hlam p).le hle
  rw [typeBPerimeterAt_typeBRadiusAtPerimeter hlam q,
    typeBPerimeterAt_typeBRadiusAtPerimeter hlam p] at hperim
  exact (not_lt_of_ge hperim) hpq'

lemma typeCRadiusAtPerimeter_strictMono {lam : ℝ} (hlam : AdmissibleDensity lam) :
    StrictMono fun p : CommonPerimeter lam => (typeCRadiusAtPerimeter hlam p).1 := by
  intro p q hpq
  have hpq' : p.1 < q.1 := hpq
  by_contra hnot
  have hle : (typeCRadiusAtPerimeter hlam q).1 ≤
      (typeCRadiusAtPerimeter hlam p).1 := le_of_not_gt hnot
  have hmono := (typeCPerimeterAtRadius_strictMonoOn hlam.1 hlam.2).monotoneOn
  have hperim : typeCPerimeterAtRadius lam (typeCRadiusAtPerimeter hlam q) ≤
      typeCPerimeterAtRadius lam (typeCRadiusAtPerimeter hlam p) :=
    hmono (typeCRadiusAtPerimeter_pos hlam q)
      (typeCRadiusAtPerimeter_pos hlam p) hle
  rw [typeCPerimeterAt_typeCRadiusAtPerimeter hlam q,
    typeCPerimeterAt_typeCRadiusAtPerimeter hlam p] at hperim
  exact (not_lt_of_ge hperim) hpq'

/-- Any local real-valued realization of the B inverse has the reciprocal
perimeter derivative.  The statement is local, so no off-domain extension is
introduced for the genuine subtype inverse. -/
lemma typeB_local_inverse_hasDerivAt {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) {g : ℝ → ℝ}
    (hgvalue : g p.1 = typeBRadiusAtPerimeter hlam p)
    (hg : ContinuousAt g p.1)
    (hlocal : ∀ᶠ q in nhds p.1, typeBPerimeterAtRadius lam (g q) = q) :
    HasDerivAt g
      (2 * (Real.pi - betaAtRadius lam (typeBRadiusAtPerimeter hlam p) +
        Real.sin (betaAtRadius lam (typeBRadiusAtPerimeter hlam p)) *
          Real.cos (betaAtRadius lam (typeBRadiusAtPerimeter hlam p))))⁻¹ p.1 := by
  rw [← hgvalue]
  apply HasDerivAt.of_local_left_inverse hg
    (typeBPerimeterAtRadius_hasDerivAt hlam.1 hlam.2)
  · have hpos := typeBPerimeterAtRadius_deriv_pos (R := g p.1) hlam.1 hlam.2
      (by rw [hgvalue]; exact typeBRadiusAtPerimeter_pos hlam p)
    rw [(typeBPerimeterAtRadius_hasDerivAt hlam.1 hlam.2).deriv] at hpos
    exact ne_of_gt hpos
  · exact hlocal

/-- Any local real-valued realization of the C inverse has the reciprocal
perimeter derivative, again without defining an off-domain inverse value. -/
lemma typeC_local_inverse_hasDerivAt {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) {g : ℝ → ℝ}
    (hgvalue : g p.1 = typeCRadiusAtPerimeter hlam p)
    (hg : ContinuousAt g p.1)
    (hlocal : ∀ᶠ q in nhds p.1, typeCPerimeterAtRadius lam (g q) = q) :
    HasDerivAt g
      (2 * (Real.pi - (1 - lam) *
        (bAtRadius (typeCRadiusAtPerimeter hlam p) -
          Real.sin (bAtRadius (typeCRadiusAtPerimeter hlam p)) *
            Real.cos (bAtRadius (typeCRadiusAtPerimeter hlam p)))))⁻¹ p.1 := by
  rw [← hgvalue]
  apply HasDerivAt.of_local_left_inverse hg
    (typeCPerimeterAtRadius_hasDerivAt (by
      rw [hgvalue]
      exact typeCRadiusAtPerimeter_pos hlam p))
  · have hpos := typeCPerimeterAtRadius_deriv_pos (R := g p.1) hlam.1 hlam.2
      (by rw [hgvalue]; exact typeCRadiusAtPerimeter_pos hlam p)
    rw [(typeCPerimeterAtRadius_hasDerivAt
      (by rw [hgvalue]; exact typeCRadiusAtPerimeter_pos hlam p)).deriv] at hpos
    exact ne_of_gt hpos
  · exact hlocal


/-- The B perimeter has a strict derivative on its radius chart.  This is the
local input needed to invoke the one-dimensional inverse function theorem. -/
lemma typeBPerimeterAtRadius_hasStrictDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    HasStrictDerivAt (typeBPerimeterAtRadius lam)
      (2 * (Real.pi - betaAtRadius lam R +
        Real.sin (betaAtRadius lam R) * Real.cos (betaAtRadius lam R))) R := by
  let d : ℝ → ℝ := fun x =>
    2 * (Real.pi - betaAtRadius lam x +
      Real.sin (betaAtRadius lam x) * Real.cos (betaAtRadius lam x))
  have hstrict : HasStrictDerivAt (typeBPerimeterAtRadius lam) (d R) R := by
    apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    · exact Filter.Eventually.of_forall fun x =>
        typeBPerimeterAtRadius_hasDerivAt (R := x) hlam0 hlam1
    · have hb : ContinuousAt (betaAtRadius lam) R :=
        (betaAtRadius_hasDerivAt hlam0 hlam1).continuousAt
      fun_prop
  exact hstrict

/-- The C perimeter has a strict derivative at every positive radius. -/
lemma typeCPerimeterAtRadius_hasStrictDerivAt {lam R : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hR : 0 < R) :
    HasStrictDerivAt (typeCPerimeterAtRadius lam)
      (2 * (Real.pi - (1 - lam) *
        (bAtRadius R - Real.sin (bAtRadius R) * Real.cos (bAtRadius R)))) R := by
  let d : ℝ → ℝ := fun x =>
    2 * (Real.pi - (1 - lam) *
      (bAtRadius x - Real.sin (bAtRadius x) * Real.cos (bAtRadius x)))
  have hstrict : HasStrictDerivAt (typeCPerimeterAtRadius lam) (d R) R := by
    apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    · filter_upwards [eventually_gt_nhds hR] with x hx
      exact typeCPerimeterAtRadius_hasDerivAt hx
    · have hb : ContinuousAt bAtRadius R :=
        (bAtRadius_hasDerivAt hR.ne').continuousAt
      fun_prop
  exact hstrict

/-- The concrete B-minus-C area gap at a genuine common perimeter. -/
def commonPerimeterAreaGap {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) : ℝ :=
  typeBAreaAtRadius lam (typeBRadiusAtPerimeter hlam p) -
    typeCAreaAtRadius lam (typeCRadiusAtPerimeter hlam p)

/-- A local real representative of the genuine common-perimeter gap exists at
every point.  It agrees locally with the subtype-valued inverse construction
and has derivative `r_B - r_C`; no value of either inverse is assigned outside
the genuine perimeter domain. -/
lemma commonPerimeterAreaGap_local_hasDerivAt {lam : ℝ}
    (hlam : AdmissibleDensity lam) (p : CommonPerimeter lam) :
    ∃ gap : ℝ → ℝ,
      HasDerivAt gap
        ((typeBRadiusAtPerimeter hlam p).1 -
          (typeCRadiusAtPerimeter hlam p).1) p.1 ∧
      ∀ᶠ q in nhds p.1, ∀ hq : 2 * lam * Real.pi < q,
        gap q = commonPerimeterAreaGap hlam ⟨q, hq⟩ := by
  let RB : ℝ := typeBRadiusAtPerimeter hlam p
  let RC : ℝ := typeCRadiusAtPerimeter hlam p
  let dB : ℝ := 2 * (Real.pi - betaAtRadius lam RB +
    Real.sin (betaAtRadius lam RB) * Real.cos (betaAtRadius lam RB))
  let dC : ℝ := 2 * (Real.pi - (1 - lam) *
    (bAtRadius RC - Real.sin (bAtRadius RC) * Real.cos (bAtRadius RC)))
  have hPB : HasStrictDerivAt (typeBPerimeterAtRadius lam) dB RB := by
    dsimp [dB, RB]
    exact typeBPerimeterAtRadius_hasStrictDerivAt hlam.1 hlam.2
  have hPC : HasStrictDerivAt (typeCPerimeterAtRadius lam) dC RC := by
    dsimp [dC, RC]
    exact typeCPerimeterAtRadius_hasStrictDerivAt hlam.1 hlam.2
      (typeCRadiusAtPerimeter_pos hlam p)
  have hdB : dB ≠ 0 := by
    have hpos := typeBPerimeterAtRadius_deriv_pos
      (R := RB) hlam.1 hlam.2 (typeBRadiusAtPerimeter_pos hlam p)
    rw [hPB.hasDerivAt.deriv] at hpos
    exact ne_of_gt hpos
  have hdC : dC ≠ 0 := by
    have hpos := typeCPerimeterAtRadius_deriv_pos
      (R := RC) hlam.1 hlam.2 (typeCRadiusAtPerimeter_pos hlam p)
    rw [hPC.hasDerivAt.deriv] at hpos
    exact ne_of_gt hpos
  let gB : ℝ → ℝ := hPB.localInverse (typeBPerimeterAtRadius lam) dB RB hdB
  let gC : ℝ → ℝ := hPC.localInverse (typeCPerimeterAtRadius lam) dC RC hdC
  have hpB : typeBPerimeterAtRadius lam RB = p.1 := by
    exact typeBPerimeterAt_typeBRadiusAtPerimeter hlam p
  have hpC : typeCPerimeterAtRadius lam RC = p.1 := by
    exact typeCPerimeterAt_typeCRadiusAtPerimeter hlam p
  have hgB : HasDerivAt gB dB⁻¹ p.1 := by
    rw [← hpB]
    exact hPB.to_localInverse hdB |>.hasDerivAt
  have hgC : HasDerivAt gC dC⁻¹ p.1 := by
    rw [← hpC]
    exact hPC.to_localInverse hdC |>.hasDerivAt
  have hgBval : gB p.1 = RB := by
    rw [← hpB]
    exact (hPB.eventually_left_inverse hdB).self_of_nhds
  have hgCval : gC p.1 = RC := by
    rw [← hpC]
    exact (hPC.eventually_left_inverse hdC).self_of_nhds
  have hAB : HasDerivAt (typeBAreaAtRadius lam) (RB * dB) RB := by
    dsimp [RB, dB]
    exact typeBAreaAtRadius_hasDerivAt hlam.1 hlam.2
      (typeBRadiusAtPerimeter_pos hlam p)
  have hAC : HasDerivAt (typeCAreaAtRadius lam) (RC * dC) RC := by
    dsimp [RC, dC]
    exact typeCAreaAtRadius_hasDerivAt (lam := lam)
      (typeCRadiusAtPerimeter_pos hlam p)
  have hABcomp : HasDerivAt (typeBAreaAtRadius lam ∘ gB) RB p.1 := by
    have hAB' : HasDerivAt (typeBAreaAtRadius lam) (RB * dB) (gB p.1) := by
      rw [hgBval]
      exact hAB
    have h := hAB'.comp p.1 hgB
    have hcoef : RB * dB * dB⁻¹ = RB := by
      field_simp [hdB]
    rwa [hcoef] at h
  have hACcomp : HasDerivAt (typeCAreaAtRadius lam ∘ gC) RC p.1 := by
    have hAC' : HasDerivAt (typeCAreaAtRadius lam) (RC * dC) (gC p.1) := by
      rw [hgCval]
      exact hAC
    have h := hAC'.comp p.1 hgC
    have hcoef : RC * dC * dC⁻¹ = RC := by
      field_simp [hdC]
    rwa [hcoef] at h
  refine ⟨(typeBAreaAtRadius lam ∘ gB) -
      (typeCAreaAtRadius lam ∘ gC), ?_, ?_⟩
  · change HasDerivAt
      ((typeBAreaAtRadius lam ∘ gB) -
        (typeCAreaAtRadius lam ∘ gC)) (RB - RC) p.1
    exact hABcomp.sub hACcomp
  have hrightB := hPB.eventually_right_inverse hdB
  have hrightC := hPC.eventually_right_inverse hdC
  rw [hpB] at hrightB
  rw [hpC] at hrightC
  have hposB : ∀ᶠ q in nhds p.1, 0 < gB q :=
    hgB.continuousAt.eventually (Ioi_mem_nhds (by
      rw [hgBval]
      exact typeBRadiusAtPerimeter_pos hlam p))
  have hposC : ∀ᶠ q in nhds p.1, 0 < gC q :=
    hgC.continuousAt.eventually (Ioi_mem_nhds (by
      rw [hgCval]
      exact typeCRadiusAtPerimeter_pos hlam p))
  filter_upwards [hrightB, hrightC, hposB, hposC] with q hqB hqC hqBpos hqCpos
  intro hq
  let qs : CommonPerimeter lam := ⟨q, hq⟩
  have heqB : (typeBRadiusAtPerimeter hlam qs).1 = gB q :=
    typeBRadiusAtPerimeter_unique hlam qs hqBpos hqB
  have heqC : (typeCRadiusAtPerimeter hlam qs).1 = gC q :=
    typeCRadiusAtPerimeter_unique hlam qs hqCpos hqC
  change typeBAreaAtRadius lam (gB q) -
    typeCAreaAtRadius lam (gC q) = _
  unfold commonPerimeterAreaGap
  rw [heqB, heqC]


/-- Clamp a real perimeter to an interval's genuine lower endpoint.  This is
used only to transport the subtype gap across a fixed compact interval. -/
def commonPerimeterClamp {lam : ℝ} (p : CommonPerimeter lam) (q : ℝ) :
    CommonPerimeter lam :=
  ⟨max q p.1, p.2.trans_le (le_max_right q p.1)⟩

lemma commonPerimeterClamp_eq {lam : ℝ} (p : CommonPerimeter lam)
    {q : ℝ} (hq : p.1 ≤ q) :
    commonPerimeterClamp p q = ⟨q, p.2.trans_le hq⟩ := by
  apply Subtype.ext
  exact max_eq_left hq

/-- Real-valued transport of the genuine gap above a fixed genuine perimeter.
Only its restriction to that upper interval is used. -/
def commonPerimeterAreaGapAbove {lam : ℝ} (hlam : AdmissibleDensity lam)
    (p : CommonPerimeter lam) (q : ℝ) : ℝ :=
  commonPerimeterAreaGap hlam (commonPerimeterClamp p q)

lemma commonPerimeterAreaGapAbove_hasDerivWithinAt {lam : ℝ}
    (hlam : AdmissibleDensity lam) (p : CommonPerimeter lam)
    {q : ℝ} (hq : p.1 ≤ q) :
    HasDerivWithinAt (commonPerimeterAreaGapAbove hlam p)
      ((typeBRadiusAtPerimeter hlam ⟨q, p.2.trans_le hq⟩).1 -
        (typeCRadiusAtPerimeter hlam ⟨q, p.2.trans_le hq⟩).1)
      (Set.Ici p.1) q := by
  let qs : CommonPerimeter lam := ⟨q, p.2.trans_le hq⟩
  rcases commonPerimeterAreaGap_local_hasDerivAt hlam qs with
    ⟨gap, hgap, hagree⟩
  have hagree' :
      ∀ᶠ x in nhdsWithin q (Set.Ici p.1),
        ∀ hx : 2 * lam * Real.pi < x,
          gap x = commonPerimeterAreaGap hlam ⟨x, hx⟩ :=
    mem_nhdsWithin_of_mem_nhds hagree
  have heq : commonPerimeterAreaGapAbove hlam p =ᶠ[nhdsWithin q (Set.Ici p.1)]
      gap := by
    filter_upwards [hagree', self_mem_nhdsWithin] with x hxagree hxmem
    have hxdomain : 2 * lam * Real.pi < x := p.2.trans_le hxmem
    rw [commonPerimeterAreaGapAbove,
      commonPerimeterClamp_eq p hxmem]
    exact (hxagree hxdomain).symm
  have hwithin :=
    hgap.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq hq
  simpa [qs] using hwithin

/-- The concrete common-perimeter area gap is strictly decreasing throughout
the genuine open perimeter domain. -/
theorem commonPerimeterAreaGap_strictAnti {lam : ℝ}
    (hlam : AdmissibleDensity lam) :
    StrictAnti (commonPerimeterAreaGap hlam) := by
  intro p q hpq
  let F : ℝ → ℝ := commonPerimeterAreaGapAbove hlam p
  have hcont : ContinuousOn F (Set.Icc p.1 q.1) := by
    intro x hx
    have hder := commonPerimeterAreaGapAbove_hasDerivWithinAt hlam p hx.1
    exact (hder.mono (Set.Icc_subset_Ici_self)).continuousWithinAt
  have hinterior : interior (Set.Icc p.1 q.1) = Set.Ioo p.1 q.1 :=
    interior_Icc
  let radiusGap : ℝ → ℝ := fun x =>
    (typeBRadiusAtPerimeter hlam (commonPerimeterClamp p x)).1 -
      (typeCRadiusAtPerimeter hlam (commonPerimeterClamp p x)).1
  have hderiv : ∀ x ∈ interior (Set.Icc p.1 q.1),
      HasDerivWithinAt F (radiusGap x)
        (interior (Set.Icc p.1 q.1)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo p.1 q.1 := by rwa [hinterior] at hx
    have hlocal0 :=
      commonPerimeterAreaGapAbove_hasDerivWithinAt hlam p hx'.1.le
    have hlocal : HasDerivWithinAt (commonPerimeterAreaGapAbove hlam p)
        ((typeBRadiusAtPerimeter hlam
            ⟨x, p.2.trans_le hx'.1.le⟩).1 -
          (typeCRadiusAtPerimeter hlam
            ⟨x, p.2.trans_le hx'.1.le⟩).1)
        (interior (Set.Icc p.1 q.1)) x :=
      hlocal0.mono (by
        intro y hy
        rw [hinterior] at hy
        exact hy.1.le)
    change HasDerivWithinAt (commonPerimeterAreaGapAbove hlam p)
      ((typeBRadiusAtPerimeter hlam (commonPerimeterClamp p x)).1 -
        (typeCRadiusAtPerimeter hlam (commonPerimeterClamp p x)).1)
      (interior (Set.Icc p.1 q.1)) x
    rw [commonPerimeterClamp_eq p hx'.1.le]
    exact hlocal
  have hneg : ∀ x ∈ interior (Set.Icc p.1 q.1), radiusGap x < 0 := by
    intro x _
    exact sub_neg.mpr
      (typeBRadiusAtPerimeter_lt_typeCRadiusAtPerimeter hlam
        (commonPerimeterClamp p x))
  have hanti : StrictAntiOn F (Set.Icc p.1 q.1) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc p.1 q.1)
      hcont hderiv hneg
  have hresult := hanti
    (show p.1 ∈ Set.Icc p.1 q.1 from ⟨le_rfl, hpq.le⟩)
    (show q.1 ∈ Set.Icc p.1 q.1 from ⟨hpq.le, le_rfl⟩) hpq
  dsimp [F, commonPerimeterAreaGapAbove] at hresult
  rw [commonPerimeterClamp_eq p (le_refl p.1),
    commonPerimeterClamp_eq p hpq.le] at hresult
  exact hresult


lemma typeBPerimeterAtArea_gt_commonEndpoint {lam v : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hv : lam * Real.pi < v) :
    2 * lam * Real.pi < typeBPerimeterAtArea lam v := by
  rcases exists_typeBRadius_at_area hlam0 hlam1 hv with ⟨R, hR, harea⟩
  change 0 < R at hR
  rw [typeBPerimeterAtArea_eq_radius hlam0 hlam1 hR harea,
    ← typeBPerimeterAtRadius_zero hlam0 hlam1]
  exact typeBPerimeterAtRadius_strictMonoOn hlam0 hlam1
    (show (0 : ℝ) ≤ 0 from le_rfl) hR.le hR

/-- Weak C dominance at an area puts the common-perimeter area gap at the B
profile value at or below zero. -/
lemma commonPerimeterAreaGap_at_typeBProfile_nonpos {lam v : ℝ}
    (hlam : AdmissibleDensity lam) (hv : lam * Real.pi < v)
    (hprofile :
      typeCPerimeterAtArea lam v ≤ typeBPerimeterAtArea lam v) :
    commonPerimeterAreaGap hlam
      ⟨typeBPerimeterAtArea lam v,
        typeBPerimeterAtArea_gt_commonEndpoint hlam.1 hlam.2 hv⟩ ≤ 0 := by
  rcases exists_typeBRadius_at_area hlam.1 hlam.2 hv with
    ⟨RB, hRB, hareaB⟩
  rcases exists_typeCRadius_at_area hlam.1 hlam.2 hv with
    ⟨SC, hSC, hareaC⟩
  change 0 < RB at hRB
  change 0 < SC at hSC
  let p : CommonPerimeter lam :=
    ⟨typeBPerimeterAtArea lam v,
      typeBPerimeterAtArea_gt_commonEndpoint hlam.1 hlam.2 hv⟩
  have hprofileB :
      typeBPerimeterAtArea lam v = typeBPerimeterAtRadius lam RB :=
    typeBPerimeterAtArea_eq_radius hlam.1 hlam.2 hRB hareaB
  have hprofileC :
      typeCPerimeterAtArea lam v = typeCPerimeterAtRadius lam SC :=
    typeCPerimeterAtArea_eq_radius hlam.1 hlam.2 hSC hareaC
  have heqB : (typeBRadiusAtPerimeter hlam p).1 = RB :=
    typeBRadiusAtPerimeter_unique hlam p hRB hprofileB.symm
  have hSCle : SC ≤ (typeCRadiusAtPerimeter hlam p).1 := by
    by_contra hnot
    have hlt : (typeCRadiusAtPerimeter hlam p).1 < SC := lt_of_not_ge hnot
    have hperimlt := typeCPerimeterAtRadius_strictMonoOn hlam.1 hlam.2
      (typeCRadiusAtPerimeter_pos hlam p) hSC hlt
    rw [typeCPerimeterAt_typeCRadiusAtPerimeter hlam p,
      ← hprofileC] at hperimlt
    exact (not_lt_of_ge hprofile) hperimlt
  have harea_le :=
    (typeCAreaAtRadius_strictMonoOn hlam.1 hlam.2).monotoneOn
      hSC (typeCRadiusAtPerimeter_pos hlam p) hSCle
  rw [hareaC] at harea_le
  change commonPerimeterAreaGap hlam p ≤ 0
  unfold commonPerimeterAreaGap
  rw [heqB, hareaB]
  linarith


/-- A negative common-perimeter gap at the B profile value converts back to
strict C-profile dominance at the same weighted area. -/
lemma typeCPerimeterAtArea_lt_of_commonPerimeterAreaGap_neg {lam v : ℝ}
    (hlam : AdmissibleDensity lam) (hv : lam * Real.pi < v)
    (hgap : commonPerimeterAreaGap hlam
      ⟨typeBPerimeterAtArea lam v,
        typeBPerimeterAtArea_gt_commonEndpoint hlam.1 hlam.2 hv⟩ < 0) :
    typeCPerimeterAtArea lam v < typeBPerimeterAtArea lam v := by
  rcases exists_typeBRadius_at_area hlam.1 hlam.2 hv with
    ⟨RB, hRB, hareaB⟩
  rcases exists_typeCRadius_at_area hlam.1 hlam.2 hv with
    ⟨SC, hSC, hareaC⟩
  change 0 < RB at hRB
  change 0 < SC at hSC
  let p : CommonPerimeter lam :=
    ⟨typeBPerimeterAtArea lam v,
      typeBPerimeterAtArea_gt_commonEndpoint hlam.1 hlam.2 hv⟩
  have hprofileB :
      typeBPerimeterAtArea lam v = typeBPerimeterAtRadius lam RB :=
    typeBPerimeterAtArea_eq_radius hlam.1 hlam.2 hRB hareaB
  have hprofileC :
      typeCPerimeterAtArea lam v = typeCPerimeterAtRadius lam SC :=
    typeCPerimeterAtArea_eq_radius hlam.1 hlam.2 hSC hareaC
  have heqB : (typeBRadiusAtPerimeter hlam p).1 = RB :=
    typeBRadiusAtPerimeter_unique hlam p hRB hprofileB.symm
  have harea_lt :
      v < typeCAreaAtRadius lam (typeCRadiusAtPerimeter hlam p) := by
    change commonPerimeterAreaGap hlam p < 0 at hgap
    unfold commonPerimeterAreaGap at hgap
    rw [heqB, hareaB] at hgap
    linarith
  have hSC_lt : SC < (typeCRadiusAtPerimeter hlam p).1 := by
    by_contra hnot
    have hle : (typeCRadiusAtPerimeter hlam p).1 ≤ SC := le_of_not_gt hnot
    have harea_le :=
      (typeCAreaAtRadius_strictMonoOn hlam.1 hlam.2).monotoneOn
        (typeCRadiusAtPerimeter_pos hlam p) hSC hle
    rw [hareaC] at harea_le
    exact (not_lt_of_ge harea_le) harea_lt
  have hperim_lt := typeCPerimeterAtRadius_strictMonoOn hlam.1 hlam.2
    hSC (typeCRadiusAtPerimeter_pos hlam p) hSC_lt
  rw [← hprofileC, typeCPerimeterAt_typeCRadiusAtPerimeter hlam p] at hperim_lt
  exact hperim_lt

/-- Once the orthogonal-ball profile is no worse than the equal-area type-(B)
profile, the concrete common-perimeter gap forces strict dominance at every
larger weighted area. -/
theorem typeC_dominance_persists :
    ∀ {lam v₀ v : ℝ},
      0 < lam → lam < 1 → lam * Real.pi < v₀ → v₀ < v →
      typeCPerimeterAtArea lam v₀ ≤ typeBPerimeterAtArea lam v₀ →
      typeCPerimeterAtArea lam v < typeBPerimeterAtArea lam v := by
  intro lam v₀ v hlam0 hlam1 hv₀ hv hinitial
  let hlam : AdmissibleDensity lam := ⟨hlam0, hlam1⟩
  have hv' : lam * Real.pi < v := hv₀.trans hv
  let p₀ : CommonPerimeter lam :=
    ⟨typeBPerimeterAtArea lam v₀,
      typeBPerimeterAtArea_gt_commonEndpoint hlam0 hlam1 hv₀⟩
  let p : CommonPerimeter lam :=
    ⟨typeBPerimeterAtArea lam v,
      typeBPerimeterAtArea_gt_commonEndpoint hlam0 hlam1 hv'⟩
  have hp : p₀ < p := by
    exact typeBPerimeterAtArea_strictMonoOn hlam0 hlam1 hv₀ hv' hv
  have hgap₀ : commonPerimeterAreaGap hlam p₀ ≤ 0 := by
    exact commonPerimeterAreaGap_at_typeBProfile_nonpos hlam hv₀ hinitial
  have hgap_lt : commonPerimeterAreaGap hlam p <
      commonPerimeterAreaGap hlam p₀ :=
    commonPerimeterAreaGap_strictAnti hlam hp
  have hgap : commonPerimeterAreaGap hlam p < 0 :=
    lt_of_lt_of_le hgap_lt hgap₀
  exact typeCPerimeterAtArea_lt_of_commonPerimeterAreaGap_neg hlam hv' hgap

end CMVBallCase
