/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalTranscription

/-!
# Exact centered-difference certificates for the scale-local atlas

The coefficient intervals below enclose exact secant coefficients.  They are not
derivative claims.  The product rule deliberately uses whole-box value
intervals, matching the retained atlas arithmetic.
-/

namespace NearOneLocalCentered

open scoped BigOperators
noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

private def zeroInterval : QInterval := LeanSuffixReflective.QInterval.point 0

/-- A scalar value together with its center value and an exact coordinatewise
centered-difference decomposition.  `whole` encloses both values because the
product rule may use either endpoint of the centered difference. -/
structure Certificate {n : ℕ} (delta : Fin n → ℝ)
    (whole center : QInterval) (coefficient : Fin n → QInterval)
    (value centerValue : ℝ) : Prop where
  whole_value : whole.RealContains value
  whole_center : whole.RealContains centerValue
  center_value : center.RealContains centerValue
  difference : ∃ d : Fin n → ℝ,
    (∀ j, (coefficient j).RealContains (d j)) ∧
      value - centerValue = ∑ j, d j * delta j

namespace Certificate

variable {n : ℕ} {delta : Fin n → ℝ}

/-- A fixed scalar is constant in all centered coordinates.  The interval may
still be nontrivial, as for the single actual constant `Real.pi`. -/
theorem const (whole center : QInterval) (q : ℝ)
    (hwhole : whole.RealContains q) (hcenter : center.RealContains q) :
    Certificate delta whole center (fun _ => zeroInterval) q q := by
  refine ⟨hwhole, hwhole, hcenter, ⟨fun _ => 0, ?_, ?_⟩⟩
  · intro j
    norm_num [zeroInterval, LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.point]
  · simp

/-- A coordinate leaf.  `hdelta` states that the selected centered coordinate
is its actual displacement; no calculus is involved. -/
theorem coordinate (j : Fin n) (whole center : QInterval)
    (x c : ℝ) (hwholeX : whole.RealContains x)
    (hwholeC : whole.RealContains c) (hcenter : center.RealContains c)
    (hdelta : delta j = x - c) :
    Certificate delta whole center
      (fun k => if k = j then LeanSuffixReflective.QInterval.point 1 else zeroInterval) x c := by
  refine ⟨hwholeX, hwholeC, hcenter, ⟨fun k => if k = j then 1 else 0, ?_, ?_⟩⟩
  · intro k
    by_cases hk : k = j
    · subst k
      simp [zeroInterval]
    · simp [hk, zeroInterval]
  · simpa [hdelta] using hdelta.symm

/-- Exact interval addition preserves centered-difference certificates. -/
theorem add
    {wholeF centerF wholeG centerG : QInterval}
    {coefficientF coefficientG : Fin n → QInterval}
    {f fc g gc : ℝ}
    (hf : Certificate delta wholeF centerF coefficientF f fc)
    (hg : Certificate delta wholeG centerG coefficientG g gc) :
    Certificate delta (wholeF.add wholeG) (centerF.add centerG)
      (fun j => (coefficientF j).add (coefficientG j)) (f + g) (fc + gc) := by
  rcases hf.difference with ⟨df, hdf, hdiffF⟩
  rcases hg.difference with ⟨dg, hdg, hdiffG⟩
  refine ⟨
    LeanSuffixReflective.QInterval.realContains_add hf.whole_value hg.whole_value,
    LeanSuffixReflective.QInterval.realContains_add hf.whole_center hg.whole_center,
    LeanSuffixReflective.QInterval.realContains_add hf.center_value hg.center_value,
    ⟨fun j => df j + dg j, ?_, ?_⟩⟩
  · intro j
    exact LeanSuffixReflective.QInterval.realContains_add (hdf j) (hdg j)
  · rw [show f + g - (fc + gc) = (f - fc) + (g - gc) by ring, hdiffF, hdiffG,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Exact interval negation preserves centered-difference certificates. -/
theorem neg
    {whole center : QInterval} {coefficient : Fin n → QInterval} {f fc : ℝ}
    (hf : Certificate delta whole center coefficient f fc) :
    Certificate delta whole.neg center.neg (fun j => (coefficient j).neg) (-f) (-fc) := by
  rcases hf.difference with ⟨df, hdf, hdiff⟩
  refine ⟨LeanSuffixReflective.QInterval.realContains_neg hf.whole_value,
    LeanSuffixReflective.QInterval.realContains_neg hf.whole_center,
    LeanSuffixReflective.QInterval.realContains_neg hf.center_value,
    ⟨fun j => -df j, fun j => LeanSuffixReflective.QInterval.realContains_neg (hdf j), ?_⟩⟩
  rw [show -f - -fc = -(f - fc) by ring, hdiff, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Subtraction is addition followed by exact interval negation. -/
theorem sub
    {wholeF centerF wholeG centerG : QInterval}
    {coefficientF coefficientG : Fin n → QInterval}
    {f fc g gc : ℝ}
    (hf : Certificate delta wholeF centerF coefficientF f fc)
    (hg : Certificate delta wholeG centerG coefficientG g gc) :
    Certificate delta (wholeF.sub wholeG) (centerF.sub centerG)
      (fun j => (coefficientF j).sub (coefficientG j)) (f - g) (fc - gc) := by
  exact add hf (neg hg)

/-- Exact centered product identity.  The output coefficient interval is
`D_f * V_g + V_f * D_g`, exactly the retained checker rule. -/
theorem mul
    {wholeF centerF wholeG centerG : QInterval}
    {coefficientF coefficientG : Fin n → QInterval}
    {f fc g gc : ℝ}
    (hf : Certificate delta wholeF centerF coefficientF f fc)
    (hg : Certificate delta wholeG centerG coefficientG g gc) :
    Certificate delta
      (ScalarSuffixCertificate.QInterval.mul wholeF wholeG)
      (ScalarSuffixCertificate.QInterval.mul centerF centerG)
      (fun j => (ScalarSuffixCertificate.QInterval.mul (coefficientF j) wholeG).add
        (ScalarSuffixCertificate.QInterval.mul wholeF (coefficientG j)))
      (f * g) (fc * gc) := by
  rcases hf.difference with ⟨df, hdf, hdiffF⟩
  rcases hg.difference with ⟨dg, hdg, hdiffG⟩
  refine ⟨
    ScalarSuffixCertificate.QInterval.realContains_mul hf.whole_value hg.whole_value,
    ScalarSuffixCertificate.QInterval.realContains_mul hf.whole_center hg.whole_center,
    ScalarSuffixCertificate.QInterval.realContains_mul hf.center_value hg.center_value,
    ⟨fun j => df j * g + fc * dg j, ?_, ?_⟩⟩
  · intro j
    exact LeanSuffixReflective.QInterval.realContains_add
      (ScalarSuffixCertificate.QInterval.realContains_mul (hdf j) hg.whole_value)
      (ScalarSuffixCertificate.QInterval.realContains_mul hf.whole_center (hdg j))
  · rw [show f * g - fc * gc = (f - fc) * g + fc * (g - gc) by ring,
      hdiffF, hdiffG, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Scalar secant composition.  The caller supplies the actual scalar secant
coefficient and its enclosure; analytic atoms use this rule without calling the
coefficient a composite derivative. -/
theorem comp
    {wholeIn centerIn wholeOut centerOut slope : QInterval}
    {coefficient : Fin n → QInterval} {f fc : ℝ} (phi : ℝ → ℝ)
    (hf : Certificate delta wholeIn centerIn coefficient f fc)
    (hwholeValue : wholeOut.RealContains (phi f))
    (hwholeCenter : wholeOut.RealContains (phi fc))
    (hcenterValue : centerOut.RealContains (phi fc))
    (hsecant : ∃ q : ℝ, slope.RealContains q ∧ phi f - phi fc = q * (f - fc)) :
    Certificate delta wholeOut centerOut
      (fun j => ScalarSuffixCertificate.QInterval.mul slope (coefficient j))
      (phi f) (phi fc) := by
  rcases hf.difference with ⟨df, hdf, hdiff⟩
  rcases hsecant with ⟨q, hq, hqeq⟩
  refine ⟨hwholeValue, hwholeCenter, hcenterValue,
    ⟨fun j => q * df j,
      fun j => ScalarSuffixCertificate.QInterval.realContains_mul hq (hdf j), ?_⟩⟩
  rw [hqeq, hdiff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Scalar mean-value specialization of `comp`.  Only the one-dimensional
analytic atom is differentiated; the incoming centered coefficients remain
exact secants. -/
theorem comp_of_meanValue
    {wholeIn centerIn wholeOut centerOut slope : QInterval}
    {coefficient : Fin n → QInterval} {f fc : ℝ}
    (phi phi' : ℝ → ℝ)
    (hf : Certificate delta wholeIn centerIn coefficient f fc)
    (hwholeValue : wholeOut.RealContains (phi f))
    (hwholeCenter : wholeOut.RealContains (phi fc))
    (hcenterValue : centerOut.RealContains (phi fc))
    (hderiv : ∀ y ∈ Set.uIcc fc f, HasDerivAt phi (phi' y) y)
    (hslope : ∀ y ∈ Set.uIcc fc f, slope.RealContains (phi' y)) :
    Certificate delta wholeOut centerOut
      (fun j => ScalarSuffixCertificate.QInterval.mul slope (coefficient j))
      (phi f) (phi fc) := by
  rcases LeanSuffixAnalytic.centered_meanValue_exists phi phi' hderiv with
    ⟨y, hy, heq⟩
  apply comp phi hf hwholeValue hwholeCenter hcenterValue
  exact ⟨phi' y, hslope y hy, by linarith⟩

/-- Positive reciprocal rule with the exact secant
`-(1/f) * (1/fc)`.  Both reciprocal factors use the whole-box interval, so
the coefficient interval is the checker rule `-(inverseInterval^2)`. -/
theorem recipPos
    {whole center : QInterval} {coefficient : Fin n → QInterval} {f fc : ℝ}
    (hWholePos : 0 < whole.lo) (hCenterPos : 0 < center.lo)
    (hf : Certificate delta whole center coefficient f fc) :
    Certificate delta
      (ScalarSuffixCertificate.QInterval.recipPos whole hWholePos)
      (ScalarSuffixCertificate.QInterval.recipPos center hCenterPos)
      (fun j => ScalarSuffixCertificate.QInterval.mul
        (ScalarSuffixCertificate.QInterval.mul
          (ScalarSuffixCertificate.QInterval.recipPos whole hWholePos)
          (ScalarSuffixCertificate.QInterval.recipPos whole hWholePos)).neg
        (coefficient j))
      (1 / f) (1 / fc) := by
  have hWholeLo : (0 : ℝ) < (whole.lo : ℝ) := by exact_mod_cast hWholePos
  have hfPos : 0 < f := hWholeLo.trans_le hf.whole_value.1
  have hfcPos : 0 < fc := hWholeLo.trans_le hf.whole_center.1
  apply comp (fun x => 1 / x) hf
    (ScalarSuffixCertificate.QInterval.realContains_recipPos hWholePos hf.whole_value)
    (ScalarSuffixCertificate.QInterval.realContains_recipPos hWholePos hf.whole_center)
    (ScalarSuffixCertificate.QInterval.realContains_recipPos hCenterPos hf.center_value)
  refine ⟨-(1 / f) * (1 / fc), ?_, ?_⟩
  · convert LeanSuffixReflective.QInterval.realContains_neg
      (ScalarSuffixCertificate.QInterval.realContains_mul
        (ScalarSuffixCertificate.QInterval.realContains_recipPos
          hWholePos hf.whole_value)
        (ScalarSuffixCertificate.QInterval.realContains_recipPos
          hWholePos hf.whole_center)) using 1
    ring
  · field_simp [ne_of_gt hfPos, ne_of_gt hfcPos]
    <;> ring

/-- Widening only checks exact-rational interval inclusions.  This is the
soundness boundary for each outward-rounded generated node. -/
theorem widen
    {whole center whole' center' : QInterval}
    {coefficient coefficient' : Fin n → QInterval} {f fc : ℝ}
    (hf : Certificate delta whole center coefficient f fc)
    (hWholeLo : whole'.lo ≤ whole.lo) (hWholeHi : whole.hi ≤ whole'.hi)
    (hCenterLo : center'.lo ≤ center.lo) (hCenterHi : center.hi ≤ center'.hi)
    (hCoefficientLo : ∀ j, (coefficient' j).lo ≤ (coefficient j).lo)
    (hCoefficientHi : ∀ j, (coefficient j).hi ≤ (coefficient' j).hi) :
    Certificate delta whole' center' coefficient' f fc := by
  rcases hf.difference with ⟨d, hd, hdiff⟩
  refine ⟨NearOneLocalInterval.realContains_of_subset hWholeLo hWholeHi hf.whole_value,
    NearOneLocalInterval.realContains_of_subset hWholeLo hWholeHi hf.whole_center,
    NearOneLocalInterval.realContains_of_subset hCenterLo hCenterHi hf.center_value,
    ⟨d, fun j => NearOneLocalInterval.realContains_of_subset
      (hCoefficientLo j) (hCoefficientHi j) (hd j), hdiff⟩⟩

end Certificate

/-- One certificate valid uniformly over a closed coordinate box. -/
def UniformCertificate {n : ℕ} (box : Fin n → Set ℝ) (centerPoint : Fin n → ℝ)
    (whole center : QInterval) (coefficient : Fin n → QInterval)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ j, x j ∈ box j) →
    Certificate (fun j => x j - centerPoint j) whole center coefficient
      (f x) (f centerPoint)

namespace UniformCertificate

variable {n : ℕ} {box : Fin n → Set ℝ} {centerPoint : Fin n → ℝ}

/-- Uniform fixed-scalar certificate, including non-point constants such as pi. -/
theorem const (whole center : QInterval) (q : ℝ)
    (hwhole : whole.RealContains q) (hcenter : center.RealContains q) :
    UniformCertificate box centerPoint whole center (fun _ => zeroInterval) (fun _ => q) := by
  intro x _
  exact Certificate.const whole center q hwhole hcenter

/-- Uniform addition is pointwise exact centered addition. -/
theorem add
    {wholeF centerF wholeG centerG : QInterval}
    {coefficientF coefficientG : Fin n → QInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : UniformCertificate box centerPoint wholeF centerF coefficientF f)
    (hg : UniformCertificate box centerPoint wholeG centerG coefficientG g) :
    UniformCertificate box centerPoint (wholeF.add wholeG) (centerF.add centerG)
      (fun j => (coefficientF j).add (coefficientG j)) (fun x => f x + g x) := by
  intro x hx
  exact Certificate.add (hf x hx) (hg x hx)

/-- Uniform negation is pointwise exact centered negation. -/
theorem neg
    {whole center : QInterval} {coefficient : Fin n → QInterval}
    {f : (Fin n → ℝ) → ℝ}
    (hf : UniformCertificate box centerPoint whole center coefficient f) :
    UniformCertificate box centerPoint whole.neg center.neg
      (fun j => (coefficient j).neg) (fun x => -f x) := by
  intro x hx
  exact Certificate.neg (hf x hx)

/-- Uniform multiplication uses the same whole-box product coefficients as the
retained checker. -/
theorem mul
    {wholeF centerF wholeG centerG : QInterval}
    {coefficientF coefficientG : Fin n → QInterval}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : UniformCertificate box centerPoint wholeF centerF coefficientF f)
    (hg : UniformCertificate box centerPoint wholeG centerG coefficientG g) :
    UniformCertificate box centerPoint
      (ScalarSuffixCertificate.QInterval.mul wholeF wholeG)
      (ScalarSuffixCertificate.QInterval.mul centerF centerG)
      (fun j => (ScalarSuffixCertificate.QInterval.mul (coefficientF j) wholeG).add
        (ScalarSuffixCertificate.QInterval.mul wholeF (coefficientG j)))
      (fun x => f x * g x) := by
  intro x hx
  exact Certificate.mul (hf x hx) (hg x hx)

end UniformCertificate

end

end NearOneLocalCentered
