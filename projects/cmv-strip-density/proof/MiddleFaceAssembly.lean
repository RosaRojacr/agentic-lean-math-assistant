/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import ScalarSuffixCertificate

/-!
# Reusable middle-face certificate assembly

This module separates the exact middle-face coordinate model and the compact
root assembly from the rational interval calculations for an individual brick.
A `Conditions` value contains the numerical checker semantics: branch bounds,
strict opposite-face signs, and the uniform `K3` and `G` signs.
-/

open Real Set
open scoped BigOperators
noncomputable section
open ScalarSuffixCertificate

namespace MiddleFaceAssembly

abbrev QInterval := ScalarSuffixCertificate.QInterval
abbrev Vec4 := ScalarSuffixCertificate.Vec4
abbrev InSymmetricBox := ScalarSuffixCertificate.InSymmetricBox

/-- Exact rational data defining one centered middle-face brick. -/
structure Brick where
  lamLo : ℚ
  lamHi : ℚ
  centers : Fin 4 → ℚ
  slopes : Fin 4 → ℚ
  yXiSlope : ℚ
  vRhoSlope : ℚ
  radii : Fin 4 → ℚ
  lamOrdered : lamLo < lamHi
  radiiPos : ∀ j, 0 < radii j

abbrev lamMid (b : Brick) : ℚ := (b.lamLo + b.lamHi) / 2
abbrev tRadius (b : Brick) : ℚ := (b.lamHi - b.lamLo) / 2

def tInterval (b : Brick) : QInterval :=
  ⟨-tRadius b, tRadius b, by
    dsimp [tRadius]
    linarith [b.lamOrdered]⟩

def lamInterval (b : Brick) : QInterval :=
  ⟨b.lamLo, b.lamHi, b.lamOrdered.le⟩

/-- Centered checker coordinates. -/
structure Point where
  t : ℝ
  xi : ℝ
  eta : ℝ
  rho : ℝ
  sigma : ℝ

/- Exact analytic model attached to a rational brick. -/
namespace Model

variable (b : Brick)

def lam (p : Point) : ℝ := (lamMid b : ℝ) + p.t
def x (p : Point) : ℝ := b.centers 0 + b.slopes 0 * p.t + p.xi
def y (p : Point) : ℝ := b.centers 1 + b.slopes 1 * p.t + b.yXiSlope * p.xi + p.eta
def w (p : Point) : ℝ := b.centers 2 + b.slopes 2 * p.t + p.rho
def v (p : Point) : ℝ := b.centers 3 + b.slopes 3 * p.t + b.vRhoSlope * p.rho + p.sigma

def B4 (p : Point) : ℝ := lam b p * y b p + π / 2 - x b p
def D4 (p : Point) : ℝ := sin (y b p) - sin (x b p)
def N4 (p : Point) : ℝ := B4 b p + cos (x b p) * D4 b p
def B3 (p : Point) : ℝ := lam b p * v b p + π - w b p
def D3 (p : Point) : ℝ := sin (v b p) - sin (w b p)
def N3 (p : Point) : ℝ := B3 b p + (cos (w b p) + 2) * D3 b p

def C4 (p : Point) : ℝ := cos (x b p) - lam b p * cos (y b p)
def F (p : Point) : ℝ :=
  cos (x b p) * D4 b p - sin (x b p) * sin (y b p) * B4 b p
def C3 (p : Point) : ℝ := cos (w b p) - lam b p * cos (v b p)
def E (p : Point) : ℝ :=
  2 * cos (x b p) ^ 2 * N3 b p - (1 + cos (w b p)) ^ 2 * N4 b p
def G (p : Point) : ℝ :=
  cos (x b p) * (B3 b p + D3 b p) - (1 + cos (w b p)) * B4 b p

def K3 (p : Point) : ℝ :=
  let h3 := (1 + cos (w b p)) / 2
  4 * h3 * ((1 + cos (w b p)) / sin (w b p) -
    (lam b p ^ 2 + cos (w b p)) / (lam b p * (lam b p * sin (v b p)))) -
  2 * (B3 b p + D3 b p)

def vars (p : Point) : Vec4 := ![p.xi, p.eta, p.rho, p.sigma]
def radiiReal : Vec4 := fun j => (b.radii j : ℝ)
def pointOf (t : ℝ) (z : Vec4) : Point := ⟨t, z 0, z 1, z 2, z 3⟩

def rootMap (t : ℝ) (z : Vec4) : Vec4 :=
  let p := pointOf t z
  ![-F b p, C4 b p, E b p, C3 b p]

def typeThreeCellHeight (t rho : ℝ) : ℝ :=
  (1 + cos ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)) / 2

def typeThreeCellInterval (t : ℝ) : Set ℝ :=
  Icc (typeThreeCellHeight b t (radiiReal b 2))
    (typeThreeCellHeight b t (-radiiReal b 2))

def typeFourCellHeight (t xi : ℝ) : ℝ :=
  cos ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)

def typeFourCellInterval (t : ℝ) : Set ℝ :=
  Icc (typeFourCellHeight b t (radiiReal b 0))
    (typeFourCellHeight b t (-radiiReal b 0))

/-- Continuity of the exact checker map is part of the reusable model, rather
than a numerical obligation for each brick. -/
theorem rootMap_continuous (t : ℝ) : Continuous (rootMap b t) := by
  apply continuous_pi
  intro j
  fin_cases j <;>
    simp [rootMap, Model.F, C4, E, C3, N3, N4, B3, B4, D3, D4, pointOf,
      lam, x, y, w, v] <;> fun_prop

end Model

/-! ### Equal-area residual derivative and opposite-`rho` face lane -/

/- Brick-parametric analytic machinery for the equal-area residual.

Individual bricks retain only their numerical trigonometric enclosures,
derivative-bound certificate, and origin certificate. -/
namespace EResidual

variable (b : Brick)

/-- Scalar form of the equal-area residual, retaining all five affine
variables and hence all correlations used by the face estimate. -/
def reduced (t xi eta rho sigma : ℝ) : ℝ :=
  let ll := (lamMid b : ℝ) + t
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  let ww := (b.centers 2 : ℝ) + b.slopes 2 * t + rho
  let vv := (b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma
  let nn4 := ll * yy + π / 2 - xx + cos xx * (sin yy - sin xx)
  let nn3 := ll * vv + π - ww + (cos ww + 2) * (sin vv - sin ww)
  2 * cos xx ^ 2 * nn3 - (1 + cos ww) ^ 2 * nn4

theorem E_pointOf_eq_reduced (t : ℝ) (z : Vec4) :
    Model.E b (Model.pointOf t z) =
      reduced b t (z 0) (z 1) (z 2) (z 3) := by
  rfl

/-- Directional derivative of the five-variable equal-area formula. -/
def formulaDeriv (ll xx yy ww vv dl dx dy dw dv : ℝ) : ℝ :=
  let nn4 := ll * yy + π / 2 - xx + cos xx * (sin yy - sin xx)
  let nn3 := ll * vv + π - ww + (cos ww + 2) * (sin vv - sin ww)
  let dn4 := dl * yy + ll * dy - dx +
    (-sin xx * dx) * (sin yy - sin xx) +
    cos xx * (cos yy * dy - cos xx * dx)
  let dn3 := dl * vv + ll * dv - dw +
    (-sin ww * dw) * (sin vv - sin ww) +
    (cos ww + 2) * (cos vv * dv - cos ww * dw)
  (-4 : ℝ) * cos xx * sin xx * dx * nn3 + 2 * cos xx ^ 2 * dn3 +
    2 * (1 + cos ww) * sin ww * dw * nn4 - (1 + cos ww) ^ 2 * dn4

/-- Certificate expression matching `formulaDeriv`.  Brick-local interval
certificates supply its atom enclosures. -/
def formulaDerivExpr
    (ell ex ey ew ev esx ecx esy ecy esw ecw esv ecv ep :
      CertificateExpr) (dl dx dy dw dv : ℚ) : CertificateExpr :=
  let nn4 :=
    .add
      (.add
        (.add (.mul ell ey) (.mul (.rational (1 / 2)) ep))
        (.neg ex))
      (.mul ecx (.add esy (.neg esx)))
  let nn3 :=
    .add
      (.add (.add (.mul ell ev) ep) (.neg ew))
      (.mul (.add ecw (.rational 2)) (.add esv (.neg esw)))
  let dn4 :=
    .add
      (.add
        (.add
          (.add (.mul (.rational dl) ey) (.mul ell (.rational dy)))
          (.neg (.rational dx)))
        (.mul
          (.mul (.neg esx) (.rational dx))
          (.add esy (.neg esx))))
      (.mul ecx
        (.add
          (.mul ecy (.rational dy))
          (.neg (.mul ecx (.rational dx)))))
  let dn3 :=
    .add
      (.add
        (.add
          (.add (.mul (.rational dl) ev) (.mul ell (.rational dv)))
          (.neg (.rational dw)))
        (.mul
          (.mul (.neg esw) (.rational dw))
          (.add esv (.neg esw))))
      (.mul (.add ecw (.rational 2))
        (.add
          (.mul ecv (.rational dv))
          (.neg (.mul ecw (.rational dw)))))
  .add
    (.add
      (.mul
        (.mul
          (.mul (.mul (.rational (-4)) ecx) esx)
          (.rational dx))
        nn3)
      (.mul (.mul (.rational 2) (.mul ecx ecx)) dn3))
    (.add
      (.mul
        (.mul
          (.mul (.mul (.rational 2) (.add (.rational 1) ecw)) esw)
          (.rational dw))
        nn4)
      (.neg
        (.mul
          (.mul (.add (.rational 1) ecw) (.add (.rational 1) ecw))
          dn4)))

def derivT (t xi eta rho sigma : ℝ) : ℝ :=
  formulaDeriv ((lamMid b : ℝ) + t)
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
    1 (b.slopes 0) (b.slopes 1) (b.slopes 2) (b.slopes 3)

def derivXi (t xi eta rho sigma : ℝ) : ℝ :=
  formulaDeriv ((lamMid b : ℝ) + t)
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
    0 1 b.yXiSlope 0 0

def derivEta (t xi eta rho sigma : ℝ) : ℝ :=
  formulaDeriv ((lamMid b : ℝ) + t)
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
    0 0 1 0 0

def derivRho (t xi eta rho sigma : ℝ) : ℝ :=
  formulaDeriv ((lamMid b : ℝ) + t)
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
    0 0 0 1 b.vRhoSlope

def derivSigma (t xi eta rho sigma : ℝ) : ℝ :=
  formulaDeriv ((lamMid b : ℝ) + t)
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
    0 0 0 0 1

private theorem formula_hasDerivAt
    {lf xf yf wf vf : ℝ → ℝ} {q ll xx yy ww vv dl dx dy dw dv : ℝ}
    (hl : HasDerivAt lf dl q) (hx : HasDerivAt xf dx q)
    (hy : HasDerivAt yf dy q) (hw : HasDerivAt wf dw q)
    (hv : HasDerivAt vf dv q)
    (hll : lf q = ll) (hxx : xf q = xx) (hyy : yf q = yy)
    (hww : wf q = ww) (hvv : vf q = vv) :
    HasDerivAt
      (fun u =>
        let nn4 := lf u * yf u + π / 2 - xf u +
          cos (xf u) * (sin (yf u) - sin (xf u))
        let nn3 := lf u * vf u + π - wf u +
          (cos (wf u) + 2) * (sin (vf u) - sin (wf u))
        2 * cos (xf u) ^ 2 * nn3 - (1 + cos (wf u)) ^ 2 * nn4)
      (formulaDeriv ll xx yy ww vv dl dx dy dw dv) q := by
  subst ll
  subst xx
  subst yy
  subst ww
  subst vv
  have hsx := (Real.hasDerivAt_sin (xf q)).comp q hx
  have hcx := (Real.hasDerivAt_cos (xf q)).comp q hx
  have hsy := (Real.hasDerivAt_sin (yf q)).comp q hy
  have hcy := (Real.hasDerivAt_cos (yf q)).comp q hy
  have hsw := (Real.hasDerivAt_sin (wf q)).comp q hw
  have hcw := (Real.hasDerivAt_cos (wf q)).comp q hw
  have hsv := (Real.hasDerivAt_sin (vf q)).comp q hv
  have hcv := (Real.hasDerivAt_cos (vf q)).comp q hv
  have hn4 :=
    (((hl.mul hy).add (hasDerivAt_const q (π / 2))).sub hx).add
      (hcx.mul (hsy.sub hsx))
  have hn3 :=
    (((hl.mul hv).add (hasDerivAt_const q π)).sub hw).add
      ((hcw.add_const 2).mul (hsv.sub hsw))
  have he :=
    (((hasDerivAt_const q 2).mul (hcx.pow 2)).mul hn3).sub
      (((hasDerivAt_const q 1).add hcw).pow 2 |>.mul hn4)
  convert he using 1 <;> try rfl
  simp [Function.comp_apply, formulaDeriv]
  ring

private theorem hasDerivAt_affine (a d c q : ℝ) :
    HasDerivAt (fun u => a + d * u + c) d q := by
  convert ((hasDerivAt_const q a).add
    ((hasDerivAt_const q d).mul (hasDerivAt_id q))).add
      (hasDerivAt_const q c) using 1 <;>
    first | rfl | ring_nf

theorem reduced_hasDerivAt_t (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b u xi eta rho sigma)
      (derivT b t xi eta rho sigma) t := by
  have hl : HasDerivAt (fun u : ℝ => (lamMid b : ℝ) + u) 1 t := by
    convert hasDerivAt_affine (lamMid b : ℝ) 1 0 t using 1 <;>
      first | rfl | ring_nf
  have hx : HasDerivAt
      (fun u : ℝ => (b.centers 0 : ℝ) + b.slopes 0 * u + xi)
      (b.slopes 0 : ℝ) t := hasDerivAt_affine _ _ _ _
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * u +
        b.yXiSlope * xi + eta) (b.slopes 1 : ℝ) t := by
    convert hasDerivAt_affine (b.centers 1 : ℝ) (b.slopes 1 : ℝ)
      ((b.yXiSlope : ℝ) * xi + eta) t using 1 <;>
        first | rfl | ring_nf
  have hw : HasDerivAt
      (fun u : ℝ => (b.centers 2 : ℝ) + b.slopes 2 * u + rho)
      (b.slopes 2 : ℝ) t := hasDerivAt_affine _ _ _ _
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * u +
        b.vRhoSlope * rho + sigma) (b.slopes 3 : ℝ) t := by
    convert hasDerivAt_affine (b.centers 3 : ℝ) (b.slopes 3 : ℝ)
      ((b.vRhoSlope : ℝ) * rho + sigma) t using 1 <;>
        first | rfl | ring_nf
  exact formula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

theorem reduced_hasDerivAt_xi (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t u eta rho sigma)
      (derivXi b t xi eta rho sigma) xi := by
  have hl := hasDerivAt_const xi ((lamMid b : ℝ) + t)
  have hx : HasDerivAt
      (fun u : ℝ => (b.centers 0 : ℝ) + b.slopes 0 * t + u) 1 xi := by
    convert hasDerivAt_affine
      ((b.centers 0 : ℝ) + b.slopes 0 * t) 1 0 xi using 1 <;>
        first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * u + eta) (b.yXiSlope : ℝ) xi := by
    convert hasDerivAt_affine
      ((b.centers 1 : ℝ) + b.slopes 1 * t) (b.yXiSlope : ℝ)
        eta xi using 1 <;> first | rfl | ring_nf
  have hw := hasDerivAt_const xi
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
  have hv := hasDerivAt_const xi
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
  exact formula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

theorem reduced_hasDerivAt_eta (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t xi u rho sigma)
      (derivEta b t xi eta rho sigma) eta := by
  have hl := hasDerivAt_const eta ((lamMid b : ℝ) + t)
  have hx := hasDerivAt_const eta
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi + u) 1 eta := by
    convert hasDerivAt_affine
      ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi) 1 0 eta using 1 <;>
        first | rfl | ring_nf
  have hw := hasDerivAt_const eta
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
  have hv := hasDerivAt_const eta
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho + sigma)
  exact formula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

theorem reduced_hasDerivAt_rho (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t xi eta u sigma)
      (derivRho b t xi eta rho sigma) rho := by
  have hl := hasDerivAt_const rho ((lamMid b : ℝ) + t)
  have hx := hasDerivAt_const rho
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
  have hy := hasDerivAt_const rho
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
  have hw : HasDerivAt
      (fun u : ℝ => (b.centers 2 : ℝ) + b.slopes 2 * t + u) 1 rho := by
    convert hasDerivAt_affine
      ((b.centers 2 : ℝ) + b.slopes 2 * t) 1 0 rho using 1 <;>
        first | rfl | ring_nf
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * u + sigma) (b.vRhoSlope : ℝ) rho := by
    convert hasDerivAt_affine
      ((b.centers 3 : ℝ) + b.slopes 3 * t)
        (b.vRhoSlope : ℝ) sigma rho using 1 <;>
          first | rfl | ring_nf
  exact formula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

theorem reduced_hasDerivAt_sigma (t xi eta rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t xi eta rho u)
      (derivSigma b t xi eta rho sigma) sigma := by
  have hl := hasDerivAt_const sigma ((lamMid b : ℝ) + t)
  have hx := hasDerivAt_const sigma
    ((b.centers 0 : ℝ) + b.slopes 0 * t + xi)
  have hy := hasDerivAt_const sigma
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)
  have hw := hasDerivAt_const sigma
    ((b.centers 2 : ℝ) + b.slopes 2 * t + rho)
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * rho + u) 1 sigma := by
    convert hasDerivAt_affine
      ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho)
        1 0 sigma using 1 <;> first | rfl | ring_nf
  exact formula_hasDerivAt hl hx hy hw hv rfl rfl rfl rfl rfl

/-- The uniform numerical derivative contract proved separately by each
brick's exact-rational interval certificate on a lambda-centered interval of
radius `R`. -/
def DerivativeBoundsOn (R : ℝ) : Prop :=
  ∀ {t xi eta rho sigma : ℝ},
    (-R ≤ t ∧ t ≤ R) →
    (-(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) →
    (-(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) →
    (-(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) →
    (-(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) →
    |derivT b t xi eta rho sigma| ≤ (7 / 100 : ℝ) ∧
      |derivXi b t xi eta rho sigma| ≤ (3 / 500 : ℝ) ∧
      |derivEta b t xi eta rho sigma| ≤ (721 / 100 : ℝ) ∧
      (47 / 25 : ℝ) ≤ derivRho b t xi eta rho sigma ∧
      |derivSigma b t xi eta rho sigma| ≤ (351 / 50 : ℝ)

/-- Full-width compatibility specialization. -/
abbrev DerivativeBounds : Prop := DerivativeBoundsOn b (1 / 20000)

theorem abs_image_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {R M u : ℝ}
    (hR : 0 ≤ R) (hu : u ∈ Icc (-R) R)
    (hderiv : ∀ q ∈ Icc (-R) R, HasDerivAt f (f' q) q)
    (hbound : ∀ q ∈ Icc (-R) R, |f' q| ≤ M) :
    |f u - f 0| ≤ M * |u| := by
  have hzero : (0 : ℝ) ∈ Icc (-R) R := by constructor <;> linarith
  have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (C := M)
    (fun q hq => (hderiv q hq).hasFDerivAt.hasFDerivWithinAt)
    (fun q hq => by simpa [Real.norm_eq_abs] using hbound q hq)
    hzero hu
  simpa [Real.norm_eq_abs] using h

theorem rho_zero_abs_lt_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    |reduced b t xi eta 0 sigma| < (37 / 2000000 : ℝ) := by
  have hzeroT : (0 : ℝ) ∈ Icc (-R) R := by
    constructor <;> linarith
  have hzeroXi : (0 : ℝ) ∈ Icc (-(1 / 100000)) (1 / 100000) := by
    constructor <;> norm_num
  have hzeroEta : (0 : ℝ) ∈ Icc (-(1 / 1000000)) (1 / 1000000) := by
    constructor <;> norm_num
  have hzeroRho : (0 : ℝ) ∈ Icc (-(1 / 100000)) (1 / 100000) := by
    constructor <;> norm_num
  have hzeroSigma : (0 : ℝ) ∈ Icc (-(1 / 1000000)) (1 / 1000000) := by
    constructor <;> norm_num
  have htChange :
      |reduced b t 0 0 0 0 - reduced b 0 0 0 0 0| ≤ (7 / 100 : ℝ) * |t| := by
    apply abs_image_sub_le_of_hasDerivAt (R := R) (u := t)
      hR ht
    · intro q _
      exact reduced_hasDerivAt_t b q 0 0 0 0
    · intro q hq
      exact (hderiv hq hzeroXi hzeroEta hzeroRho hzeroSigma).1
  have hxiChange :
      |reduced b t xi 0 0 0 - reduced b t 0 0 0 0| ≤
        (3 / 500 : ℝ) * |xi| := by
    apply abs_image_sub_le_of_hasDerivAt (R := (1 / 100000 : ℝ)) (u := xi)
      (by norm_num) hxi
    · intro q _
      exact reduced_hasDerivAt_xi b t q 0 0 0
    · intro q hq
      exact (hderiv ht hq hzeroEta hzeroRho hzeroSigma).2.1
  have hetaChange :
      |reduced b t xi eta 0 0 - reduced b t xi 0 0 0| ≤
        (721 / 100 : ℝ) * |eta| := by
    apply abs_image_sub_le_of_hasDerivAt (R := (1 / 1000000 : ℝ)) (u := eta)
      (by norm_num) heta
    · intro q _
      exact reduced_hasDerivAt_eta b t xi q 0 0
    · intro q hq
      exact (hderiv ht hxi hq hzeroRho hzeroSigma).2.2.1
  have hsigmaChange :
      |reduced b t xi eta 0 sigma - reduced b t xi eta 0 0| ≤
        (351 / 50 : ℝ) * |sigma| := by
    apply abs_image_sub_le_of_hasDerivAt
      (R := (1 / 1000000 : ℝ)) (u := sigma) (by norm_num) hsigma
    · intro q _
      exact reduced_hasDerivAt_sigma b t xi eta 0 q
    · intro q hq
      exact (hderiv ht hxi heta hzeroRho hq).2.2.2.2
  have htAbs : |t| ≤ R := (abs_le).2 ht
  have hxiAbs : |xi| ≤ (1 / 100000 : ℝ) := (abs_le).2 hxi
  have hetaAbs : |eta| ≤ (1 / 1000000 : ℝ) := (abs_le).2 heta
  have hsigmaAbs : |sigma| ≤ (1 / 1000000 : ℝ) := (abs_le).2 hsigma
  have htriangle :
      |reduced b t xi eta 0 sigma| ≤
        |reduced b t xi eta 0 sigma - reduced b t xi eta 0 0| +
        |reduced b t xi eta 0 0 - reduced b t xi 0 0 0| +
        |reduced b t xi 0 0 0 - reduced b t 0 0 0 0| +
        |reduced b t 0 0 0 0 - reduced b 0 0 0 0 0| +
        |reduced b 0 0 0 0 0| := by
    calc
      |reduced b t xi eta 0 sigma| =
          |(reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
           (reduced b t xi eta 0 0 - reduced b t xi 0 0 0) +
           (reduced b t xi 0 0 0 - reduced b t 0 0 0 0) +
           (reduced b t 0 0 0 0 - reduced b 0 0 0 0 0) +
           reduced b 0 0 0 0 0| := by ring
      _ ≤
          |(reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
            (reduced b t xi eta 0 0 - reduced b t xi 0 0 0) +
            (reduced b t xi 0 0 0 - reduced b t 0 0 0 0) +
            (reduced b t 0 0 0 0 - reduced b 0 0 0 0 0)| +
          |reduced b 0 0 0 0 0| := abs_add_le _ _
      _ ≤ _ := by
        calc
          _ ≤
              (|(reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
                (reduced b t xi eta 0 0 - reduced b t xi 0 0 0) +
                (reduced b t xi 0 0 0 - reduced b t 0 0 0 0)| +
              |reduced b t 0 0 0 0 - reduced b 0 0 0 0 0|) +
              |reduced b 0 0 0 0 0| := by
                linarith [abs_add_le
                  ((reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
                   (reduced b t xi eta 0 0 - reduced b t xi 0 0 0) +
                   (reduced b t xi 0 0 0 - reduced b t 0 0 0 0))
                  (reduced b t 0 0 0 0 - reduced b 0 0 0 0 0)]
          _ ≤
              ((|(reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
                (reduced b t xi eta 0 0 - reduced b t xi 0 0 0)| +
              |reduced b t xi 0 0 0 - reduced b t 0 0 0 0|) +
              |reduced b t 0 0 0 0 - reduced b 0 0 0 0 0|) +
              |reduced b 0 0 0 0 0| := by
                linarith [abs_add_le
                  ((reduced b t xi eta 0 sigma - reduced b t xi eta 0 0) +
                   (reduced b t xi eta 0 0 - reduced b t xi 0 0 0))
                  (reduced b t xi 0 0 0 - reduced b t 0 0 0 0)]
          _ ≤ _ := by
            linarith [abs_add_le
              (reduced b t xi eta 0 sigma - reduced b t xi eta 0 0)
              (reduced b t xi eta 0 0 - reduced b t xi 0 0 0)]
  norm_num at htChange hxiChange hetaChange hsigmaChange htAbs hxiAbs hetaAbs
  norm_num at hsigmaAbs htriangle horigin ⊢
  nlinarith [hRmax]

theorem rho_growth_on {R : ℝ} (hderiv : DerivativeBoundsOn b R)
    {t xi eta sigma rho₁ rho₂ : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000)
    (hrho₁ : rho₁ ∈ Icc (-(1 / 100000 : ℝ)) (1 / 100000))
    (hrho₂ : rho₂ ∈ Icc (-(1 / 100000 : ℝ)) (1 / 100000))
    (hrho : rho₁ ≤ rho₂) :
    (47 / 25 : ℝ) * (rho₂ - rho₁) ≤
      reduced b t xi eta rho₂ sigma - reduced b t xi eta rho₁ sigma := by
  apply (convex_Icc (-(1 / 100000 : ℝ))
    (1 / 100000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold reduced; fun_prop) (by unfold reduced; fun_prop) ?_
        rho₁ hrho₁ rho₂ hrho₂ hrho
  intro q hq
  have hq' : -(1 / 100000 : ℝ) ≤ q ∧ q ≤ 1 / 100000 := by
    have hqi : q ∈ Ioo (-(1 / 100000 : ℝ)) (1 / 100000) := by
      simpa only [interior_Icc] using hq
    exact ⟨hqi.1.le, hqi.2.le⟩
  rw [(reduced_hasDerivAt_rho b t xi eta q sigma).deriv]
  exact (hderiv ht hxi heta hq' hsigma).2.2.2.1

theorem low_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    reduced b t xi eta (-(1 / 100000)) sigma <
      -(14 / 1000000000 : ℝ) := by
  have hzero := rho_zero_abs_lt_on b hR hRmax hderiv horigin ht hxi heta hsigma
  have hgrowth := rho_growth_on b hderiv ht hxi heta hsigma
    (rho₁ := -(1 / 100000 : ℝ)) (rho₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

theorem high_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    (14 / 1000000000 : ℝ) <
      reduced b t xi eta (1 / 100000) sigma := by
  have hzero := rho_zero_abs_lt_on b hR hRmax hderiv horigin ht hxi heta hsigma
  have hgrowth := rho_growth_on b hderiv ht hxi heta hsigma
    (rho₁ := 0) (rho₂ := (1 / 100000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

/-- Full-width compatibility specialization. -/
theorem rho_zero_abs_lt (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    |reduced b t xi eta 0 sigma| < (37 / 2000000 : ℝ) :=
  rho_zero_abs_lt_on b (by norm_num) (by norm_num) hderiv horigin
    ht hxi heta hsigma

/-- Full-width compatibility specialization. -/
theorem rho_growth (hderiv : DerivativeBounds b)
    {t xi eta sigma rho₁ rho₂ : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000)
    (hrho₁ : rho₁ ∈ Icc (-(1 / 100000 : ℝ)) (1 / 100000))
    (hrho₂ : rho₂ ∈ Icc (-(1 / 100000 : ℝ)) (1 / 100000))
    (hrho : rho₁ ≤ rho₂) :
    (47 / 25 : ℝ) * (rho₂ - rho₁) ≤
      reduced b t xi eta rho₂ sigma - reduced b t xi eta rho₁ sigma :=
  rho_growth_on b hderiv ht hxi heta hsigma hrho₁ hrho₂ hrho

/-- Full-width compatibility specialization. -/
theorem low_face_margin (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    reduced b t xi eta (-(1 / 100000)) sigma <
      -(14 / 1000000000 : ℝ) :=
  low_face_margin_on b (by norm_num) (by norm_num) hderiv horigin
    ht hxi heta hsigma

/-- Full-width compatibility specialization. -/
theorem high_face_margin (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0 0 0| < (3 / 10000000 : ℝ))
    {t xi eta sigma : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000)
    (hsigma : -(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) :
    (14 / 1000000000 : ℝ) <
      reduced b t xi eta (1 / 100000) sigma :=
  high_face_margin_on b (by norm_num) (by norm_num) hderiv horigin
    ht hxi heta hsigma


end EResidual

/-! ### Correlation-preserving type-(iv) Snell residual lane -/

/- Brick-parametric analytic machinery for the `C4` residual.

Individual bricks retain only the exact-rational trigonometric enclosures that
prove the origin and uniform derivative bounds below. -/
namespace C4Residual

variable (b : Brick)

/-- Scalar form of `C4`, retaining the correlated `t`, `xi`, and `eta`
variables used by the opposite-face certificate. -/
def reduced (t xi eta : ℝ) : ℝ :=
  cos ((b.centers 0 : ℝ) + b.slopes 0 * t + xi) -
    ((lamMid b : ℝ) + t) *
      cos ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)

theorem C4_pointOf_eq_reduced (t : ℝ) (z : Vec4) :
    Model.C4 b (Model.pointOf t z) = reduced b t (z 0) (z 1) := by
  rfl

/-- Derivative of the correlated `C4` residual in the brick parameter. -/
def derivT (t xi eta : ℝ) : ℝ :=
  -(b.slopes 0 : ℝ) *
      sin ((b.centers 0 : ℝ) + b.slopes 0 * t + xi) -
    cos ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta) +
    (b.slopes 1 : ℝ) * (((lamMid b : ℝ) + t) *
      sin ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta))

/-- Derivative of the correlated `C4` residual in `xi`. -/
def derivXi (t xi eta : ℝ) : ℝ :=
  -sin ((b.centers 0 : ℝ) + b.slopes 0 * t + xi) +
    (b.yXiSlope : ℝ) * (((lamMid b : ℝ) + t) *
      sin ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta))

/-- Derivative of the correlated `C4` residual in `eta`. -/
def derivEta (t xi eta : ℝ) : ℝ :=
  ((lamMid b : ℝ) + t) *
    sin ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta)

theorem reduced_hasDerivAt_t (t xi eta : ℝ) :
    HasDerivAt (fun u => reduced b u xi eta) (derivT b t xi eta) t := by
  have hx : HasDerivAt
      (fun u : ℝ => (b.centers 0 : ℝ) + b.slopes 0 * u + xi)
      (b.slopes 0 : ℝ) t := by
    convert ((hasDerivAt_const t (b.centers 0 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 0 : ℝ)).mul
        (hasDerivAt_id t))).add (hasDerivAt_const t xi) using 1 <;>
      first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * u +
        b.yXiSlope * xi + eta) (b.slopes 1 : ℝ) t := by
    convert (((hasDerivAt_const t (b.centers 1 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 1 : ℝ)).mul
        (hasDerivAt_id t))).add
          (hasDerivAt_const t ((b.yXiSlope : ℝ) * xi))).add
            (hasDerivAt_const t eta) using 1 <;>
      first | rfl | ring_nf
  have hlam : HasDerivAt (fun u : ℝ => (lamMid b : ℝ) + u) 1 t := by
    convert (hasDerivAt_const t (lamMid b : ℝ)).add (hasDerivAt_id t) using 1 <;>
      first | rfl | ring_nf
  convert ((Real.hasDerivAt_cos _).comp t hx).sub
      (hlam.mul ((Real.hasDerivAt_cos _).comp t hy)) using 1 <;> try rfl
  simp only [Function.comp_apply, derivT]
  ring

theorem reduced_hasDerivAt_xi (t xi eta : ℝ) :
    HasDerivAt (fun u => reduced b t u eta) (derivXi b t xi eta) xi := by
  have hx : HasDerivAt
      (fun u : ℝ => (b.centers 0 : ℝ) + b.slopes 0 * t + u) 1 xi := by
    convert (hasDerivAt_const xi
      ((b.centers 0 : ℝ) + b.slopes 0 * t)).add (hasDerivAt_id xi) using 1 <;>
      first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * u + eta) (b.yXiSlope : ℝ) xi := by
    convert ((hasDerivAt_const xi
      ((b.centers 1 : ℝ) + b.slopes 1 * t)).add
        ((hasDerivAt_const xi (b.yXiSlope : ℝ)).mul
          (hasDerivAt_id xi))).add (hasDerivAt_const xi eta) using 1 <;>
      first | rfl | ring_nf
  convert ((Real.hasDerivAt_cos _).comp xi hx).sub
      ((hasDerivAt_const xi ((lamMid b : ℝ) + t)).mul
        ((Real.hasDerivAt_cos _).comp xi hy)) using 1 <;> try rfl
  simp only [Function.comp_apply, derivXi]
  ring

theorem reduced_hasDerivAt_eta (t xi eta : ℝ) :
    HasDerivAt (fun u => reduced b t xi u) (derivEta b t xi eta) eta := by
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi + u) 1 eta := by
    convert (hasDerivAt_const eta
      ((b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi)).add (hasDerivAt_id eta) using 1 <;>
      first | rfl | ring_nf
  convert (hasDerivAt_const eta
      (cos ((b.centers 0 : ℝ) + b.slopes 0 * t + xi))).sub
    ((hasDerivAt_const eta ((lamMid b : ℝ) + t)).mul
      ((Real.hasDerivAt_cos _).comp eta hy)) using 1 <;> try rfl
  simp only [Function.comp_apply, derivEta]
  ring

/-- Uniform numerical derivative contract proved by each brick's exact
rational enclosure certificate on a lambda-centered interval of radius `R`. -/
def DerivativeBoundsOn (R : ℝ) : Prop :=
  ∀ {t xi eta : ℝ},
    (-R ≤ t ∧ t ≤ R) →
    (-(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) →
    (-(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) →
    |derivT b t xi eta| ≤ (11 / 5000 : ℝ) ∧
      |derivXi b t xi eta| ≤ (3 / 2000 : ℝ) ∧
      (109 / 400 : ℝ) ≤ derivEta b t xi eta

/-- Full-width compatibility specialization. -/
abbrev DerivativeBounds : Prop := DerivativeBoundsOn b (1 / 20000)

/-- The `C4` residual at `eta = 0` stays close to its certified origin value.
All mean-value bookkeeping is independent of the brick's numerical data. -/
theorem eta_zero_abs_lt_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    |reduced b t xi 0| < (1 / 5000000 : ℝ) := by
  have hzeroXi : (0 : ℝ) ∈ Icc (-(1 / 100000)) (1 / 100000) := by
    constructor <;> norm_num
  have hzeroEta : (0 : ℝ) ∈ Icc (-(1 / 1000000)) (1 / 1000000) := by
    constructor <;> norm_num
  have htChange :
      |reduced b t 0 0 - reduced b 0 0 0| ≤ (11 / 5000 : ℝ) * |t| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := R) (u := t) hR ht
    · intro q _
      exact reduced_hasDerivAt_t b q 0 0
    · intro q hq
      exact (hderiv hq hzeroXi hzeroEta).1
  have hxiChange :
      |reduced b t xi 0 - reduced b t 0 0| ≤
        (3 / 2000 : ℝ) * |xi| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := (1 / 100000 : ℝ)) (u := xi) (by norm_num) hxi
    · intro q _
      exact reduced_hasDerivAt_xi b t q 0
    · intro q hq
      exact (hderiv ht hq hzeroEta).2.1
  have htAbs : |t| ≤ R := (abs_le).2 ht
  have hxiAbs : |xi| ≤ (1 / 100000 : ℝ) := (abs_le).2 hxi
  have htriangle :
      |reduced b t xi 0| ≤
        |reduced b t xi 0 - reduced b t 0 0| +
          |reduced b t 0 0 - reduced b 0 0 0| +
            |reduced b 0 0 0| := by
    calc
      |reduced b t xi 0| =
          |(reduced b t xi 0 - reduced b t 0 0) +
            (reduced b t 0 0 - reduced b 0 0 0) +
              reduced b 0 0 0| := by ring
      _ ≤ |(reduced b t xi 0 - reduced b t 0 0) +
              (reduced b t 0 0 - reduced b 0 0 0)| +
            |reduced b 0 0 0| := abs_add_le _ _
      _ ≤ _ := by
        linarith [abs_add_le
          (reduced b t xi 0 - reduced b t 0 0)
          (reduced b t 0 0 - reduced b 0 0 0)]
  norm_num at htChange hxiChange htAbs hxiAbs htriangle horigin ⊢
  nlinarith [hRmax]

/-- Quantitative monotonicity in `eta`, deduced once from the certified
derivative lower bound. -/
theorem eta_growth_on {R : ℝ} (hderiv : DerivativeBoundsOn b R)
    {t xi eta₁ eta₂ : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta₁ : eta₁ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (heta₂ : eta₂ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (heta : eta₁ ≤ eta₂) :
    (109 / 400 : ℝ) * (eta₂ - eta₁) ≤
      reduced b t xi eta₂ - reduced b t xi eta₁ := by
  apply (convex_Icc (-(1 / 1000000 : ℝ))
    (1 / 1000000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold reduced; fun_prop) (by unfold reduced; fun_prop) ?_
        eta₁ heta₁ eta₂ heta₂ heta
  intro q hq
  have hq' : -(1 / 1000000 : ℝ) ≤ q ∧ q ≤ 1 / 1000000 := by
    have hqi : q ∈ Ioo (-(1 / 1000000 : ℝ)) (1 / 1000000) := by
      simpa only [interior_Icc] using hq
    exact ⟨hqi.1.le, hqi.2.le⟩
  rw [(reduced_hasDerivAt_eta b t xi q).deriv]
  exact (hderiv ht hxi hq').2.2

theorem low_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    reduced b t xi (-(1 / 1000000)) < -(11 / 10000000000 : ℝ) := by
  have hzero := eta_zero_abs_lt_on b hR hRmax hderiv horigin ht hxi
  have hgrowth := eta_growth_on b hderiv ht hxi
    (eta₁ := -(1 / 1000000 : ℝ)) (eta₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

theorem high_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    (11 / 10000000000 : ℝ) < reduced b t xi (1 / 1000000) := by
  have hzero := eta_zero_abs_lt_on b hR hRmax hderiv horigin ht hxi
  have hgrowth := eta_growth_on b hderiv ht hxi
    (eta₁ := 0) (eta₂ := (1 / 1000000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

/-- Full-width compatibility specialization. -/
theorem eta_zero_abs_lt (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    |reduced b t xi 0| < (1 / 5000000 : ℝ) :=
  eta_zero_abs_lt_on b (by norm_num) (by norm_num) hderiv horigin ht hxi

/-- Full-width compatibility specialization. -/
theorem eta_growth (hderiv : DerivativeBounds b)
    {t xi eta₁ eta₂ : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta₁ : eta₁ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (heta₂ : eta₂ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (heta : eta₁ ≤ eta₂) :
    (109 / 400 : ℝ) * (eta₂ - eta₁) ≤
      reduced b t xi eta₂ - reduced b t xi eta₁ :=
  eta_growth_on b hderiv ht hxi heta₁ heta₂ heta

/-- Full-width compatibility specialization. -/
theorem low_face_margin (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    reduced b t xi (-(1 / 1000000)) < -(11 / 10000000000 : ℝ) :=
  low_face_margin_on b (by norm_num) (by norm_num) hderiv horigin ht hxi

/-- Full-width compatibility specialization. -/
theorem high_face_margin (hderiv : DerivativeBounds b)
    (horigin : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t xi : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) :
    (11 / 10000000000 : ℝ) < reduced b t xi (1 / 1000000) :=
  high_face_margin_on b (by norm_num) (by norm_num) hderiv horigin ht hxi

end C4Residual

/-! ### Correlation-preserving type-(iv) fold residual lane -/

/- Brick-parametric analytic machinery for the `F` residual.

Individual bricks retain only the exact-rational endpoint and derivative
enclosures used by the shared opposite-face argument below. -/
namespace FResidual

variable (b : Brick)

/-- Scalar form of `F`, retaining the correlated `t`, `xi`, and `eta`
variables used by the opposite-face certificate. -/
def reduced (t xi eta : ℝ) : ℝ :=
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  let ll := (lamMid b : ℝ) + t
  cos xx * (sin yy - sin xx) -
    sin xx * sin yy * (ll * yy + π / 2 - xx)

theorem F_pointOf_eq_reduced (t : ℝ) (z : Vec4) :
    Model.F b (Model.pointOf t z) = reduced b t (z 0) (z 1) := by
  rfl

/-- Derivative of the correlated `F` residual in the brick parameter. -/
def derivT (t xi eta : ℝ) : ℝ :=
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  let ll := (lamMid b : ℝ) + t
  let bb := ll * yy + π / 2 - xx
  let dx := (b.slopes 0 : ℝ)
  let dy := (b.slopes 1 : ℝ)
  (-dx) * sin xx * (sin yy - sin xx) +
    cos xx * (dy * cos yy - dx * cos xx) -
      (dx * cos xx * sin yy * bb + sin xx * dy * cos yy * bb +
        sin xx * sin yy * (yy + ll * dy - dx))

/-- Derivative of the correlated `F` residual in the thin `eta` direction. -/
def derivEta (t xi eta : ℝ) : ℝ :=
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  let ll := (lamMid b : ℝ) + t
  let bb := ll * yy + π / 2 - xx
  cos xx * cos yy - sin xx * cos yy * bb - sin xx * sin yy * ll

theorem reduced_hasDerivAt_t (t xi eta : ℝ) :
    HasDerivAt (fun u => reduced b u xi eta) (derivT b t xi eta) t := by
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  have hx : HasDerivAt
      (fun u : ℝ => (b.centers 0 : ℝ) + b.slopes 0 * u + xi)
      (b.slopes 0 : ℝ) t := by
    convert ((hasDerivAt_const t (b.centers 0 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 0 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t xi) using 1 <;>
      first | rfl | ring_nf
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * u +
        b.yXiSlope * xi + eta) (b.slopes 1 : ℝ) t := by
    convert (((hasDerivAt_const t (b.centers 1 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 1 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t ((b.yXiSlope : ℝ) * xi))).add
          (hasDerivAt_const t eta) using 1 <;>
      first | rfl | ring_nf
  have hl : HasDerivAt (fun u : ℝ => (lamMid b : ℝ) + u) 1 t := by
    convert (hasDerivAt_const t (lamMid b : ℝ)).add (hasDerivAt_id t) using 1 <;>
      first | rfl | ring_nf
  have hxxs := (Real.hasDerivAt_sin xx).comp t hx
  have hxxc := (Real.hasDerivAt_cos xx).comp t hx
  have hyys := (Real.hasDerivAt_sin yy).comp t hy
  have hb := (((hl.mul hy).add (hasDerivAt_const t (π / 2))).sub hx)
  convert (hxxc.mul (hyys.sub hxxs)).sub ((hxxs.mul hyys).mul hb) using 1 <;>
    try rfl
  simp [Function.comp_apply, xx, yy, derivT]
  ring

theorem reduced_hasDerivAt_eta (t xi eta : ℝ) :
    HasDerivAt (fun u => reduced b t xi u) (derivEta b t xi eta) eta := by
  let xx := (b.centers 0 : ℝ) + b.slopes 0 * t + xi
  let yy := (b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi + eta
  have hy : HasDerivAt
      (fun u : ℝ => (b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi + u) 1 eta := by
    convert (hasDerivAt_const eta
      ((b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi)).add (hasDerivAt_id eta) using 1 <;>
      first | rfl | ring_nf
  have hyys : HasDerivAt
      (fun u : ℝ => sin ((b.centers 1 : ℝ) + b.slopes 1 * t +
        b.yXiSlope * xi + u)) (cos yy) eta := by
    convert (Real.hasDerivAt_sin yy).comp eta hy using 1 <;> try rfl
    ring
  have hb := (((hasDerivAt_const eta ((lamMid b : ℝ) + t)).mul hy).add
    (hasDerivAt_const eta (π / 2))).sub (hasDerivAt_const eta xx)
  convert ((hasDerivAt_const eta (cos xx)).mul
      (hyys.sub (hasDerivAt_const eta (sin xx)))).sub
        (((hasDerivAt_const eta (sin xx)).mul hyys).mul hb) using 1 <;>
    try rfl
  simp [derivEta, xx, yy]
  ring

/-- Uniform numerical derivative contract proved by each brick's exact
rational enclosure certificate on a lambda-centered interval of radius `R`.
The `t` derivative is needed only on the `eta = 0` leg of the path. -/
def DerivativeBoundsOn (R : ℝ) : Prop :=
  ∀ {t xi eta : ℝ},
    (-R ≤ t ∧ t ≤ R) →
    (-(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000) →
    (-(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) →
    |derivT b t xi 0| ≤ (1 / 200 : ℝ) ∧
      |derivEta b t xi eta| ≤ (61 / 100 : ℝ)

/-- Full-width compatibility specialization. -/
abbrev DerivativeBounds : Prop := DerivativeBoundsOn b (1 / 20000)

/-- Varying `t` and `eta` from a fixed `xi`-face anchor changes `F` by
less than `10⁻⁶`. -/
theorem face_deviation_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    {t xi eta : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    |reduced b t xi eta - reduced b 0 xi 0| ≤
      (1 / 1000000 : ℝ) := by
  have hzeroEta : (0 : ℝ) ∈
      Icc (-(1 / 1000000 : ℝ)) (1 / 1000000) := by
    constructor <;> norm_num
  have htChange :
      |reduced b t xi 0 - reduced b 0 xi 0| ≤
        (1 / 200 : ℝ) * |t| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := R) (u := t) hR ht
    · intro q _
      exact reduced_hasDerivAt_t b q xi 0
    · intro q hq
      exact (hderiv hq hxi hzeroEta).1
  have hetaChange :
      |reduced b t xi eta - reduced b t xi 0| ≤
        (61 / 100 : ℝ) * |eta| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := (1 / 1000000 : ℝ)) (u := eta) (by norm_num) heta
    · intro q _
      exact reduced_hasDerivAt_eta b t xi q
    · intro q hq
      exact (hderiv ht hxi hq).2
  have htAbs : |t| ≤ R := (abs_le).2 ht
  have hetaAbs : |eta| ≤ (1 / 1000000 : ℝ) := (abs_le).2 heta
  have htriangle :
      |reduced b t xi eta - reduced b 0 xi 0| ≤
        |reduced b t xi eta - reduced b t xi 0| +
          |reduced b t xi 0 - reduced b 0 xi 0| := by
    calc
      |reduced b t xi eta - reduced b 0 xi 0| =
          |(reduced b t xi eta - reduced b t xi 0) +
            (reduced b t xi 0 - reduced b 0 xi 0)| := by ring
      _ ≤ |reduced b t xi eta - reduced b t xi 0| +
          |reduced b t xi 0 - reduced b 0 xi 0| := abs_add_le _ _
  norm_num at htChange hetaChange htAbs hetaAbs htriangle ⊢
  nlinarith [hRmax]

theorem low_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (hanchor : (8 / 1000000 : ℝ) <
      reduced b 0 (-(1 / 100000 : ℝ)) 0)
    {t eta : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    (88 / 1000000000 : ℝ) <
      reduced b t (-(1 / 100000 : ℝ)) eta := by
  have hdev := face_deviation_on b hR hRmax hderiv ht
    (xi := -(1 / 100000 : ℝ)) (by constructor <;> norm_num) heta
  have hdevLo := (abs_le.mp hdev).1
  norm_num at hdevLo hanchor ⊢
  linarith

theorem high_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (hanchor : reduced b 0 (1 / 100000 : ℝ) 0 <
      -(8 / 1000000 : ℝ))
    {t eta : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    reduced b t (1 / 100000 : ℝ) eta <
      -(86 / 1000000000 : ℝ) := by
  have hdev := face_deviation_on b hR hRmax hderiv ht
    (xi := (1 / 100000 : ℝ)) (by constructor <;> norm_num) heta
  have hdevHi := (abs_le.mp hdev).2
  norm_num at hdevHi hanchor ⊢
  linarith

/-- Full-width compatibility specialization. -/
theorem face_deviation (hderiv : DerivativeBounds b)
    {t xi eta : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hxi : -(1 / 100000 : ℝ) ≤ xi ∧ xi ≤ 1 / 100000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    |reduced b t xi eta - reduced b 0 xi 0| ≤
      (1 / 1000000 : ℝ) :=
  face_deviation_on b (by norm_num) (by norm_num) hderiv ht hxi heta

/-- Full-width compatibility specialization. -/
theorem low_face_margin (hderiv : DerivativeBounds b)
    (hanchor : (8 / 1000000 : ℝ) <
      reduced b 0 (-(1 / 100000 : ℝ)) 0)
    {t eta : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    (88 / 1000000000 : ℝ) <
      reduced b t (-(1 / 100000 : ℝ)) eta :=
  low_face_margin_on b (by norm_num) (by norm_num) hderiv hanchor ht heta

/-- Full-width compatibility specialization. -/
theorem high_face_margin (hderiv : DerivativeBounds b)
    (hanchor : reduced b 0 (1 / 100000 : ℝ) 0 <
      -(8 / 1000000 : ℝ))
    {t eta : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (heta : -(1 / 1000000 : ℝ) ≤ eta ∧ eta ≤ 1 / 1000000) :
    reduced b t (1 / 100000 : ℝ) eta <
      -(86 / 1000000000 : ℝ) :=
  high_face_margin_on b (by norm_num) (by norm_num) hderiv hanchor ht heta

end FResidual

/-! ### Correlation-preserving type-(iii) Snell residual lane -/

/- Brick-parametric analytic machinery for the `C3` residual.

Individual bricks retain only their exact origin certificate, trigonometric
enclosures, and the resulting uniform derivative bounds. -/
namespace C3Residual

variable (b : Brick)

/-- Scalar form of `C3`, retaining the correlated `t`, `rho`, and `sigma`
variables used by the opposite-face certificate. -/
def reduced (t rho sigma : ℝ) : ℝ :=
  cos ((b.centers 2 : ℝ) + b.slopes 2 * t + rho) -
    ((lamMid b : ℝ) + t) *
      cos ((b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * rho + sigma)

theorem C3_pointOf_eq_reduced (t : ℝ) (z : Vec4) :
    Model.C3 b (Model.pointOf t z) = reduced b t (z 2) (z 3) := by
  rfl

/-- Derivative of the correlated `C3` residual in the brick parameter. -/
def derivT (t rho sigma : ℝ) : ℝ :=
  let ww := (b.centers 2 : ℝ) + b.slopes 2 * t + rho
  let vv := (b.centers 3 : ℝ) + b.slopes 3 * t +
    b.vRhoSlope * rho + sigma
  let ll := (lamMid b : ℝ) + t
  (-(b.slopes 2 : ℝ) * sin ww - cos vv +
    (b.slopes 3 : ℝ) * (ll * sin vv))

/-- Derivative of the correlated `C3` residual in the `rho` direction. -/
def derivRho (t rho sigma : ℝ) : ℝ :=
  let ww := (b.centers 2 : ℝ) + b.slopes 2 * t + rho
  let vv := (b.centers 3 : ℝ) + b.slopes 3 * t +
    b.vRhoSlope * rho + sigma
  let ll := (lamMid b : ℝ) + t
  (-sin ww + (b.vRhoSlope : ℝ) * (ll * sin vv))

/-- Derivative of the correlated `C3` residual in the `sigma` direction. -/
def derivSigma (t rho sigma : ℝ) : ℝ :=
  let vv := (b.centers 3 : ℝ) + b.slopes 3 * t +
    b.vRhoSlope * rho + sigma
  ((lamMid b : ℝ) + t) * sin vv

theorem reduced_hasDerivAt_t (t rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b u rho sigma)
      (derivT b t rho sigma) t := by
  have hw : HasDerivAt
      (fun u : ℝ => (b.centers 2 : ℝ) + b.slopes 2 * u + rho)
      (b.slopes 2 : ℝ) t := by
    convert ((hasDerivAt_const t (b.centers 2 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 2 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t rho) using 1 <;>
      first | rfl | ring_nf
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * u +
        b.vRhoSlope * rho + sigma) (b.slopes 3 : ℝ) t := by
    convert (((hasDerivAt_const t (b.centers 3 : ℝ)).add
      ((hasDerivAt_const t (b.slopes 3 : ℝ)).mul (hasDerivAt_id t))).add
        (hasDerivAt_const t ((b.vRhoSlope : ℝ) * rho))).add
          (hasDerivAt_const t sigma) using 1 <;>
      first | rfl | ring_nf
  have hl : HasDerivAt (fun u : ℝ => (lamMid b : ℝ) + u) 1 t := by
    convert (hasDerivAt_const t (lamMid b : ℝ)).add (hasDerivAt_id t) using 1 <;>
      first | rfl | ring_nf
  convert ((Real.hasDerivAt_cos _).comp t hw).sub
      (hl.mul ((Real.hasDerivAt_cos _).comp t hv)) using 1 <;> try rfl
  simp [derivT, Function.comp_apply]
  ring

theorem reduced_hasDerivAt_rho (t rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t u sigma)
      (derivRho b t rho sigma) rho := by
  have hw : HasDerivAt
      (fun u : ℝ => (b.centers 2 : ℝ) + b.slopes 2 * t + u) 1 rho := by
    convert (hasDerivAt_const rho
      ((b.centers 2 : ℝ) + b.slopes 2 * t)).add (hasDerivAt_id rho) using 1 <;>
      first | rfl | ring_nf
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * u + sigma) (b.vRhoSlope : ℝ) rho := by
    convert (((hasDerivAt_const rho
      ((b.centers 3 : ℝ) + b.slopes 3 * t)).add
        ((hasDerivAt_const rho (b.vRhoSlope : ℝ)).mul
          (hasDerivAt_id rho))).add (hasDerivAt_const rho sigma)) using 1 <;>
      first | rfl | ring_nf
  convert ((Real.hasDerivAt_cos _).comp rho hw).sub
      ((hasDerivAt_const rho ((lamMid b : ℝ) + t)).mul
        ((Real.hasDerivAt_cos _).comp rho hv)) using 1 <;> try rfl
  simp [derivRho, Function.comp_apply]
  ring

theorem reduced_hasDerivAt_sigma (t rho sigma : ℝ) :
    HasDerivAt (fun u => reduced b t rho u)
      (derivSigma b t rho sigma) sigma := by
  have hv : HasDerivAt
      (fun u : ℝ => (b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * rho + u) 1 sigma := by
    convert (hasDerivAt_const sigma
      ((b.centers 3 : ℝ) + b.slopes 3 * t +
        b.vRhoSlope * rho)).add (hasDerivAt_id sigma) using 1 <;>
      first | rfl | ring_nf
  convert (hasDerivAt_const sigma
      (cos ((b.centers 2 : ℝ) + b.slopes 2 * t + rho))).sub
    ((hasDerivAt_const sigma ((lamMid b : ℝ) + t)).mul
      ((Real.hasDerivAt_cos _).comp sigma hv)) using 1 <;> try rfl
  simp [derivSigma, Function.comp_apply]

/-- Uniform numerical derivative contract proved by each brick's exact
rational enclosure certificate on a lambda-centered interval of radius `R`.
The `t` and `rho` derivatives are needed only on the `rho = sigma = 0` and
`sigma = 0` legs, respectively. -/
def DerivativeBoundsOn (R : ℝ) : Prop :=
  ∀ {t rho sigma : ℝ},
    (-R ≤ t ∧ t ≤ R) →
    (-(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) →
    (-(1 / 1000000 : ℝ) ≤ sigma ∧ sigma ≤ 1 / 1000000) →
    |derivT b t 0 0| ≤ (3 / 500 : ℝ) ∧
      |derivRho b t rho 0| ≤ (1 / 1000 : ℝ) ∧
      (9 / 20 : ℝ) ≤ derivSigma b t rho sigma

/-- Full-width compatibility specialization. -/
abbrev DerivativeBounds : Prop := DerivativeBoundsOn b (1 / 20000)

/-- At `sigma = 0`, the correlated `C3` residual stays below `4 · 10⁻⁷`. -/
theorem sigma_zero_abs_lt_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    |reduced b t rho 0| < (2 / 5000000 : ℝ) := by
  have hzeroRho : (0 : ℝ) ∈ Icc (-(1 / 100000)) (1 / 100000) := by
    constructor <;> norm_num
  have hzeroSigma : (0 : ℝ) ∈ Icc (-(1 / 1000000)) (1 / 1000000) := by
    constructor <;> norm_num
  have htChange :
      |reduced b t 0 0 - reduced b 0 0 0| ≤
        (3 / 500 : ℝ) * |t| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := R) (u := t) hR ht
    · intro q _
      exact reduced_hasDerivAt_t b q 0 0
    · intro q hq
      exact (hderiv hq hzeroRho hzeroSigma).1
  have hrhoChange :
      |reduced b t rho 0 - reduced b t 0 0| ≤
        (1 / 1000 : ℝ) * |rho| := by
    apply EResidual.abs_image_sub_le_of_hasDerivAt
      (R := (1 / 100000 : ℝ)) (u := rho) (by norm_num) hrho
    · intro q _
      exact reduced_hasDerivAt_rho b t q 0
    · intro q hq
      exact (hderiv ht hq hzeroSigma).2.1
  have htAbs : |t| ≤ R := (abs_le).2 ht
  have hrhoAbs : |rho| ≤ (1 / 100000 : ℝ) := (abs_le).2 hrho
  have hsum :
      |reduced b t rho 0| ≤
        |reduced b t rho 0 - reduced b t 0 0| +
          |reduced b t 0 0 - reduced b 0 0 0| +
            |reduced b 0 0 0| := by
    calc
      |reduced b t rho 0| =
          |(reduced b t rho 0 - reduced b t 0 0) +
            (reduced b t 0 0 - reduced b 0 0 0) +
              reduced b 0 0 0| := by ring
      _ ≤ |(reduced b t rho 0 - reduced b t 0 0) +
              (reduced b t 0 0 - reduced b 0 0 0)| +
            |reduced b 0 0 0| := abs_add_le _ _
      _ ≤ |reduced b t rho 0 - reduced b t 0 0| +
              |reduced b t 0 0 - reduced b 0 0 0| +
            |reduced b 0 0 0| := by
        have hab := abs_add_le
          (reduced b t rho 0 - reduced b t 0 0)
          (reduced b t 0 0 - reduced b 0 0 0)
        linarith
  norm_num at htChange hrhoChange htAbs hrhoAbs hanchor hsum ⊢
  nlinarith [hRmax]

/-- Quantitative monotonicity in `sigma` on the complete brick. -/
theorem sigma_growth_on {R : ℝ} (hderiv : DerivativeBoundsOn b R)
    {t rho sigma₁ sigma₂ : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000)
    (hsigma₁ : sigma₁ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (hsigma₂ : sigma₂ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (hsigma : sigma₁ ≤ sigma₂) :
    (9 / 20 : ℝ) * (sigma₂ - sigma₁) ≤
      reduced b t rho sigma₂ - reduced b t rho sigma₁ := by
  apply (convex_Icc (-(1 / 1000000 : ℝ))
    (1 / 1000000 : ℝ)).mul_sub_le_image_sub_of_le_deriv
      (by unfold reduced; fun_prop) (by unfold reduced; fun_prop) ?_
        sigma₁ hsigma₁ sigma₂ hsigma₂ hsigma
  intro q hq
  have hq' : -(1 / 1000000 : ℝ) ≤ q ∧ q ≤ 1 / 1000000 := by
    have hi : -(1 / 1000000 : ℝ) < q ∧ q < 1 / 1000000 := by
      simpa only [interior_Icc, mem_Ioo] using hq
    exact ⟨hi.1.le, hi.2.le⟩
  rw [(reduced_hasDerivAt_sigma b t rho q).deriv]
  exact (hderiv ht hrho hq').2.2

/-- The lower `sigma` face has the required `C3` sign. -/
theorem low_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    reduced b t rho (-(1 / 1000000 : ℝ)) <
      -(1 / 1000000000 : ℝ) := by
  have hzero := sigma_zero_abs_lt_on b hR hRmax hderiv hanchor ht hrho
  have hgrowth := sigma_growth_on b hderiv ht hrho
    (sigma₁ := -(1 / 1000000 : ℝ)) (sigma₂ := 0)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroHi := (abs_lt.mp hzero).2
  norm_num at hgrowth hzeroHi ⊢
  linarith

/-- The upper `sigma` face has the required `C3` sign. -/
theorem high_face_margin_on {R : ℝ} (hR : 0 ≤ R)
    (hRmax : R ≤ (1 / 20000 : ℝ)) (hderiv : DerivativeBoundsOn b R)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -R ≤ t ∧ t ≤ R)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    (1 / 1000000000 : ℝ) <
      reduced b t rho (1 / 1000000 : ℝ) := by
  have hzero := sigma_zero_abs_lt_on b hR hRmax hderiv hanchor ht hrho
  have hgrowth := sigma_growth_on b hderiv ht hrho
    (sigma₁ := 0) (sigma₂ := (1 / 1000000 : ℝ))
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  have hzeroLo := (abs_lt.mp hzero).1
  norm_num at hgrowth hzeroLo ⊢
  linarith

/-- Full-width compatibility specialization. -/
theorem sigma_zero_abs_lt (hderiv : DerivativeBounds b)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    |reduced b t rho 0| < (2 / 5000000 : ℝ) :=
  sigma_zero_abs_lt_on b (by norm_num) (by norm_num) hderiv hanchor ht hrho

/-- Full-width compatibility specialization. -/
theorem sigma_growth (hderiv : DerivativeBounds b)
    {t rho sigma₁ sigma₂ : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000)
    (hsigma₁ : sigma₁ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (hsigma₂ : sigma₂ ∈ Icc (-(1 / 1000000 : ℝ)) (1 / 1000000))
    (hsigma : sigma₁ ≤ sigma₂) :
    (9 / 20 : ℝ) * (sigma₂ - sigma₁) ≤
      reduced b t rho sigma₂ - reduced b t rho sigma₁ :=
  sigma_growth_on b hderiv ht hrho hsigma₁ hsigma₂ hsigma

/-- Full-width compatibility specialization. -/
theorem low_face_margin (hderiv : DerivativeBounds b)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    reduced b t rho (-(1 / 1000000 : ℝ)) <
      -(1 / 1000000000 : ℝ) :=
  low_face_margin_on b (by norm_num) (by norm_num) hderiv hanchor ht hrho

/-- Full-width compatibility specialization. -/
theorem high_face_margin (hderiv : DerivativeBounds b)
    (hanchor : |reduced b 0 0 0| < (1 / 25000000 : ℝ))
    {t rho : ℝ}
    (ht : -(1 / 20000 : ℝ) ≤ t ∧ t ≤ 1 / 20000)
    (hrho : -(1 / 100000 : ℝ) ≤ rho ∧ rho ≤ 1 / 100000) :
    (1 / 1000000000 : ℝ) <
      reduced b t rho (1 / 1000000 : ℝ) :=
  high_face_margin_on b (by norm_num) (by norm_num) hderiv hanchor ht hrho

end C3Residual

open Model

/-- Strict semantic decisions emitted by the middle-face interval checker.

The brick itself carries the six exact rational input fields.  This record
separates the checker decisions by residual and face, matching the retained
diagnostic schema while keeping every decision proof-valued. -/
structure CellCertificate (b : Brick) : Prop where
  lambda_one_lt : ∀ t, (tInterval b).RealContains t →
    1 < lam b (pointOf t 0)
  branches : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    let p := pointOf t z
    0 < x b p ∧ x b p < π / 4 ∧
    0 < y b p ∧ y b p < π / 4 ∧
    0 < w b p ∧ w b p < π / 4 ∧
    0 < v b p ∧ v b p < π / 4
  F_xi_low_pos : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 0 = -radiiReal b 0 → 0 < F b (pointOf t z)
  F_xi_high_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 0 = radiiReal b 0 → F b (pointOf t z) < 0
  C4_eta_low_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 1 = -radiiReal b 1 → C4 b (pointOf t z) < 0
  C4_eta_high_pos : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 1 = radiiReal b 1 → 0 < C4 b (pointOf t z)
  E_rho_low_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 2 = -radiiReal b 2 → E b (pointOf t z) < 0
  E_rho_high_pos : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 2 = radiiReal b 2 → 0 < E b (pointOf t z)
  C3_sigma_low_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 3 = -radiiReal b 3 → C3 b (pointOf t z) < 0
  C3_sigma_high_pos : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    z 3 = radiiReal b 3 → 0 < C3 b (pointOf t z)
  K3_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z → K3 b (pointOf t z) < 0
  G_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z → G b (pointOf t z) < 0

/-- Numerical obligations discharged by an exact-rational middle-face checker.
The fields state primitive checker facts, not a candidate-facing conclusion. -/
structure Conditions (b : Brick) : Prop where
  lambda_one_lt : ∀ t, (tInterval b).RealContains t → 1 < lam b (pointOf t 0)
  branches : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    let p := pointOf t z
    0 < x b p ∧ x b p < π / 4 ∧
    0 < y b p ∧ y b p < π / 4 ∧
    0 < w b p ∧ w b p < π / 4 ∧
    0 < v b p ∧ v b p < π / 4
  lowFaces : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    ∀ j, z j = -radiiReal b j → rootMap b t z j < 0
  highFaces : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z →
    ∀ j, z j = radiiReal b j → 0 < rootMap b t z j
  K3_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z → K3 b (pointOf t z) < 0
  G_neg : ∀ t z, (tInterval b).RealContains t →
    InSymmetricBox (radiiReal b) z → G b (pointOf t z) < 0

namespace CellCertificate

/-- The checker decisions have exactly the orientation required by the
Poincaré--Miranda root assembly.  In particular, the first component of
`rootMap` is `-F`, so its two face decisions reverse orientation. -/
theorem sound {b : Brick} (certificate : CellCertificate b) : Conditions b where
  lambda_one_lt := certificate.lambda_one_lt
  branches := certificate.branches
  lowFaces := by
    intro t z ht hz j hj
    fin_cases j
    · simpa [rootMap] using
        (neg_lt_zero.mpr (certificate.F_xi_low_pos t z ht hz hj))
    · simpa [rootMap] using certificate.C4_eta_low_neg t z ht hz hj
    · simpa [rootMap] using certificate.E_rho_low_neg t z ht hz hj
    · simpa [rootMap] using certificate.C3_sigma_low_neg t z ht hz hj
  highFaces := by
    intro t z ht hz j hj
    fin_cases j
    · simpa [rootMap] using
        (neg_pos.mpr (certificate.F_xi_high_neg t z ht hz hj))
    · simpa [rootMap] using certificate.C4_eta_high_pos t z ht hz hj
    · simpa [rootMap] using certificate.E_rho_high_pos t z ht hz hj
    · simpa [rootMap] using certificate.C3_sigma_high_pos t z ht hz hj
  K3_neg := certificate.K3_neg
  G_neg := certificate.G_neg

end CellCertificate

/-- The exact analytic interpretation of the checker coordinates on the
recorded angle branch.  Its equation and sign consequences remain separate
from the primitive numerical conditions. -/
structure PointEquationSemantics (b : Brick) (p : Point) : Prop where
  typeThreeHeight_gt_half : 1 / 2 < (1 + cos (w b p)) / 2
  typeThreeHeight_lt_one : (1 + cos (w b p)) / 2 < 1
  typeFourHeight_pos : 0 < cos (x b p)
  typeFourHeight_lt_one : cos (x b p) < 1
  equalArea_of_E_zero : E b p = 0 →
    LeanSuffixAnalytic.typeThreeArea (lam b p) ((1 + cos (w b p)) / 2) =
      LeanSuffixAnalytic.typeFourArea (lam b p) (cos (x b p))
  stationary_of_F_zero : F b p = 0 →
    LeanSuffixAnalytic.typeFourFold (lam b p) (cos (x b p)) = 0
  perimeter_lt_of_G_neg : G b p < 0 →
    LeanSuffixAnalytic.typeThreePerimeter (lam b p) ((1 + cos (w b p)) / 2) <
      LeanSuffixAnalytic.typeFourPerimeter (lam b p) (cos (x b p))

/-- Honest analytic semantics of the reusable checker model. -/
theorem pointEquationSemantics (b : Brick) (p : Point) (hlam : 1 < lam b p)
    (hbranches :
      0 < x b p ∧ x b p < π / 4 ∧
      0 < y b p ∧ y b p < π / 4 ∧
      0 < w b p ∧ w b p < π / 4 ∧
      0 < v b p ∧ v b p < π / 4)
    (hC4 : C4 b p = 0) (hC3 : C3 b p = 0) :
    PointEquationSemantics b p := by
  rcases hbranches with ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  have hpi4_lt_pi : π / 4 < π := by linarith [Real.pi_pos]
  have hpi4_lt_pi_div_two : π / 4 < π / 2 := by linarith [Real.pi_pos]
  have hxpi : x b p < π := hxq.trans hpi4_lt_pi
  have hypi : y b p < π := hyq.trans hpi4_lt_pi
  have hwpi : w b p < π := hwq.trans hpi4_lt_pi
  have hvpi : v b p < π := hvq.trans hpi4_lt_pi
  have hlam_pos : 0 < lam b p := lt_trans (by norm_num) hlam
  have hxcos_pos : 0 < cos (x b p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hxq.trans hpi4_lt_pi_div_two⟩
  have hwcos_pos : 0 < cos (w b p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hwq.trans hpi4_lt_pi_div_two⟩
  have hzero_mem : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hx_mem : x b p ∈ Icc 0 π := ⟨hx0.le, hxpi.le⟩
  have hw_mem : w b p ∈ Icc 0 π := ⟨hw0.le, hwpi.le⟩
  have hxcos_lt_one : cos (x b p) < 1 := by
    simpa using Real.strictAntiOn_cos hzero_mem hx_mem hx0
  have hwcos_lt_one : cos (w b p) < 1 := by
    simpa using Real.strictAntiOn_cos hzero_mem hw_mem hw0
  have hxsin_pos : 0 < sin (x b p) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hysin_pos : 0 < sin (y b p) :=
    Real.sin_pos_of_pos_of_lt_pi hy0 hypi
  have hwsin_pos : 0 < sin (w b p) :=
    Real.sin_pos_of_pos_of_lt_pi hw0 hwpi
  have hvsin_pos : 0 < sin (v b p) :=
    Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
  have hcos_xy : cos (x b p) = lam b p * cos (y b p) := by
    unfold C4 at hC4
    linarith
  have hcos_wv : cos (w b p) = lam b p * cos (v b p) := by
    unfold C3 at hC3
    linarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape ((1 + cos (w b p)) / 2) =
        cos (w b p) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hcos_xy_div : cos (x b p) / lam b p = cos (y b p) := by
    rw [hcos_xy]
    field_simp [ne_of_gt hlam_pos]
  have hcos_wv_div : cos (w b p) / lam b p = cos (v b p) := by
    rw [hcos_wv]
    field_simp [ne_of_gt hlam_pos]
  have hB4 :
      LeanSuffixAnalytic.typeFourAngle (lam b p) (cos (x b p)) = B4 b p := by
    rw [LeanSuffixAnalytic.typeFourAngle_eq_checker, hcos_xy_div,
      Real.arccos_cos hy0.le hypi.le, Real.arccos_cos hx0.le hxpi.le]
    rfl
  have hB3 :
      LeanSuffixAnalytic.typeThreeAngle (lam b p)
          ((1 + cos (w b p)) / 2) + π / 2 = B3 b p := by
    rw [LeanSuffixAnalytic.typeThreeAngle_add_halfPi, hshape, hcos_wv_div,
      Real.arccos_cos hv0.le hvpi.le, Real.arccos_cos hw0.le hwpi.le]
    rfl
  have hsqrt_x : sqrt (1 - cos (x b p) ^ 2) = sin (x b p) := by
    have htrig := Real.sin_sq_add_cos_sq (x b p)
    rw [show 1 - cos (x b p) ^ 2 = sin (x b p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hxsin_pos]
  have hsqrt_w : sqrt (1 - cos (w b p) ^ 2) = sin (w b p) := by
    have htrig := Real.sin_sq_add_cos_sq (w b p)
    rw [show 1 - cos (w b p) ^ 2 = sin (w b p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hwsin_pos]
  have hsqrt_lam_x :
      sqrt (lam b p ^ 2 - cos (x b p) ^ 2) = lam b p * sin (y b p) := by
    have htrig := Real.sin_sq_add_cos_sq (y b p)
    rw [show lam b p ^ 2 - cos (x b p) ^ 2 =
        (lam b p * sin (y b p)) ^ 2 by
      rw [hcos_xy]
      linear_combination -(lam b p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hysin_pos)]
  have hsqrt_lam_w :
      sqrt (lam b p ^ 2 - cos (w b p) ^ 2) = lam b p * sin (v b p) := by
    have htrig := Real.sin_sq_add_cos_sq (v b p)
    rw [show lam b p ^ 2 - cos (w b p) ^ 2 =
        (lam b p * sin (v b p)) ^ 2 by
      rw [hcos_wv]
      linear_combination -(lam b p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hvsin_pos)]
  have hD4 :
      LeanSuffixAnalytic.typeFourDelta (lam b p) (cos (x b p)) = D4 b p := by
    rw [LeanSuffixAnalytic.typeFourDelta, hsqrt_lam_x, hsqrt_x]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hD3 :
      LeanSuffixAnalytic.typeThreeDelta (lam b p)
          ((1 + cos (w b p)) / 2) = D3 b p := by
    rw [LeanSuffixAnalytic.typeThreeDelta, hshape, hsqrt_lam_w, hsqrt_w]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hh3_pos : 0 < (1 + cos (w b p)) / 2 := by linarith
  have hh4_pos : 0 < cos (x b p) := hxcos_pos
  have equalArea_of_E_zero (hE : E b p = 0) :
      LeanSuffixAnalytic.typeThreeArea (lam b p) ((1 + cos (w b p)) / 2) =
        LeanSuffixAnalytic.typeFourArea (lam b p) (cos (x b p)) := by
    rw [LeanSuffixAnalytic.typeThreeArea, LeanSuffixAnalytic.typeFourArea,
      hshape, hB3, hD3, hB4, hD4]
    apply (div_eq_div_iff (pow_ne_zero 2 (ne_of_gt hh3_pos))
      (pow_ne_zero 2 (ne_of_gt hh4_pos))).2
    unfold E N3 N4 at hE
    linear_combination (1 / 2 : ℝ) * hE
  have stationary_of_F_zero (hF : F b p = 0) :
      LeanSuffixAnalytic.typeFourFold (lam b p) (cos (x b p)) = 0 := by
    have hden_ne : sin (x b p) * sin (y b p) ≠ 0 :=
      mul_ne_zero (ne_of_gt hxsin_pos) (ne_of_gt hysin_pos)
    have hnumerator :
        cos (x b p) * (sin (y b p) - sin (x b p)) =
          sin (x b p) * sin (y b p) * B4 b p := by
      unfold Model.F D4 at hF
      linarith
    have hcore :
        cos (x b p) * (1 / sin (x b p) - 1 / sin (y b p)) = B4 b p := by
      calc
        cos (x b p) * (1 / sin (x b p) - 1 / sin (y b p)) =
            (cos (x b p) * (sin (y b p) - sin (x b p))) /
              (sin (x b p) * sin (y b p)) := by
                field_simp [ne_of_gt hxsin_pos, ne_of_gt hysin_pos]
        _ = B4 b p := (div_eq_iff hden_ne).2 (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hnumerator)
    have hcancel : lam b p / (lam b p * sin (y b p)) =
        1 / sin (y b p) := by
      field_simp [ne_of_gt hlam_pos, ne_of_gt hysin_pos]
    rw [LeanSuffixAnalytic.typeFourFold, hsqrt_x, hsqrt_lam_x, hB4,
      hcancel, hcore]
    ring
  have perimeter_lt_of_G_neg (hG : G b p < 0) :
      LeanSuffixAnalytic.typeThreePerimeter (lam b p)
          ((1 + cos (w b p)) / 2) <
        LeanSuffixAnalytic.typeFourPerimeter (lam b p) (cos (x b p)) := by
    rw [LeanSuffixAnalytic.typeThreePerimeter,
      LeanSuffixAnalytic.typeFourPerimeter, hB3, hD3, hB4]
    apply (div_lt_div_iff₀ hh3_pos hh4_pos).2
    unfold G at hG
    nlinarith
  exact ⟨by linarith, by linarith, hxcos_pos, hxcos_lt_one,
    equalArea_of_E_zero, stationary_of_F_zero, perimeter_lt_of_G_neg⟩

/-- The checker `K3` is the numerator of the actual type-(iii) area
derivative on the certified branch. -/
theorem typeThreeArea_deriv_eq_K3 (b : Brick) (p : Point)
    (hlam : 1 < lam b p)
    (hbranches :
      0 < w b p ∧ w b p < π / 4 ∧ 0 < v b p ∧ v b p < π / 4)
    (hC3 : C3 b p = 0) :
    deriv (LeanSuffixAnalytic.typeThreeArea (lam b p))
        ((1 + cos (w b p)) / 2) =
      K3 b p / ((1 + cos (w b p)) / 2) ^ 3 := by
  rcases hbranches with ⟨hw0, hwq, hv0, hvq⟩
  have hpi4_lt_pi : π / 4 < π := by linarith [Real.pi_pos]
  have hpi4_lt_pi_div_two : π / 4 < π / 2 := by
    linarith [Real.pi_pos]
  have hwpi : w b p < π := hwq.trans hpi4_lt_pi
  have hvpi : v b p < π := hvq.trans hpi4_lt_pi
  have hlam_pos : 0 < lam b p := lt_trans (by norm_num) hlam
  have hwcos_pos : 0 < cos (w b p) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hwq.trans hpi4_lt_pi_div_two⟩
  have hzero_mem : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
  have hw_mem : w b p ∈ Icc 0 π := ⟨hw0.le, hwpi.le⟩
  have hwcos_lt_one : cos (w b p) < 1 := by
    simpa using Real.strictAntiOn_cos hzero_mem hw_mem hw0
  have hwsin_pos : 0 < sin (w b p) :=
    Real.sin_pos_of_pos_of_lt_pi hw0 hwpi
  have hvsin_pos : 0 < sin (v b p) :=
    Real.sin_pos_of_pos_of_lt_pi hv0 hvpi
  have hcos_wv : cos (w b p) = lam b p * cos (v b p) := by
    unfold C3 at hC3
    linarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape ((1 + cos (w b p)) / 2) =
        cos (w b p) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hcos_wv_div : cos (w b p) / lam b p = cos (v b p) := by
    rw [hcos_wv]
    field_simp [ne_of_gt hlam_pos]
  have hB3 :
      LeanSuffixAnalytic.typeThreeAngle (lam b p)
          ((1 + cos (w b p)) / 2) + π / 2 = B3 b p := by
    rw [LeanSuffixAnalytic.typeThreeAngle_add_halfPi, hshape, hcos_wv_div,
      Real.arccos_cos hv0.le hvpi.le, Real.arccos_cos hw0.le hwpi.le]
    rfl
  have hsqrt_w : sqrt (1 - cos (w b p) ^ 2) = sin (w b p) := by
    have htrig := Real.sin_sq_add_cos_sq (w b p)
    rw [show 1 - cos (w b p) ^ 2 = sin (w b p) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs, abs_of_pos hwsin_pos]
  have hsqrt_lam_w :
      sqrt (lam b p ^ 2 - cos (w b p) ^ 2) = lam b p * sin (v b p) := by
    have htrig := Real.sin_sq_add_cos_sq (v b p)
    rw [show lam b p ^ 2 - cos (w b p) ^ 2 =
        (lam b p * sin (v b p)) ^ 2 by
      rw [hcos_wv]
      linear_combination -(lam b p) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hlam_pos hvsin_pos)]
  have hD3 :
      LeanSuffixAnalytic.typeThreeDelta (lam b p)
          ((1 + cos (w b p)) / 2) = D3 b p := by
    rw [LeanSuffixAnalytic.typeThreeDelta, hshape, hsqrt_lam_w, hsqrt_w]
    field_simp [ne_of_gt hlam_pos]
    rfl
  have hh3_pos : 0 < (1 + cos (w b p)) / 2 := by linarith
  have hh3_one : (1 + cos (w b p)) / 2 < 1 := by linarith
  rw [LeanSuffixAnalytic.typeThreeArea_deriv_eq_explicit
    hlam hh3_pos hh3_one, hshape, hsqrt_w, hsqrt_lam_w, hB3, hD3]
  unfold K3
  dsimp only
  field_simp [ne_of_gt hlam_pos, ne_of_gt hwsin_pos, ne_of_gt hvsin_pos]
  ring

namespace Conditions

variable {b : Brick}

private theorem radiiReal_pos (j : Fin 4) : 0 < radiiReal b j := by
  change 0 < (b.radii j : ℝ)
  exact_mod_cast b.radiiPos j

private theorem zero_mem_coordinate (j : Fin 4) :
    (0 : ℝ) ∈ Icc (-radiiReal b j) (radiiReal b j) :=
  ⟨(neg_lt_zero.mpr (radiiReal_pos j)).le, (radiiReal_pos j).le⟩

private theorem vector_mem_box {xi eta rho sigma : ℝ}
    (hxi : xi ∈ Icc (-radiiReal b 0) (radiiReal b 0))
    (heta : eta ∈ Icc (-radiiReal b 1) (radiiReal b 1))
    (hrho : rho ∈ Icc (-radiiReal b 2) (radiiReal b 2))
    (hsigma : sigma ∈ Icc (-radiiReal b 3) (radiiReal b 3)) :
    InSymmetricBox (radiiReal b) ![xi, eta, rho, sigma] := by
  intro j
  fin_cases j
  · simpa using hxi
  · simpa using heta
  · simpa [Matrix.cons_val_two] using hrho
  · simpa [Matrix.cons_val_three] using hsigma

private def etaRoot (b : Brick) (t xi : ℝ) : ℝ :=
  arccos
      (cos ((b.centers 0 : ℝ) + b.slopes 0 * t + xi) /
        ((lamMid b : ℝ) + t)) -
    ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi)

private theorem etaRoot_continuous (b : Brick) (t : ℝ) :
    Continuous (etaRoot b t) := by
  unfold etaRoot
  fun_prop

private theorem etaRoot_spec (conditions : Conditions b) {t xi : ℝ}
    (ht : (tInterval b).RealContains t)
    (hxi : xi ∈ Icc (-radiiReal b 0) (radiiReal b 0)) :
    etaRoot b t xi ∈ Icc (-radiiReal b 1) (radiiReal b 1) ∧
      C4 b (pointOf t ![xi, etaRoot b t xi, 0, 0]) = 0 := by
  let zAt : ℝ → Vec4 := fun eta => ![xi, eta, 0, 0]
  have hz (eta : ℝ) (heta : eta ∈ Icc (-radiiReal b 1) (radiiReal b 1)) :
      InSymmetricBox (radiiReal b) (zAt eta) :=
    vector_mem_box hxi heta (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hlo : C4 b (pointOf t (zAt (-radiiReal b 1))) ≤ 0 := by
    have h := conditions.lowFaces t _ ht
      (hz _ ⟨le_rfl, neg_le_self (radiiReal_pos 1).le⟩) 1 (by simp [zAt])
    simpa [rootMap] using h.le
  have hhi : 0 ≤ C4 b (pointOf t (zAt (radiiReal b 1))) := by
    have h := conditions.highFaces t _ ht
      (hz _ ⟨neg_le_self (radiiReal_pos 1).le, le_rfl⟩) 1 (by simp [zAt])
    simpa [rootMap] using h.le
  have hcont : Continuous (fun eta => C4 b (pointOf t (zAt eta))) := by
    unfold C4 pointOf x y lam
    fun_prop
  rcases oppositeFace_zero (neg_le_self (radiiReal_pos 1).le)
      hcont.continuousOn hlo hhi with ⟨eta, heta, hzero⟩
  let p := pointOf t (zAt eta)
  have hzeta : InSymmetricBox (radiiReal b) (zAt eta) := hz eta heta
  rcases conditions.branches t (zAt eta) ht hzeta with
    ⟨_, _, hy0, hyq, _, _, _, _⟩
  have hlamPos : 0 < lam b p := by
    have h := conditions.lambda_one_lt t ht
    simpa [p, zAt, lam, pointOf] using h.trans' (by norm_num)
  have hC4 : C4 b p = 0 := by simpa [p] using hzero
  have hratio : cos (x b p) / lam b p = cos (y b p) := by
    apply (div_eq_iff (ne_of_gt hlamPos)).2
    unfold C4 at hC4
    nlinarith
  have harccos : arccos (cos (x b p) / lam b p) = y b p :=
    Real.arccos_eq_of_eq_cos hy0.le
      (hyq.trans (by linarith [Real.pi_pos])).le hratio
  have hetaEq : etaRoot b t xi = eta := by
    calc
      etaRoot b t xi = arccos (cos (x b p) / lam b p) -
          ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi) := by rfl
      _ = y b p -
          ((b.centers 1 : ℝ) + b.slopes 1 * t + b.yXiSlope * xi) := by rw [harccos]
      _ = eta := by simp [p, zAt, y, pointOf]
  rw [hetaEq]
  exact ⟨heta, hzero⟩

private def sigmaRoot (b : Brick) (t rho : ℝ) : ℝ :=
  arccos
      (cos ((b.centers 2 : ℝ) + b.slopes 2 * t + rho) /
        ((lamMid b : ℝ) + t)) -
    ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho)

private theorem sigmaRoot_continuous (b : Brick) (t : ℝ) :
    Continuous (sigmaRoot b t) := by
  unfold sigmaRoot
  fun_prop

private theorem sigmaRoot_spec (conditions : Conditions b) {t rho : ℝ}
    (ht : (tInterval b).RealContains t)
    (hrho : rho ∈ Icc (-radiiReal b 2) (radiiReal b 2)) :
    sigmaRoot b t rho ∈ Icc (-radiiReal b 3) (radiiReal b 3) ∧
      C3 b (pointOf t ![0, 0, rho, sigmaRoot b t rho]) = 0 := by
  let zAt : ℝ → Vec4 := fun sigma => ![0, 0, rho, sigma]
  have hz (sigma : ℝ) (hsigma : sigma ∈ Icc (-radiiReal b 3) (radiiReal b 3)) :
      InSymmetricBox (radiiReal b) (zAt sigma) :=
    vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1) hrho hsigma
  have hlo : C3 b (pointOf t (zAt (-radiiReal b 3))) ≤ 0 := by
    have h := conditions.lowFaces t _ ht
      (hz _ ⟨le_rfl, neg_le_self (radiiReal_pos 3).le⟩) 3 (by simp [zAt])
    simpa [rootMap] using h.le
  have hhi : 0 ≤ C3 b (pointOf t (zAt (radiiReal b 3))) := by
    have h := conditions.highFaces t _ ht
      (hz _ ⟨neg_le_self (radiiReal_pos 3).le, le_rfl⟩) 3 (by simp [zAt])
    simpa [rootMap] using h.le
  have hcont : Continuous (fun sigma => C3 b (pointOf t (zAt sigma))) := by
    unfold C3 pointOf w v lam
    fun_prop
  rcases oppositeFace_zero (neg_le_self (radiiReal_pos 3).le)
      hcont.continuousOn hlo hhi with ⟨sigma, hsigma, hzero⟩
  let p := pointOf t (zAt sigma)
  have hzsigma : InSymmetricBox (radiiReal b) (zAt sigma) := hz sigma hsigma
  rcases conditions.branches t (zAt sigma) ht hzsigma with
    ⟨_, _, _, _, _, _, hv0, hvq⟩
  have hlamPos : 0 < lam b p := by
    have h := conditions.lambda_one_lt t ht
    simpa [p, zAt, lam, pointOf] using h.trans' (by norm_num)
  have hC3 : C3 b p = 0 := by simpa [p] using hzero
  have hratio : cos (w b p) / lam b p = cos (v b p) := by
    apply (div_eq_iff (ne_of_gt hlamPos)).2
    unfold C3 at hC3
    nlinarith
  have harccos : arccos (cos (w b p) / lam b p) = v b p :=
    Real.arccos_eq_of_eq_cos hv0.le
      (hvq.trans (by linarith [Real.pi_pos])).le hratio
  have hsigmaEq : sigmaRoot b t rho = sigma := by
    calc
      sigmaRoot b t rho = arccos (cos (w b p) / lam b p) -
          ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho) := by rfl
      _ = v b p -
          ((b.centers 3 : ℝ) + b.slopes 3 * t + b.vRhoSlope * rho) := by rw [harccos]
      _ = sigma := by
        simp [p, zAt, v, pointOf, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [hsigmaEq]
  exact ⟨hsigma, hzero⟩

/-- Four checker equations have a root in every centered lambda slice. -/
theorem root_exists (conditions : Conditions b) (t : ℝ)
    (ht : (tInterval b).RealContains t) :
    ∃ z, InSymmetricBox (radiiReal b) z ∧ ∀ j, rootMap b t z j = 0 := by
  let zF : ℝ → Vec4 := fun xi => ![xi, etaRoot b t xi, 0, 0]
  have hzF_cont : Continuous zF := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun xi : ℝ => xi); fun_prop
    · exact etaRoot_continuous b t
    · change Continuous (fun _ : ℝ => (0 : ℝ)); fun_prop
    · change Continuous (fun _ : ℝ => (0 : ℝ)); fun_prop
  have hxiLow : -radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩
  have hxiHigh : radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) :=
    ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩
  have hetaLow := (etaRoot_spec conditions ht hxiLow).1
  have hetaHigh := (etaRoot_spec conditions ht hxiHigh).1
  have hzFLow : InSymmetricBox (radiiReal b) (zF (-radiiReal b 0)) :=
    vector_mem_box hxiLow hetaLow (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hzFHigh : InSymmetricBox (radiiReal b) (zF (radiiReal b 0)) :=
    vector_mem_box hxiHigh hetaHigh (zero_mem_coordinate 2) (zero_mem_coordinate 3)
  have hloF : rootMap b t (zF (-radiiReal b 0)) 0 ≤ 0 :=
    (conditions.lowFaces t _ ht hzFLow 0 (by simp [zF])).le
  have hhiF : 0 ≤ rootMap b t (zF (radiiReal b 0)) 0 :=
    (conditions.highFaces t _ ht hzFHigh 0 (by simp [zF])).le
  have hroot_continuous : Continuous (rootMap b t) := rootMap_continuous b t
  have hcontF : Continuous (fun xi => rootMap b t (zF xi) 0) :=
    (continuous_apply (0 : Fin 4)).comp (hroot_continuous.comp hzF_cont)
  rcases oppositeFace_zero (neg_le_self (radiiReal_pos 0).le)
      hcontF.continuousOn hloF hhiF with ⟨xi, hxi, hF⟩
  let eta := etaRoot b t xi
  have hetaSpec := etaRoot_spec conditions ht hxi
  have heta : eta ∈ Icc (-radiiReal b 1) (radiiReal b 1) := hetaSpec.1
  have hC4 : C4 b (pointOf t ![xi, eta, 0, 0]) = 0 := by
    simpa [eta] using hetaSpec.2
  let zE : ℝ → Vec4 := fun rho => ![xi, eta, rho, sigmaRoot b t rho]
  have hzE_cont : Continuous zE := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun _ : ℝ => xi); fun_prop
    · change Continuous (fun _ : ℝ => eta); fun_prop
    · change Continuous (fun rho : ℝ => rho); fun_prop
    · exact sigmaRoot_continuous b t
  have hrhoLow : -radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩
  have hrhoHigh : radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) :=
    ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩
  have hsigmaLow := (sigmaRoot_spec conditions ht hrhoLow).1
  have hsigmaHigh := (sigmaRoot_spec conditions ht hrhoHigh).1
  have hzELow : InSymmetricBox (radiiReal b) (zE (-radiiReal b 2)) :=
    vector_mem_box hxi heta hrhoLow hsigmaLow
  have hzEHigh : InSymmetricBox (radiiReal b) (zE (radiiReal b 2)) :=
    vector_mem_box hxi heta hrhoHigh hsigmaHigh
  have hloE : rootMap b t (zE (-radiiReal b 2)) 2 ≤ 0 :=
    (conditions.lowFaces t _ ht hzELow 2 (by simp [zE, Matrix.cons_val_two])).le
  have hhiE : 0 ≤ rootMap b t (zE (radiiReal b 2)) 2 :=
    (conditions.highFaces t _ ht hzEHigh 2 (by simp [zE, Matrix.cons_val_two])).le
  have hcontE : Continuous (fun rho => rootMap b t (zE rho) 2) :=
    (continuous_apply (2 : Fin 4)).comp (hroot_continuous.comp hzE_cont)
  rcases oppositeFace_zero (neg_le_self (radiiReal_pos 2).le)
      hcontE.continuousOn hloE hhiE with ⟨rho, hrho, hE⟩
  let sigma := sigmaRoot b t rho
  have hsigmaSpec := sigmaRoot_spec conditions ht hrho
  have hsigma : sigma ∈ Icc (-radiiReal b 3) (radiiReal b 3) := hsigmaSpec.1
  have hC3 : C3 b (pointOf t ![0, 0, rho, sigma]) = 0 := by
    simpa [sigma] using hsigmaSpec.2
  let z : Vec4 := ![xi, eta, rho, sigma]
  refine ⟨z, vector_mem_box hxi heta hrho hsigma, ?_⟩
  intro j
  fin_cases j
  · simpa [zF, z, eta, rootMap, Model.F, B4, D4, x, y, lam, pointOf] using hF
  · simpa [z, rootMap, C4, x, y, lam, pointOf] using hC4
  · simpa [zE, z, sigma, rootMap, Matrix.cons_val_two] using hE
  · simpa [z, rootMap, C3, w, v, lam, pointOf, Matrix.cons_val_three] using hC3

/-- Root and curvature-projection facts assembled solely from checked numerical
semantics.  This remains below the candidate layer. -/
structure RootProjection (b : Brick) (t : ℝ) (z : Vec4) : Prop where
  mem_box : InSymmetricBox (radiiReal b) z
  equations : ∀ j, rootMap b t z j = 0
  branches :
    let p := pointOf t z
    0 < x b p ∧ x b p < π / 4 ∧
    0 < y b p ∧ y b p < π / 4 ∧
    0 < w b p ∧ w b p < π / 4 ∧
    0 < v b p ∧ v b p < π / 4
  K3_neg : K3 b (pointOf t z) < 0
  G_neg : G b (pointOf t z) < 0
  typeThreeHeight_regular :
    (1 + cos (w b (pointOf t z))) / 2 ∈ Ioo (0 : ℝ) 1
  typeFourHeight_regular : cos (x b (pointOf t z)) ∈ Ioo (0 : ℝ) 1

/-- Generic root/projection assembly for a checked middle-face brick. -/
theorem rootProjection (conditions : Conditions b) (t : ℝ)
    (ht : (tInterval b).RealContains t) : ∃ z, RootProjection b t z := by
  rcases conditions.root_exists t ht with ⟨z, hz, hroot⟩
  have hb := conditions.branches t z ht hz
  have hK3 := conditions.K3_neg t z ht hz
  have hG := conditions.G_neg t z ht hz
  rcases hb with ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  have hxpi : x b (pointOf t z) < π := hxq.trans (by linarith [Real.pi_pos])
  have hwpi : w b (pointOf t z) < π := hwq.trans (by linarith [Real.pi_pos])
  have hxcosPos : 0 < cos (x b (pointOf t z)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hxq.trans (by linarith [Real.pi_pos])⟩
  have hwcosPos : 0 < cos (w b (pointOf t z)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
      hwq.trans (by linarith [Real.pi_pos])⟩
  have hxcosLt : cos (x b (pointOf t z)) < 1 := by
    simpa using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, Real.pi_pos.le⟩)
      ⟨hx0.le, hxpi.le⟩ hx0
  have hwcosLt : cos (w b (pointOf t z)) < 1 := by
    simpa using Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, Real.pi_pos.le⟩)
      ⟨hw0.le, hwpi.le⟩ hw0
  refine ⟨z, hz, hroot, ?_, hK3, hG, ?_, ⟨hxcosPos, hxcosLt⟩⟩
  · exact ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  · constructor <;> linarith

private theorem typeThreeCellAngle_mem_Icc_zero_pi
    (conditions : Conditions b) {t rho : ℝ}
    (ht : (tInterval b).RealContains t)
    (hrho : rho ∈ Icc (-radiiReal b 2) (radiiReal b 2)) :
    (b.centers 2 : ℝ) + b.slopes 2 * t + rho ∈ Icc (0 : ℝ) π := by
  rcases sigmaRoot_spec conditions ht hrho with ⟨hsigma, _⟩
  have hz := vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1)
    hrho hsigma
  rcases conditions.branches t ![0, 0, rho, sigmaRoot b t rho] ht hz with
    ⟨_, _, _, _, hw0, hwq, _, _⟩
  have hwpi : w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]) < π :=
    hwq.trans (by linarith [Real.pi_pos])
  simpa [w, pointOf, Matrix.cons_val_two, Matrix.cons_val_three] using
    And.intro hw0.le hwpi.le

/-- Every `rho` coordinate projects into the type-(iii) cell interval. -/
theorem typeThreeCellHeight_mem_interval
    (conditions : Conditions b) {t rho : ℝ}
    (ht : (tInterval b).RealContains t)
    (hrho : rho ∈ Icc (-radiiReal b 2) (radiiReal b 2)) :
    typeThreeCellHeight b t rho ∈ typeThreeCellInterval b t := by
  have hcur := typeThreeCellAngle_mem_Icc_zero_pi conditions ht hrho
  have hright := typeThreeCellAngle_mem_Icc_zero_pi conditions ht
    (show radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) from
      ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)
  have hleft := typeThreeCellAngle_mem_Icc_zero_pi conditions ht
    (show -radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)
  constructor
  · have hangle :
        (b.centers 2 : ℝ) + b.slopes 2 * t + rho ≤
          (b.centers 2 : ℝ) + b.slopes 2 * t + radiiReal b 2 := by
      linarith [hrho.2]
    have hcos := Real.strictAntiOn_cos.antitoneOn hcur hright hangle
    unfold typeThreeCellHeight
    linarith
  · have hangle :
        (b.centers 2 : ℝ) + b.slopes 2 * t - radiiReal b 2 ≤
          (b.centers 2 : ℝ) + b.slopes 2 * t + rho := by
      linarith [hrho.1]
    have hcos := Real.strictAntiOn_cos.antitoneOn hleft hcur hangle
    unfold typeThreeCellHeight
    linarith

private theorem typeThreeCellHeight_mem_Ioo
    (conditions : Conditions b) {t rho : ℝ}
    (ht : (tInterval b).RealContains t)
    (hrho : rho ∈ Icc (-radiiReal b 2) (radiiReal b 2)) :
    typeThreeCellHeight b t rho ∈ Ioo (0 : ℝ) 1 := by
  rcases sigmaRoot_spec conditions ht hrho with ⟨hsigma, _⟩
  have hz := vector_mem_box (zero_mem_coordinate 0) (zero_mem_coordinate 1)
    hrho hsigma
  rcases conditions.branches t ![0, 0, rho, sigmaRoot b t rho] ht hz with
    ⟨_, _, _, _, hw0, hwq, _, _⟩
  have hwpi : w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]) < π :=
    hwq.trans (by linarith [Real.pi_pos])
  have hwpi2 : w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]) < π / 2 := by
    linarith [Real.pi_pos]
  have hcos_pos :
      0 < cos (w b (pointOf t ![0, 0, rho, sigmaRoot b t rho])) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hwpi2⟩
  have hcos_lt_one :
      cos (w b (pointOf t ![0, 0, rho, sigmaRoot b t rho])) < 1 := by
    have hzero : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
    have hwmem :
        w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]) ∈ Icc 0 π :=
      ⟨hw0.le, hwpi.le⟩
    simpa using Real.strictAntiOn_cos hzero hwmem hw0
  simpa [typeThreeCellHeight, w, pointOf, Matrix.cons_val_two,
    Matrix.cons_val_three] using
    (show 0 < (1 + cos
        (w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]))) / 2 ∧
      (1 + cos
        (w b (pointOf t ![0, 0, rho, sigmaRoot b t rho]))) / 2 < 1 by
      constructor <;> linarith)

/-- The full projected type-(iii) interval consists of regular heights. -/
theorem typeThreeCellInterval_subset_regular
    (conditions : Conditions b) {t : ℝ}
    (ht : (tInterval b).RealContains t) :
    typeThreeCellInterval b t ⊆ Ioo (0 : ℝ) 1 := by
  intro h hh
  have hlo := typeThreeCellHeight_mem_Ioo conditions ht
    (show radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) from
      ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩)
  have hhi := typeThreeCellHeight_mem_Ioo conditions ht
    (show -radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩)
  exact ⟨hlo.1.trans_le hh.1, hh.2.trans_lt hhi.2⟩

/-- The primitive `K3 < 0` condition controls the actual analytic area
derivative throughout the type-(iii) projection. -/
theorem typeThreeArea_deriv_neg_on_cellInterval
    (conditions : Conditions b) {t h₃ : ℝ}
    (ht : (tInterval b).RealContains t)
    (hh₃ : h₃ ∈ typeThreeCellInterval b t) :
    deriv (LeanSuffixAnalytic.typeThreeArea ((lamMid b : ℝ) + t)) h₃ < 0 := by
  have hrad : -radiiReal b 2 ≤ radiiReal b 2 :=
    neg_le_self (radiiReal_pos 2).le
  have hcont : ContinuousOn (typeThreeCellHeight b t)
      (Icc (-radiiReal b 2) (radiiReal b 2)) := by
    apply Continuous.continuousOn
    unfold typeThreeCellHeight
    fun_prop
  have hh₃' : h₃ ∈ Icc
      (typeThreeCellHeight b t (radiiReal b 2))
      (typeThreeCellHeight b t (-radiiReal b 2)) := by
    simpa [typeThreeCellInterval] using hh₃
  rcases intermediate_value_Icc' hrad hcont hh₃' with
    ⟨rho, hrho, hrfl⟩
  let z : Vec4 := ![0, 0, rho, sigmaRoot b t rho]
  let p : Point := pointOf t z
  rcases sigmaRoot_spec conditions ht hrho with ⟨hsigma, hC3'⟩
  have hz : InSymmetricBox (radiiReal b) z := by
    simpa [z] using vector_mem_box (zero_mem_coordinate 0)
      (zero_mem_coordinate 1) hrho hsigma
  rcases conditions.branches t z ht hz with
    ⟨_, _, _, _, hw0, hwq, hv0, hvq⟩
  have hC3 : C3 b p = 0 := by
    simpa [p, z] using hC3'
  have hlamPoint : 1 < lam b p := by
    simpa [p, z, lam, pointOf] using conditions.lambda_one_lt t ht
  have hlamEq : lam b p = (lamMid b : ℝ) + t := by
    simp [p, z, lam, pointOf]
  have hhEq :
      (1 + cos (w b p)) / 2 = typeThreeCellHeight b t rho := by
    simp [p, z, w, pointOf, typeThreeCellHeight, Matrix.cons_val_two,
      Matrix.cons_val_three]
  rw [← hrfl, ← hlamEq, ← hhEq]
  rw [MiddleFaceAssembly.typeThreeArea_deriv_eq_K3 b p hlamPoint
    ⟨hw0, hwq, hv0, hvq⟩ hC3]
  exact div_neg_of_neg_of_pos
    (conditions.K3_neg t z ht hz)
    (pow_pos (by
      rw [hhEq]
      exact (typeThreeCellHeight_mem_Ioo conditions ht hrho).1) 3)

private theorem typeFourCellAngle_mem_Icc_zero_pi
    (conditions : Conditions b) {t xi : ℝ}
    (ht : (tInterval b).RealContains t)
    (hxi : xi ∈ Icc (-radiiReal b 0) (radiiReal b 0)) :
    (b.centers 0 : ℝ) + b.slopes 0 * t + xi ∈ Icc (0 : ℝ) π := by
  rcases etaRoot_spec conditions ht hxi with ⟨heta, _⟩
  have hz := vector_mem_box hxi heta (zero_mem_coordinate 2)
    (zero_mem_coordinate 3)
  rcases conditions.branches t ![xi, etaRoot b t xi, 0, 0] ht hz with
    ⟨hx0, hxq, _, _, _, _, _, _⟩
  have hxpi : x b (pointOf t ![xi, etaRoot b t xi, 0, 0]) < π :=
    hxq.trans (by linarith [Real.pi_pos])
  simpa [x, pointOf] using And.intro hx0.le hxpi.le

/-- Every `xi` coordinate projects into the type-(iv) cell interval. -/
theorem typeFourCellHeight_mem_interval
    (conditions : Conditions b) {t xi : ℝ}
    (ht : (tInterval b).RealContains t)
    (hxi : xi ∈ Icc (-radiiReal b 0) (radiiReal b 0)) :
    typeFourCellHeight b t xi ∈ typeFourCellInterval b t := by
  have hcur := typeFourCellAngle_mem_Icc_zero_pi conditions ht hxi
  have hright := typeFourCellAngle_mem_Icc_zero_pi conditions ht
    (show radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) from
      ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩)
  have hleft := typeFourCellAngle_mem_Icc_zero_pi conditions ht
    (show -radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩)
  constructor
  · have hangle :
        (b.centers 0 : ℝ) + b.slopes 0 * t + xi ≤
          (b.centers 0 : ℝ) + b.slopes 0 * t + radiiReal b 0 := by
      linarith [hxi.2]
    exact Real.strictAntiOn_cos.antitoneOn hcur hright hangle
  · have hangle :
        (b.centers 0 : ℝ) + b.slopes 0 * t - radiiReal b 0 ≤
          (b.centers 0 : ℝ) + b.slopes 0 * t + xi := by
      linarith [hxi.1]
    exact Real.strictAntiOn_cos.antitoneOn hleft hcur hangle

private theorem typeFourCellHeight_mem_Ioo
    (conditions : Conditions b) {t xi : ℝ}
    (ht : (tInterval b).RealContains t)
    (hxi : xi ∈ Icc (-radiiReal b 0) (radiiReal b 0)) :
    typeFourCellHeight b t xi ∈ Ioo (0 : ℝ) 1 := by
  rcases etaRoot_spec conditions ht hxi with ⟨heta, _⟩
  have hz := vector_mem_box hxi heta (zero_mem_coordinate 2)
    (zero_mem_coordinate 3)
  rcases conditions.branches t ![xi, etaRoot b t xi, 0, 0] ht hz with
    ⟨hx0, hxq, _, _, _, _, _, _⟩
  have hxpi : x b (pointOf t ![xi, etaRoot b t xi, 0, 0]) < π :=
    hxq.trans (by linarith [Real.pi_pos])
  have hxpi2 : x b (pointOf t ![xi, etaRoot b t xi, 0, 0]) < π / 2 := by
    linarith [Real.pi_pos]
  have hcos_pos :
      0 < cos (x b (pointOf t ![xi, etaRoot b t xi, 0, 0])) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxpi2⟩
  have hcos_lt_one :
      cos (x b (pointOf t ![xi, etaRoot b t xi, 0, 0])) < 1 := by
    have hzero : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
    have hxmem : x b (pointOf t ![xi, etaRoot b t xi, 0, 0]) ∈ Icc 0 π :=
      ⟨hx0.le, hxpi.le⟩
    simpa using Real.strictAntiOn_cos hzero hxmem hx0
  simpa [typeFourCellHeight, x, pointOf] using
    And.intro hcos_pos hcos_lt_one

/-- The full projected type-(iv) interval consists of regular heights. -/
theorem typeFourCellInterval_subset_regular
    (conditions : Conditions b) {t : ℝ}
    (ht : (tInterval b).RealContains t) :
    typeFourCellInterval b t ⊆ Ioo (0 : ℝ) 1 := by
  intro h hh
  have hlo := typeFourCellHeight_mem_Ioo conditions ht
    (show radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) from
      ⟨neg_le_self (radiiReal_pos 0).le, le_rfl⟩)
  have hhi := typeFourCellHeight_mem_Ioo conditions ht
    (show -radiiReal b 0 ∈ Icc (-radiiReal b 0) (radiiReal b 0) from
      ⟨le_rfl, neg_le_self (radiiReal_pos 0).le⟩)
  exact ⟨hlo.1.trans_le hh.1, hh.2.trans_lt hhi.2⟩

/-- Every projected type-(iv) height has an equal-actual-area regular
type-(iii) height in the same slice with strictly smaller actual perimeter. -/
theorem projected_typeFour_scalarImprovement_exists
    (conditions : Conditions b) {t h₄ : ℝ}
    (ht : (tInterval b).RealContains t)
    (hh₄ : h₄ ∈ typeFourCellInterval b t) :
    ∃ h₃, h₃ ∈ typeThreeCellInterval b t ∧ h₃ ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea ((lamMid b : ℝ) + t) h₃ =
        LeanSuffixAnalytic.typeFourArea ((lamMid b : ℝ) + t) h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter ((lamMid b : ℝ) + t) h₃ <
        LeanSuffixAnalytic.typeFourPerimeter ((lamMid b : ℝ) + t) h₄ := by
  have hrad : -radiiReal b 0 ≤ radiiReal b 0 :=
    neg_le_self (radiiReal_pos 0).le
  have hcont : ContinuousOn (typeFourCellHeight b t)
      (Icc (-radiiReal b 0) (radiiReal b 0)) := by
    apply Continuous.continuousOn
    unfold typeFourCellHeight
    fun_prop
  have hh₄' : h₄ ∈ Icc
      (typeFourCellHeight b t (radiiReal b 0))
      (typeFourCellHeight b t (-radiiReal b 0)) := by
    simpa [typeFourCellInterval] using hh₄
  rcases intermediate_value_Icc' hrad hcont hh₄' with
    ⟨xi, hxi, hheight⟩
  let eta := etaRoot b t xi
  have hetaSpec := etaRoot_spec conditions ht hxi
  have heta : eta ∈ Icc (-radiiReal b 1) (radiiReal b 1) := hetaSpec.1
  have hC4' : C4 b (pointOf t ![xi, eta, 0, 0]) = 0 := by
    simpa [eta] using hetaSpec.2
  let zE : ℝ → Vec4 := fun rho => ![xi, eta, rho, sigmaRoot b t rho]
  have hzE_cont : Continuous zE := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun _ : ℝ => xi); fun_prop
    · change Continuous (fun _ : ℝ => eta); fun_prop
    · change Continuous (fun rho : ℝ => rho); fun_prop
    · exact sigmaRoot_continuous b t
  have hrhoLow : -radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) :=
    ⟨le_rfl, neg_le_self (radiiReal_pos 2).le⟩
  have hrhoHigh : radiiReal b 2 ∈ Icc (-radiiReal b 2) (radiiReal b 2) :=
    ⟨neg_le_self (radiiReal_pos 2).le, le_rfl⟩
  have hsigmaLow := (sigmaRoot_spec conditions ht hrhoLow).1
  have hsigmaHigh := (sigmaRoot_spec conditions ht hrhoHigh).1
  have hzELow : InSymmetricBox (radiiReal b) (zE (-radiiReal b 2)) :=
    vector_mem_box hxi heta hrhoLow hsigmaLow
  have hzEHigh : InSymmetricBox (radiiReal b) (zE (radiiReal b 2)) :=
    vector_mem_box hxi heta hrhoHigh hsigmaHigh
  have hloE : rootMap b t (zE (-radiiReal b 2)) 2 ≤ 0 :=
    (conditions.lowFaces t _ ht hzELow 2
      (by simp [zE, Matrix.cons_val_two])).le
  have hhiE : 0 ≤ rootMap b t (zE (radiiReal b 2)) 2 :=
    (conditions.highFaces t _ ht hzEHigh 2
      (by simp [zE, Matrix.cons_val_two])).le
  have hcontE : Continuous (fun rho => rootMap b t (zE rho) 2) :=
    (continuous_apply (2 : Fin 4)).comp ((rootMap_continuous b t).comp hzE_cont)
  rcases oppositeFace_zero (neg_le_self (radiiReal_pos 2).le)
      hcontE.continuousOn hloE hhiE with ⟨rho, hrho, hE⟩
  let sigma := sigmaRoot b t rho
  have hsigmaSpec := sigmaRoot_spec conditions ht hrho
  have hsigma : sigma ∈ Icc (-radiiReal b 3) (radiiReal b 3) := hsigmaSpec.1
  have hC3' : C3 b (pointOf t ![0, 0, rho, sigma]) = 0 := by
    simpa [sigma] using hsigmaSpec.2
  let z : Vec4 := ![xi, eta, rho, sigma]
  let p : Point := pointOf t z
  have hz : InSymmetricBox (radiiReal b) z :=
    vector_mem_box hxi heta hrho hsigma
  have hbranches := conditions.branches t z ht hz
  have hC4 : C4 b p = 0 := by
    simpa [p, z, C4, x, y, lam, pointOf] using hC4'
  have hC3 : C3 b p = 0 := by
    simpa [p, z, C3, w, v, lam, pointOf, Matrix.cons_val_three] using hC3'
  have hEPoint : E b p = 0 := by
    simpa [p, z, zE, sigma, rootMap, Matrix.cons_val_two] using hE
  have hlamPoint : 1 < lam b p := by
    simpa [p, z, lam, pointOf] using conditions.lambda_one_lt t ht
  have hsem := pointEquationSemantics b p hlamPoint hbranches hC4 hC3
  have harea := hsem.equalArea_of_E_zero hEPoint
  have hperimeter := hsem.perimeter_lt_of_G_neg (conditions.G_neg t z ht hz)
  have hlamEq : lam b p = (lamMid b : ℝ) + t := by
    simp [p, z, lam, pointOf]
  have hh₃Eq :
      (1 + cos (w b p)) / 2 = typeThreeCellHeight b t rho := by
    simp [p, z, w, pointOf, typeThreeCellHeight, Matrix.cons_val_two,
      Matrix.cons_val_three]
  have hh₄Eq : cos (x b p) = typeFourCellHeight b t xi := by
    simp [p, z, x, pointOf, typeFourCellHeight]
  refine ⟨typeThreeCellHeight b t rho,
    typeThreeCellHeight_mem_interval conditions ht hrho,
    typeThreeCellHeight_mem_Ioo conditions ht hrho, ?_, ?_⟩
  · simpa [hlamEq, hh₃Eq, hh₄Eq, hheight] using harea
  · simpa [hlamEq, hh₃Eq, hh₄Eq, hheight] using hperimeter

/-- Every checked middle-face brick supplies one stationary equal-area pair
whose type-(iii) member lies on the descending branch and has strictly smaller
perimeter.  This is the reusable scalar input for the global equal-area
envelope; it does not restrict the eventual candidate to the brick projection. -/
theorem stationaryEqualAreaPair_exists
    (conditions : Conditions b) {t : ℝ}
    (ht : (tInterval b).RealContains t) :
    ∃ pair :
        LeanSuffixAnalytic.StationaryEqualAreaPair ((lamMid b : ℝ) + t),
      LeanSuffixAnalytic.typeThreeFold ((lamMid b : ℝ) + t) pair.h₃ < 0 ∧
        LeanSuffixAnalytic.typeThreePerimeter
            ((lamMid b : ℝ) + t) pair.h₃ <
          LeanSuffixAnalytic.typeFourPerimeter
            ((lamMid b : ℝ) + t) pair.h₄ := by
  rcases conditions.rootProjection t ht with ⟨z, projection⟩
  let p : Point := pointOf t z
  have hbranches :
      0 < x b p ∧ x b p < π / 4 ∧
      0 < y b p ∧ y b p < π / 4 ∧
      0 < w b p ∧ w b p < π / 4 ∧
      0 < v b p ∧ v b p < π / 4 := by
    simpa [p] using projection.branches
  rcases hbranches with
    ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩
  have hFNeg : -F b p = 0 := by
    simpa [rootMap, p] using projection.equations 0
  have hF : F b p = 0 := neg_eq_zero.mp hFNeg
  have hC4 : C4 b p = 0 := by
    simpa [rootMap, p] using projection.equations 1
  have hE : E b p = 0 := by
    simpa [rootMap, p] using projection.equations 2
  have hC3 : C3 b p = 0 := by
    simpa [rootMap, p] using projection.equations 3
  have hlam : 1 < lam b p := by
    simpa [p, lam, pointOf] using conditions.lambda_one_lt t ht
  have hsem := pointEquationSemantics b p hlam
    ⟨hx0, hxq, hy0, hyq, hw0, hwq, hv0, hvq⟩ hC4 hC3
  have harea := hsem.equalArea_of_E_zero hE
  have hstationary := hsem.stationary_of_F_zero hF
  have hperimeter :=
    hsem.perimeter_lt_of_G_neg (by simpa [p] using projection.G_neg)
  have hh₃Pos : 0 < (1 + cos (w b p)) / 2 :=
    lt_trans (by norm_num) hsem.typeThreeHeight_gt_half
  have hderiv :
      deriv (LeanSuffixAnalytic.typeThreeArea (lam b p))
          ((1 + cos (w b p)) / 2) < 0 := by
    rw [MiddleFaceAssembly.typeThreeArea_deriv_eq_K3 b p hlam
      ⟨hw0, hwq, hv0, hvq⟩ hC3]
    exact div_neg_of_neg_of_pos
      (by simpa [p] using projection.K3_neg)
      (pow_pos hh₃Pos 3)
  have hfoldThree :
      LeanSuffixAnalytic.typeThreeFold (lam b p)
          ((1 + cos (w b p)) / 2) < 0 := by
    rw [(LeanSuffixAnalytic.hasDerivAt_typeThreeArea hlam hh₃Pos
      hsem.typeThreeHeight_lt_one).deriv] at hderiv
    rcases div_neg_iff.mp hderiv with hbad | hgood
    · linarith [pow_pos hh₃Pos 3]
    · exact hgood.1
  have hlamEq : lam b p = (lamMid b : ℝ) + t := by
    simp [p, lam, pointOf]
  rw [hlamEq] at harea hstationary hperimeter hfoldThree
  let pair :
      LeanSuffixAnalytic.StationaryEqualAreaPair ((lamMid b : ℝ) + t) :=
    { h₃ := (1 + cos (w b p)) / 2
      h₄ := cos (x b p)
      h₃_gt_half := hsem.typeThreeHeight_gt_half
      h₃_lt_one := hsem.typeThreeHeight_lt_one
      h₄_pos := hsem.typeFourHeight_pos
      h₄_lt_one := hsem.typeFourHeight_lt_one
      equalArea := harea
      stationary := hstationary }
  refine ⟨pair, ?_, ?_⟩
  · simpa [pair] using hfoldThree
  · simpa [pair] using hperimeter

/-- A single stationary pair from a checked brick promotes through the global
descending equal-area envelope and excludes every modeled type-(iv) candidate
at that density, including the `h₄ = 1` endpoint. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    (conditions : Conditions b) {t lam0 : ℝ}
    (ht : (tInterval b).RealContains t)
    (hlam : (lamMid b : ℝ) + t = lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  subst lam0
  rcases stationaryEqualAreaPair_exists conditions ht with
    ⟨pair, hfoldThree, hperimeter⟩
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair
      candidate hcandidate pair hfoldThree hperimeter

/-- Generic candidate-facing conclusion for the complete projected slice. -/
theorem projectedCandidate_not_isWeightedPerimeterMinimizer
    (conditions : Conditions b) {t lam0 : ℝ}
    (ht : (tInterval b).RealContains t)
    (hlam : (lamMid b : ℝ) + t = lam0)
    (candidate : _root_.FourArcCandidate lam0)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hprojected : candidate.h ∈ typeFourCellInterval b t) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  subst lam0
  rcases projected_typeFour_scalarImprovement_exists conditions ht hprojected with
    ⟨h₃, _hh₃Cell, hh₃, harea, hperimeter⟩
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
      candidate hcandidate hh₃.1 hh₃.2 harea hperimeter

end Conditions
end MiddleFaceAssembly
