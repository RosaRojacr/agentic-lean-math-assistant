/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneScalarInterval
import SameCurvatureArea
import CMVSuffixModel

/-!
# Source-native moving scalar cells

Compositional interval certificates for the exact normalized `F`, `E`, and `J`
expressions, followed by the nested-IVT transport to the existing candidate
consumer.
-/

namespace NearOneScalarCell

open Real Set
open NearOneScalarNormalization
open NearOneScalarInterval

noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

namespace SourceJet

open NearOneScalarInterval.Jet3

variable {box : Box3}

/-- The normalized density parameter as an interval jet. -/
def lamJet (t : Jet3 box) : Jet3 box := (rational 1).add t.cube

/-- The source height coordinate. -/
def xJet (t c : Jet3 box) : Jet3 box :=
  (rational 1).sub (t.sq.mul c)

/-- First pole-free radicand. -/
def uInnerJet (t c : Jet3 box) : Jet3 box :=
  ((rational 2).mul c).sub (t.sq.mul c.sq)

/-- Second pole-free radicand. -/
def vInnerJet (t c : Jet3 box) : Jet3 box :=
  ((((rational 2).mul c).add ((rational 2).mul t)).sub
    (t.sq.mul c.sq)).add t.fourth

/-- Generated square-root leaves and their exact square witnesses. -/
structure RadicalData (t c : Jet3 box) where
  u : QInterval
  uPos : 0 < u.lo
  uLoSq : u.lo ^ 2 ≤ (uInnerJet t c).range.lo
  uHiSq : (uInnerJet t c).range.hi ≤ u.hi ^ 2
  v : QInterval
  vPos : 0 < v.lo
  vLoSq : v.lo ^ 2 ≤ (vInnerJet t c).range.lo
  vHiSq : (vInnerJet t c).range.hi ≤ v.hi ^ 2

/-- Checked radical jet. -/
def uJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  (uInnerJet t c).sqrt data.u data.uPos data.uLoSq data.uHiSq

/-- Checked second radical jet. -/
def vJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  (vInnerJet t c).sqrt data.v data.vPos data.vLoSq data.vHiSq

/-- Common positive radical sum. -/
def radicalSumJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  (vJet t c data).add ((lamJet t).mul (uJet t c data))

/-- Denominator of `K`. -/
def kDenJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  ((uJet t c data).mul (vJet t c data)).mul (radicalSumJet t c data)

/-- Denominator of `D`. -/
def dDenJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  (lamJet t).mul (radicalSumJet t c data)

/-- Denominator of `rho`. -/
def rhoDenJet (t c : Jet3 box) (data : RadicalData t c) : Jet3 box :=
  ((uJet t c data).add (vJet t c data)).mul
    ((xJet t c).sq.add (t.sq.mul ((uJet t c data).mul (vJet t c data))))

/-- Remaining positivity and arctangent-domain witnesses.  A common `1/4`
argument bound suffices for every retained stress sample. -/
structure AtomData (t c : Jet3 box) where
  radicals : RadicalData t c
  xPos : 0 < (xJet t c).range.lo
  kDenPos : 0 < (kDenJet t c radicals).range.lo
  dDenPos : 0 < (dDenJet t c radicals).range.lo
  rhoDenPos : 0 < (rhoDenJet t c radicals).range.lo
  linearLo : -(1 / 4 : ℚ) ≤
    (t.mul (vJet t c radicals) |>.mul ((xJet t c).invPos xPos)).range.lo
  linearHi :
    (t.mul (vJet t c radicals) |>.mul ((xJet t c).invPos xPos)).range.hi ≤
      (1 / 4 : ℚ)
  quadraticLo : -(1 / 4 : ℚ) ≤
    (t.sq.mul
      (((xJet t c).mul ((rational 2).add t.cube)).mul
        ((rhoDenJet t c radicals).invPos rhoDenPos))).range.lo
  quadraticHi :
    (t.sq.mul
      (((xJet t c).mul ((rational 2).add t.cube)).mul
        ((rhoDenJet t c radicals).invPos rhoDenPos))).range.hi ≤
      (1 / 4 : ℚ)

/-- All normalized source atoms for one curvature coefficient. -/
structure Atom (box : Box3) where
  x : Jet3 box
  u : Jet3 box
  v : Jet3 box
  k : Jet3 box
  d : Jet3 box
  rho : Jet3 box
  linearArgument : Jet3 box
  quadraticArgument : Jet3 box
  h : Jet3 box

/-- Exact source atom assembled from checked radicals, reciprocals, and the
analytic first arctangent remainder. -/
def atom (t c : Jet3 box) (data : AtomData t c) : Atom box :=
  let x := xJet t c
  let u := uJet t c data.radicals
  let v := vJet t c data.radicals
  let lam := lamJet t
  let commonNumerator := x.sq.mul ((rational 2).add t.cube)
  let k := commonNumerator.mul ((kDenJet t c data.radicals).invPos data.kDenPos)
  let d := commonNumerator.mul ((dDenJet t c data.radicals).invPos data.dDenPos)
  let rho := (x.mul ((rational 2).add t.cube)).mul
    ((rhoDenJet t c data.radicals).invPos data.rhoDenPos)
  let linearArgument := (t.mul v).mul (x.invPos data.xPos)
  let quadraticArgument := t.sq.mul rho
  let h := (((t.sq.mul v).mul (x.invPos data.xPos)).mul
      (linearArgument.atanQuotient (1 / 4) (by norm_num) (by norm_num)
        data.linearLo data.linearHi)).add
    (rho.mul (quadraticArgument.atanQuotient (1 / 4) (by norm_num) (by norm_num)
      data.quadraticLo data.quadraticHi))
  { x := x, u := u, v := v, k := k, d := d, rho := rho,
    linearArgument := linearArgument, quadraticArgument := quadraticArgument,
    h := h }

/-- Moving affine-plus-quadratic bracket coordinate. -/
def predictorJet (t epsilon : Jet3 box) (p0 p1 : ℚ) : Jet3 box :=
  (rational p0).add ((rational p1).mul t) |>.add (t.sq.mul epsilon)

/-- Four radical packages for one complete source evaluation. -/
structure Data (t a b : Jet3 box) where
  four : AtomData t a
  three : AtomData t ((rational 2).mul b)

/-- Exact `F`, `E`, `J`, and the small set of guards needed by the scalar
consumer. -/
structure Model (box : Box3) where
  a : Jet3 box
  b : Jet3 box
  hFour : Jet3 box
  hThree : Jet3 box
  shapeThree : Jet3 box
  bSubA : Jet3 box
  fold : Jet3 box
  area : Jet3 box
  gap : Jet3 box

/-- Build the normalized source model once; every field retains its actual
partial derivatives. -/
def model (t a b : Jet3 box) (data : Data t a b) : Model box :=
  let four := atom t a data.four
  let three := atom t ((rational 2).mul b) data.three
  let hFour := four.x
  let hThree := (rational 1).sub (t.sq.mul b)
  let fold := (hFour.mul four.k).sub ((pi.mul (rational (1 / 2))).add
    (t.sq.mul four.h))
  let area :=
    (((pi.mul (b.sub a)).mul (hFour.add hThree)).add
      (hFour.sq.mul (three.h.add
        (((rational 2).mul hThree |>.add (rational 1)).mul three.d)))).sub
      (((rational 2).mul hThree.sq).mul
        (four.h.add (hFour.mul four.d)))
  let gap := ((a.sub b).mul four.k).add (hThree.mul four.d) |>.sub
    (hFour.mul three.d)
  { a := a, b := b, hFour := hFour, hThree := hThree,
    shapeThree := three.x, bSubA := b.sub a,
    fold := fold, area := area, gap := gap }

@[simp] theorem value_tVar (box : Box3) (t e4 e3 : ℝ) :
    (Jet3.tVar box).value t e4 e3 = t := rfl
@[simp] theorem value_e4Var (box : Box3) (t e4 e3 : ℝ) :
    (Jet3.e4Var box).value t e4 e3 = e4 := rfl
@[simp] theorem value_e3Var (box : Box3) (t e4 e3 : ℝ) :
    (Jet3.e3Var box).value t e4 e3 = e3 := rfl

@[simp] theorem value_predictorJet (t epsilon : Jet3 box) (p0 p1 : ℚ)
    (s e4 e3 : ℝ) :
    (predictorJet t epsilon p0 p1).value s e4 e3 =
      (p0 : ℝ) + (p1 : ℝ) * t.value s e4 e3 +
        (t.value s e4 e3) ^ 2 * epsilon.value s e4 e3 := by
  simp [predictorJet]

@[simp] theorem value_lamJet (t : Jet3 box) (s e4 e3 : ℝ) :
    (lamJet t).value s e4 e3 = lam (t.value s e4 e3) := by
  simp [lamJet, lam]

@[simp] theorem value_xJet (t c : Jet3 box) (s e4 e3 : ℝ) :
    (xJet t c).value s e4 e3 =
      xCoord (t.value s e4 e3) (c.value s e4 e3) := by
  simp [xJet, xCoord]

@[simp] theorem value_uInnerJet (t c : Jet3 box) (s e4 e3 : ℝ) :
    (uInnerJet t c).value s e4 e3 =
      uInner (t.value s e4 e3) (c.value s e4 e3) := by
  simp [uInnerJet, uInner]

@[simp] theorem value_vInnerJet (t c : Jet3 box) (s e4 e3 : ℝ) :
    (vInnerJet t c).value s e4 e3 =
      vInner (t.value s e4 e3) (c.value s e4 e3) := by
  simp [vInnerJet, vInner]

@[simp] theorem value_uJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (uJet t c data).value s e4 e3 =
      U (t.value s e4 e3) (c.value s e4 e3) := by
  simp [uJet, U]

@[simp] theorem value_vJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (vJet t c data).value s e4 e3 =
      V (t.value s e4 e3) (c.value s e4 e3) := by
  simp [vJet, V]

@[simp] theorem value_radicalSumJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (radicalSumJet t c data).value s e4 e3 =
      V (t.value s e4 e3) (c.value s e4 e3) +
        lam (t.value s e4 e3) * U (t.value s e4 e3) (c.value s e4 e3) := by
  simp [radicalSumJet]

@[simp] theorem value_kDenJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (kDenJet t c data).value s e4 e3 =
      U (t.value s e4 e3) (c.value s e4 e3) *
        V (t.value s e4 e3) (c.value s e4 e3) *
        (V (t.value s e4 e3) (c.value s e4 e3) +
          lam (t.value s e4 e3) * U (t.value s e4 e3) (c.value s e4 e3)) := by
  simp [kDenJet]

@[simp] theorem value_dDenJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (dDenJet t c data).value s e4 e3 =
      lam (t.value s e4 e3) *
        (V (t.value s e4 e3) (c.value s e4 e3) +
          lam (t.value s e4 e3) * U (t.value s e4 e3) (c.value s e4 e3)) := by
  simp [dDenJet]

@[simp] theorem value_rhoDenJet (t c : Jet3 box) (data : RadicalData t c)
    (s e4 e3 : ℝ) :
    (rhoDenJet t c data).value s e4 e3 =
      (U (t.value s e4 e3) (c.value s e4 e3) +
        V (t.value s e4 e3) (c.value s e4 e3)) *
      (xCoord (t.value s e4 e3) (c.value s e4 e3) ^ 2 +
        t.value s e4 e3 ^ 2 *
          U (t.value s e4 e3) (c.value s e4 e3) *
          V (t.value s e4 e3) (c.value s e4 e3)) := by
  simp [rhoDenJet]
  left
  ring

@[simp] theorem value_atom_x (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).x.value s e4 e3 =
      xCoord (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, xJet, xCoord]

@[simp] theorem value_atom_k (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).k.value s e4 e3 =
      K (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, K, div_eq_mul_inv, mul_inv_rev]

@[simp] theorem value_atom_d (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).d.value s e4 e3 =
      D (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, D, div_eq_mul_inv, mul_inv_rev]

@[simp] theorem value_atom_rho (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).rho.value s e4 e3 =
      rho (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, rho, div_eq_mul_inv, mul_inv_rev]

@[simp] theorem value_atom_linearArgument (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).linearArgument.value s e4 e3 =
      t.value s e4 e3 * V (t.value s e4 e3) (c.value s e4 e3) /
        xCoord (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, div_eq_mul_inv]

@[simp] theorem value_atom_quadraticArgument (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).quadraticArgument.value s e4 e3 =
      t.value s e4 e3 ^ 2 * rho (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, rho, div_eq_mul_inv, mul_inv_rev]

@[simp] theorem value_atom_h (t c : Jet3 box) (data : AtomData t c)
    (s e4 e3 : ℝ) :
    (atom t c data).h.value s e4 e3 =
      H (t.value s e4 e3) (c.value s e4 e3) := by
  simp [atom, H, rho, div_eq_mul_inv, mul_inv_rev]
  left
  ring

@[simp] theorem value_model_a (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) : (model t a b data).a.value s e4 e3 = a.value s e4 e3 := rfl
@[simp] theorem value_model_b (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) : (model t a b data).b.value s e4 e3 = b.value s e4 e3 := rfl

@[simp] theorem value_model_fold (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).fold.value s e4 e3 =
      NearOneScalarNormalization.F (t.value s e4 e3)
        (a.value s e4 e3) := by
  simp [model, NearOneScalarNormalization.F, hFour]
  ring

@[simp] theorem value_model_area (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).area.value s e4 e3 =
      E (t.value s e4 e3) (a.value s e4 e3) (b.value s e4 e3) := by
  simp [model, E, hFour, hThree, xCoord]

@[simp] theorem value_model_gap (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).gap.value s e4 e3 =
      J (t.value s e4 e3) (a.value s e4 e3) (b.value s e4 e3) := by
  simp [model, J, hFour, hThree, xCoord]

@[simp] theorem value_model_hFour (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).hFour.value s e4 e3 =
      hFour (t.value s e4 e3) (a.value s e4 e3) := by
  simp [model, hFour]

@[simp] theorem value_model_hThree (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).hThree.value s e4 e3 =
      hThree (t.value s e4 e3) (b.value s e4 e3) := by
  simp [model, hThree, xCoord]

@[simp] theorem value_model_shapeThree (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).shapeThree.value s e4 e3 =
      xCoord (t.value s e4 e3) (2 * b.value s e4 e3) := by
  simp [model, xCoord]

@[simp] theorem value_model_bSubA (t a b : Jet3 box) (data : Data t a b)
    (s e4 e3 : ℝ) :
    (model t a b data).bSubA.value s e4 e3 =
      b.value s e4 e3 - a.value s e4 e3 := by
  simp [model]

end SourceJet

/-- Consumer-level source certificate at one fixed scale. -/
structure Certificate (t : ℝ) (a b : ℝ → ℝ)
    (e4Lo e4Hi e3Lo e3Hi : ℝ) where
  tPos : 0 < t
  tLtOne : t < 1
  e4Ordered : e4Lo ≤ e4Hi
  e3Ordered : e3Lo ≤ e3Hi
  foldLo : 0 < F t (a e4Lo)
  foldHi : F t (a e4Hi) < 0
  areaLo : ∀ e4 ∈ Icc e4Lo e4Hi, E t (a e4) (b e3Lo) < 0
  areaHi : ∀ e4 ∈ Icc e4Lo e4Hi, 0 < E t (a e4) (b e3Hi)
  hFourRegular : ∀ e4 ∈ Icc e4Lo e4Hi,
    hFour t (a e4) ∈ Ioo (0 : ℝ) 1
  shapeThreeRegular : ∀ e3 ∈ Icc e3Lo e3Hi,
    xCoord t (2 * b e3) ∈ Ioo (0 : ℝ) 1
  bAboveA : ∀ e4 ∈ Icc e4Lo e4Hi, ∀ e3 ∈ Icc e3Lo e3Hi,
    a e4 < b e3
  gapNeg : ∀ e4 ∈ Icc e4Lo e4Hi, ∀ e3 ∈ Icc e3Lo e3Hi,
    J t (a e4) (b e3) < 0
  foldContinuous : ContinuousOn (fun e4 => F t (a e4)) (Icc e4Lo e4Hi)
  areaContinuous : ∀ e4 ∈ Icc e4Lo e4Hi,
    ContinuousOn (fun e3 => E t (a e4) (b e3)) (Icc e3Lo e3Hi)

/-- The scalar type-(iii) shape at `hThree` is the doubled coefficient source
coordinate. -/
theorem typeThreeShape_hThree (t b : ℝ) :
    LeanSuffixAnalytic.typeThreeShape (hThree t b) = xCoord t (2 * b) := by
  unfold LeanSuffixAnalytic.typeThreeShape hThree xCoord
  ring

/-- Positive scale reverses coefficient order into height order. -/
theorem hThree_lt_hFour {t a b : ℝ} (ht : 0 < t) (hab : a < b) :
    hThree t b < hFour t a := by
  unfold hThree hFour xCoord
  nlinarith [sq_pos_of_pos ht]

/-- Nested scalar IVTs plus the exact normalization identities produce the
actual stationary equal-area pair and both strict conclusions. -/
theorem Certificate.stationaryEqualAreaPair_strictImprovement
    {t e4Lo e4Hi e3Lo e3Hi : ℝ} {a b : ℝ → ℝ}
    (cert : Certificate t a b e4Lo e4Hi e3Lo e3Hi) :
    ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (lam t),
      LeanSuffixAnalytic.typeThreeFold (lam t) pair.h₃ < 0 ∧
      LeanSuffixAnalytic.typeThreePerimeter (lam t) pair.h₃ <
        LeanSuffixAnalytic.typeFourPerimeter (lam t) pair.h₄ := by
  have hnegContinuous : ContinuousOn (fun e4 => -F t (a e4)) (Icc e4Lo e4Hi) :=
    cert.foldContinuous.neg
  rcases ScalarSuffixCertificate.oppositeFace_zero cert.e4Ordered hnegContinuous
      (neg_nonpos.mpr cert.foldLo.le) (neg_nonneg.mpr cert.foldHi.le) with
    ⟨e4, he4, hfoldNeg⟩
  have hfold : F t (a e4) = 0 := by linarith
  rcases ScalarSuffixCertificate.oppositeFace_zero cert.e3Ordered
      (cert.areaContinuous e4 he4) (cert.areaLo e4 he4).le
      (cert.areaHi e4 he4).le with
    ⟨e3, he3, harea⟩
  have hfour := cert.hFourRegular e4 he4
  have hshape := cert.shapeThreeRegular e3 he3
  have hthreeHalf : 1 / 2 < hThree t (b e3) := by
    rw [← typeThreeShape_hThree] at hshape
    unfold LeanSuffixAnalytic.typeThreeShape at hshape
    norm_num at hshape ⊢
    linarith
  have hthreeOne : hThree t (b e3) < 1 := by
    have htSq : 0 < t ^ 2 := sq_pos_of_pos cert.tPos
    unfold xCoord at hshape
    rcases hshape with ⟨hshapePos, hshapeLt⟩
    unfold hThree xCoord
    ring_nf at hshapePos hshapeLt ⊢
    nlinarith
  have hstationary :
      LeanSuffixAnalytic.typeFourFold (lam t) (hFour t (a e4)) = 0 := by
    rw [NearOneScalarNormalization.typeFourFold_eq_four_mul_F cert.tPos hfour,
      hfold]
    ring
  have hequal :
      LeanSuffixAnalytic.typeThreeArea (lam t) (hThree t (b e3)) =
        LeanSuffixAnalytic.typeFourArea (lam t) (hFour t (a e4)) := by
    have hid := NearOneScalarNormalization.scaled_areaDifference_eq_sq_mul_E
      cert.tPos hfour hshape
    rw [harea] at hid
    have hfactor : 0 < (hThree t (b e3)) ^ 2 * (hFour t (a e4)) ^ 2 :=
      mul_pos (sq_pos_of_pos (lt_trans (by norm_num) hthreeHalf))
        (sq_pos_of_pos hfour.1)
    have htSq : 0 < t ^ 2 := sq_pos_of_pos cert.tPos
    nlinarith
  let pair : LeanSuffixAnalytic.StationaryEqualAreaPair (lam t) :=
    { h₃ := hThree t (b e3)
      h₄ := hFour t (a e4)
      h₃_gt_half := hthreeHalf
      h₃_lt_one := hthreeOne
      h₄_pos := hfour.1
      h₄_lt_one := hfour.2
      equalArea := hequal
      stationary := hstationary }
  have hlam : 1 < lam t := by
    unfold lam
    nlinarith [pow_pos cert.tPos 3]
  have hheight : pair.h₃ < pair.h₄ := by
    exact hThree_lt_hFour cert.tPos (cert.bAboveA e4 he4 e3 he3)
  have hfoldThree : LeanSuffixAnalytic.typeThreeFold (lam t) pair.h₃ < 0 :=
    LeanSuffixAnalytic.typeThreeFold_neg_of_equalArea_of_lt hlam
      ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
      ⟨pair.h₄_pos, pair.h₄_lt_one⟩ hheight pair.equalArea
  have hgap : LeanSuffixAnalytic.reducedFoldGap (lam t) pair.h₃ pair.h₄ < 0 := by
    have hid := NearOneScalarNormalization.hFour_mul_reducedFoldGap_eq_sq_mul_J
      cert.tPos hfour hshape
    have hj := cert.gapNeg e4 he4 e3 he3
    dsimp only [pair] at hid ⊢
    have htSq : 0 < t ^ 2 := sq_pos_of_pos cert.tPos
    by_contra hn
    have hnonneg : 0 ≤ LeanSuffixAnalytic.reducedFoldGap
        (lam t) (hThree t (b e3)) (hFour t (a e4)) := le_of_not_gt hn
    nlinarith [mul_nonneg hfour.1.le hnonneg, mul_neg_of_pos_of_neg htSq hj]
  have hperimeter : LeanSuffixAnalytic.typeThreePerimeter (lam t) pair.h₃ <
      LeanSuffixAnalytic.typeFourPerimeter (lam t) pair.h₄ :=
    (LeanSuffixAnalytic.stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).2 hgap
  exact ⟨pair, hfoldThree, hperimeter⟩

/-- Unchanged candidate-facing consumer for one certified source-native cell. -/
theorem Certificate.candidate_not_isWeightedPerimeterMinimizer
    {t e4Lo e4Hi e3Lo e3Hi : ℝ} {a b : ℝ → ℝ}
    (cert : Certificate t a b e4Lo e4Hi e3Lo e3Hi)
    (candidate : FourArcCandidate (lam t))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases cert.stationaryEqualAreaPair_strictImprovement with
    ⟨pair, hfold, hperimeter⟩
  exact CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair
    candidate hcandidate pair hfold hperimeter

end

end NearOneScalarCell
