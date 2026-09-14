import CMVFiniteJunctionRepair

open Set Function Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology BigOperators symmDiff ContDiff

noncomputable section

namespace CMVRelaxation.FiniteJunctionRepair

open CMVTwoPatchGraphVariation

/-- Inward horizontal coordinate at an oriented rectangle corner. -/
def orientedCornerX (horizontal : OccupiedSide) (center p : PlanePoint) : ℝ :=
  horizontal.areaSign * (p.1 - center.1)

/-- Inward vertical coordinate at an oriented rectangle corner. -/
def orientedCornerY (vertical : OccupiedSide) (center p : PlanePoint) : ℝ :=
  vertical.areaSign * (p.2 - center.2)

/-- Difference coordinate in the inward corner frame. -/
def orientedCornerT (horizontal vertical : OccupiedSide)
    (center p : PlanePoint) : ℝ :=
  orientedCornerX horizontal center p - orientedCornerY vertical center p

/-- Sum coordinate in the inward corner frame. -/
def orientedCornerS (horizontal vertical : OccupiedSide)
    (center p : PlanePoint) : ℝ :=
  orientedCornerX horizontal center p + orientedCornerY vertical center p

/-- The literal sharp one-sector (`sector = below`) or three-sector
(`sector = above`) corner carrier. -/
def openCornerSector (sector horizontal vertical : OccupiedSide)
    (center : PlanePoint) : Set PlanePoint :=
  {p | sector.areaSign *
    (|orientedCornerT horizontal vertical center p| -
      orientedCornerS horizontal vertical center p) < 0}

/-- Smooth rounded replacement of a sharp corner sector. -/
def roundedCornerValue (sector horizontal vertical : OccupiedSide)
    (center : PlanePoint) (r : ℝ) (p : PlanePoint) : ℝ :=
  sector.areaSign *
    (roundedCrossingRadius r (orientedCornerT horizontal vertical center p) -
      orientedCornerS horizontal vertical center p)

/-- Closed coordinate core containing the complete corner modification. -/
def roundedCornerCore (horizontal vertical : OccupiedSide)
    (center : PlanePoint) (r : ℝ) : Set PlanePoint :=
  {p | |orientedCornerT horizontal vertical center p| ≤ 2 * r ∧
    |orientedCornerS horizontal vertical center p| ≤ 3 * r}


lemma openCornerSector_below_mem_iff
    (horizontal vertical : OccupiedSide) (center p : PlanePoint) :
    p ∈ openCornerSector .below horizontal vertical center ↔
      0 < orientedCornerX horizontal center p ∧
        0 < orientedCornerY vertical center p := by
  simp only [openCornerSector, OccupiedSide.areaSign_below, one_mul,
    Set.mem_ofPred_eq]
  let X := orientedCornerX horizontal center p
  let Y := orientedCornerY vertical center p
  change |X - Y| - (X + Y) < 0 ↔ 0 < X ∧ 0 < Y
  constructor
  · intro h
    constructor
    · nlinarith [neg_le_abs (X - Y)]
    · nlinarith [le_abs_self (X - Y)]
  · rintro ⟨hX, hY⟩
    rw [sub_lt_zero, abs_lt]
    constructor <;> linarith

lemma openCornerSector_above_mem_iff
    (horizontal vertical : OccupiedSide) (center p : PlanePoint) :
    p ∈ openCornerSector .above horizontal vertical center ↔
      orientedCornerX horizontal center p < 0 ∨
        orientedCornerY vertical center p < 0 := by
  simp only [openCornerSector, OccupiedSide.areaSign_above, neg_mul, one_mul,
    Set.mem_ofPred_eq]
  let X := orientedCornerX horizontal center p
  let Y := orientedCornerY vertical center p
  change -( |X - Y| - (X + Y)) < 0 ↔ X < 0 ∨ Y < 0
  constructor
  · intro h
    have hs : X + Y < |X - Y| := by linarith
    rw [lt_abs] at hs
    rcases hs with hs | hs
    · right; linarith
    · left; linarith
  · rintro (hX | hY)
    · nlinarith [neg_le_abs (X - Y)]
    · nlinarith [le_abs_self (X - Y)]

lemma contDiff_orientedCornerT
    (horizontal vertical : OccupiedSide) (center : PlanePoint) :
    ContDiff ℝ ∞ (orientedCornerT horizontal vertical center) := by
  unfold orientedCornerT orientedCornerX orientedCornerY
  fun_prop

lemma contDiff_orientedCornerS
    (horizontal vertical : OccupiedSide) (center : PlanePoint) :
    ContDiff ℝ ∞ (orientedCornerS horizontal vertical center) := by
  unfold orientedCornerS orientedCornerX orientedCornerY
  fun_prop

lemma isClosed_roundedCornerCore
    (horizontal vertical : OccupiedSide) (center : PlanePoint) (r : ℝ) :
    IsClosed (roundedCornerCore horizontal vertical center r) := by
  unfold roundedCornerCore
  exact
    (isClosed_le
      (contDiff_orientedCornerT horizontal vertical center).continuous.abs
      continuous_const).inter
    (isClosed_le
      (contDiff_orientedCornerS horizontal vertical center).continuous.abs
      continuous_const)

lemma contDiff_roundedCornerValue
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (roundedCornerValue sector horizontal vertical center r) := by
  unfold roundedCornerValue
  exact contDiff_const.mul <|
    ((contDiff_roundedCrossingRadius hr).comp
      (contDiff_orientedCornerT horizontal vertical center)).sub
        (contDiff_orientedCornerS horizontal vertical center)

lemma roundedCornerValue_regular
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    ∀ p, roundedCornerValue sector horizontal vertical center r p = 0 →
      fderiv ℝ (roundedCornerValue sector horizontal vertical center r) p ≠ 0 := by
  intro p _hp hzero
  let sx := horizontal.areaSign
  let sy := vertical.areaSign
  let curve : ℝ → PlanePoint := fun a => (sx * a + p.1, sy * a + p.2)
  have hsx : sx * sx = 1 := OccupiedSide.areaSign_mul_self horizontal
  have hsy : sy * sy = 1 := OccupiedSide.areaSign_mul_self vertical
  have hcurve : HasDerivAt curve (sx, sy) 0 := by
    have hx : HasDerivAt (fun a : ℝ => sx * a + p.1) sx 0 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id 0).const_mul sx).add_const p.1
    have hy : HasDerivAt (fun a : ℝ => sy * a + p.2) sy 0 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id 0).const_mul sy).add_const p.2
    exact hx.prodMk hy
  have hx : HasDerivAt
      (fun a => orientedCornerX horizontal center (curve a)) 1 0 := by
    have heq :
        (fun a => orientedCornerX horizontal center (curve a)) =
          fun a => a + sx * (p.1 - center.1) := by
      funext a
      simp only [orientedCornerX, curve, sx]
      calc
        horizontal.areaSign *
            (horizontal.areaSign * a + p.1 - center.1) =
            (horizontal.areaSign * horizontal.areaSign) * a +
              horizontal.areaSign * (p.1 - center.1) := by ring
        _ = a + horizontal.areaSign * (p.1 - center.1) := by
          rw [OccupiedSide.areaSign_mul_self]
          ring
    rw [heq]
    have h := (hasDerivAt_id 0).add_const (sx * (p.1 - center.1))
    change HasDerivAt (fun a : ℝ => a + sx * (p.1 - center.1)) 1 0 at h
    exact h
  have hy : HasDerivAt
      (fun a => orientedCornerY vertical center (curve a)) 1 0 := by
    have heq :
        (fun a => orientedCornerY vertical center (curve a)) =
          fun a => a + sy * (p.2 - center.2) := by
      funext a
      simp only [orientedCornerY, curve, sy]
      calc
        vertical.areaSign *
            (vertical.areaSign * a + p.2 - center.2) =
            (vertical.areaSign * vertical.areaSign) * a +
              vertical.areaSign * (p.2 - center.2) := by ring
        _ = a + vertical.areaSign * (p.2 - center.2) := by
          rw [OccupiedSide.areaSign_mul_self]
          ring
    rw [heq]
    have h := (hasDerivAt_id 0).add_const (sy * (p.2 - center.2))
    change HasDerivAt (fun a : ℝ => a + sy * (p.2 - center.2)) 1 0 at h
    exact h
  have hT : HasDerivAt
      (fun a => orientedCornerT horizontal vertical center (curve a)) 0 0 := by
    change HasDerivAt
      ((fun a => orientedCornerX horizontal center (curve a)) -
        fun a => orientedCornerY vertical center (curve a)) 0 0
    simpa only [sub_self] using hx.sub hy
  have hS : HasDerivAt
      (fun a => orientedCornerS horizontal vertical center (curve a))
      ((1 : ℝ) + 1) 0 := by
    change HasDerivAt
      ((fun a => orientedCornerX horizontal center (curve a)) +
        fun a => orientedCornerY vertical center (curve a)) ((1 : ℝ) + 1) 0
    exact hx.add hy
  have hR : HasDerivAt
      (fun a => roundedCrossingRadius r
        (orientedCornerT horizontal vertical center (curve a))) 0 0 := by
    have houter : HasDerivAt (roundedCrossingRadius r)
        (deriv (roundedCrossingRadius r)
          (orientedCornerT horizontal vertical center (curve 0)))
        (orientedCornerT horizontal vertical center (curve 0)) :=
      (contDiff_roundedCrossingRadius hr).differentiable (by simp) _ |>.hasDerivAt
    change HasDerivAt
      (roundedCrossingRadius r ∘
        fun a => orientedCornerT horizontal vertical center (curve a)) 0 0
    simpa only [mul_zero] using houter.comp 0 hT
  have hcomp : HasDerivAt
      (fun a => roundedCornerValue sector horizontal vertical center r (curve a))
      (sector.areaSign * (0 - ((1 : ℝ) + 1))) 0 := by
    change HasDerivAt
      (fun a => sector.areaSign *
        (roundedCrossingRadius r
            (orientedCornerT horizontal vertical center (curve a)) -
          orientedCornerS horizontal vertical center (curve a)))
      (sector.areaSign * (0 - ((1 : ℝ) + 1))) 0
    exact (hR.sub hS).const_mul sector.areaSign
  have hcompZero : HasDerivAt
      (fun a => roundedCornerValue sector horizontal vertical center r (curve a))
      0 0 := by
    have hF : HasFDerivAt
        (roundedCornerValue sector horizontal vertical center r)
        (0 : PlanePoint →L[ℝ] ℝ) (curve 0) := by
      have h := (contDiff_roundedCornerValue sector horizontal vertical center hr)
        |>.differentiable (by simp) p |>.hasFDerivAt
      simpa [curve, hzero] using h
    change HasDerivAt
      (roundedCornerValue sector horizontal vertical center r ∘ curve) 0 0
    simpa only [zero_apply] using hF.comp_hasDerivAt 0 hcurve
  have hbad : sector.areaSign * (0 - ((1 : ℝ) + 1)) = 0 :=
    hcomp.unique hcompZero
  exact OccupiedSide.areaSign_ne_zero sector (by nlinarith)

/-- Every rounded oriented corner is a literal `C∞` smooth domain. -/
theorem isSmoothDomain_roundedCorner
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    IsSmoothDomain
      {p | roundedCornerValue sector horizontal vertical center r p < 0} := by
  exact isSmoothDomain_sublevel_of_regular
    (contDiff_roundedCornerValue sector horizontal vertical center hr)
    (roundedCornerValue_regular sector horizontal vertical center hr)
lemma abs_le_roundedCrossingRadius
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |t| ≤ roundedCrossingRadius r t := by
  have hR0 := (roundedCrossingRadius_pos hr t).le
  apply (sq_le_sq₀ (abs_nonneg t) hR0).mp
  rw [sq_abs, roundedCrossingRadius_sq hr]
  unfold roundedCrossingSquare
  exact le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg r) (oppositeCrossingBump_mem_Icc r t).1)

/-- Rounding changes either corner-sector topology only in a closed `O(r)`
coordinate core. -/
theorem roundedCorner_symmDiff_openCornerSector_subset_core
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    {p | roundedCornerValue sector horizontal vertical center r p < 0} ∆
        openCornerSector sector horizontal vertical center ⊆
      roundedCornerCore horizontal vertical center r := by
  intro p hp
  let t := orientedCornerT horizontal vertical center p
  let s := orientedCornerS horizontal vertical center p
  let R := roundedCrossingRadius r t
  have hR0 : 0 ≤ R := (roundedCrossingRadius_pos hr t).le
  have habsR : |t| ≤ R := abs_le_roundedCrossingRadius hr t
  have ht : |t| < 2 * r := by
    by_contra hnot
    have htwo : 2 * r ≤ |t| := le_of_not_gt hnot
    have hEq : R = |t| := roundedCrossingRadius_eq_abs_of_two_mul_le_abs hr htwo
    simp only [Set.mem_symmDiff, roundedCornerValue, openCornerSector,
      Set.mem_ofPred_eq] at hp
    change
      (sector.areaSign * (R - s) < 0 ∧
          ¬sector.areaSign * (|t| - s) < 0) ∨
        (sector.areaSign * (|t| - s) < 0 ∧
          ¬sector.areaSign * (R - s) < 0) at hp
    rw [hEq] at hp
    exact hp.elim (fun h => h.2 h.1) (fun h => h.2 h.1)
  have htmem : t ∈ Icc (-2 * r) (2 * r) := by
    rw [mem_Icc]
    constructor <;> nlinarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  have hRle : R ≤ 3 * r := roundedCrossingRadius_le_three_mul hr htmem
  have hs : |s| ≤ 3 * r := by
    simp only [Set.mem_symmDiff, roundedCornerValue, openCornerSector,
      Set.mem_ofPred_eq] at hp
    change
      (sector.areaSign * (R - s) < 0 ∧
          ¬sector.areaSign * (|t| - s) < 0) ∨
        (sector.areaSign * (|t| - s) < 0 ∧
          ¬sector.areaSign * (R - s) < 0) at hp
    cases sector with
    | below =>
        simp only [OccupiedSide.areaSign_below, one_mul] at hp
        rcases hp with hp | hp
        · exact False.elim (hp.2 (by nlinarith [habsR]))
        · rw [abs_le]
          constructor <;> nlinarith [abs_nonneg t]
    | above =>
        simp only [OccupiedSide.areaSign_above, neg_mul, one_mul] at hp
        rcases hp with hp | hp
        · rw [abs_le]
          constructor <;> nlinarith [abs_nonneg t]
        · exact False.elim (hp.2 (by nlinarith))
  exact ⟨ht.le, hs⟩

/-- The single smooth boundary branch of a rounded oriented corner. -/
def roundedCornerTrace (horizontal vertical : OccupiedSide)
    (center : PlanePoint) (r t : ℝ) : PlanePoint :=
  let R := roundedCrossingRadius r t
  (center.1 + horizontal.areaSign * ((R + t) / 2),
    center.2 + vertical.areaSign * ((R - t) / 2))

@[simp] lemma orientedCornerT_roundedCornerTrace
    (horizontal vertical : OccupiedSide) (center : PlanePoint) (r t : ℝ) :
    orientedCornerT horizontal vertical center
        (roundedCornerTrace horizontal vertical center r t) = t := by
  cases horizontal <;> cases vertical <;>
    simp only [orientedCornerT, orientedCornerX, orientedCornerY,
      roundedCornerTrace, OccupiedSide.areaSign_below,
      OccupiedSide.areaSign_above] <;>
    ring

@[simp] lemma orientedCornerS_roundedCornerTrace
    (horizontal vertical : OccupiedSide) (center : PlanePoint) (r t : ℝ) :
    orientedCornerS horizontal vertical center
        (roundedCornerTrace horizontal vertical center r t) =
      roundedCrossingRadius r t := by
  cases horizontal <;> cases vertical <;>
    simp only [orientedCornerS, orientedCornerX, orientedCornerY,
      roundedCornerTrace, OccupiedSide.areaSign_below,
      OccupiedSide.areaSign_above] <;>
    ring

/-- The complete rounded-corner frontier is carried by its explicit trace. -/
theorem frontier_roundedCorner_subset_trace
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    frontier {p | roundedCornerValue sector horizontal vertical center r p < 0} ⊆
      roundedCornerTrace horizontal vertical center r '' univ := by
  intro p hp
  have hp0 : roundedCornerValue sector horizontal vertical center r p = 0 :=
    frontier_lt_subset_eq
      (contDiff_roundedCornerValue sector horizontal vertical center hr).continuous
      continuous_const hp
  have hS :
      orientedCornerS horizontal vertical center p =
        roundedCrossingRadius r
          (orientedCornerT horizontal vertical center p) := by
    unfold roundedCornerValue at hp0
    have hzero := (mul_eq_zero.mp hp0).resolve_left
      (OccupiedSide.areaSign_ne_zero sector)
    linarith
  let t := orientedCornerT horizontal vertical center p
  refine ⟨t, mem_univ t, ?_⟩
  apply Prod.ext
  · have hX :
        orientedCornerX horizontal center p =
          (roundedCrossingRadius r t + t) / 2 := by
      calc
        orientedCornerX horizontal center p =
            (orientedCornerS horizontal vertical center p +
              orientedCornerT horizontal vertical center p) / 2 := by
                unfold orientedCornerS orientedCornerT
                ring
        _ = (roundedCrossingRadius r t + t) / 2 := by
          rw [hS]
    unfold roundedCornerTrace
    dsimp only
    rw [← hX]
    unfold orientedCornerX
    have hsquare := OccupiedSide.areaSign_mul_self horizontal
    calc
      center.1 + horizontal.areaSign *
          (horizontal.areaSign * (p.1 - center.1)) =
          center.1 +
            (horizontal.areaSign * horizontal.areaSign) *
              (p.1 - center.1) := by ring
      _ = p.1 := by rw [hsquare]; ring
  · have hY :
        orientedCornerY vertical center p =
          (roundedCrossingRadius r t - t) / 2 := by
      calc
        orientedCornerY vertical center p =
            (orientedCornerS horizontal vertical center p -
              orientedCornerT horizontal vertical center p) / 2 := by
                unfold orientedCornerS orientedCornerT
                ring
        _ = (roundedCrossingRadius r t - t) / 2 := by
          rw [hS]
    unfold roundedCornerTrace
    dsimp only
    rw [← hY]
    unfold orientedCornerY
    have hsquare := OccupiedSide.areaSign_mul_self vertical
    calc
      center.2 + vertical.areaSign *
          (vertical.areaSign * (p.2 - center.2)) =
          center.2 +
            (vertical.areaSign * vertical.areaSign) *
              (p.2 - center.2) := by ring
      _ = p.2 := by rw [hsquare]; ring

/-- Inside the modification core, the rounded frontier only uses parameters
from the shrinking interval `[-2r,2r]`. -/
theorem frontier_roundedCorner_inter_core_subset_trace
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    frontier {p | roundedCornerValue sector horizontal vertical center r p < 0} ∩
        roundedCornerCore horizontal vertical center r ⊆
      roundedCornerTrace horizontal vertical center r ''
        Icc (-2 * r) (2 * r) := by
  intro p hp
  rcases frontier_roundedCorner_subset_trace sector horizontal vertical center hr
      hp.1 with ⟨t, _ht, rfl⟩
  have ht := hp.2.1
  rw [orientedCornerT_roundedCornerTrace, abs_le] at ht
  exact ⟨t, by simpa only [mem_Icc, neg_mul] using ht, rfl⟩


def roundedCornerTraceX (horizontal : OccupiedSide)
    (center : PlanePoint) (r t : ℝ) : ℝ :=
  center.1 + horizontal.areaSign * ((roundedCrossingRadius r t + t) / 2)

def roundedCornerTraceY (vertical : OccupiedSide)
    (center : PlanePoint) (r t : ℝ) : ℝ :=
  center.2 + vertical.areaSign * ((roundedCrossingRadius r t - t) / 2)

lemma roundedCornerTrace_eq
    (horizontal vertical : OccupiedSide) (center : PlanePoint) (r : ℝ) :
    roundedCornerTrace horizontal vertical center r =
      fun t => (roundedCornerTraceX horizontal center r t,
        roundedCornerTraceY vertical center r t) := by
  funext t
  rfl

lemma contDiff_roundedCornerTraceX
    (horizontal : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (roundedCornerTraceX horizontal center r) := by
  unfold roundedCornerTraceX
  exact contDiff_const.add <|
    contDiff_const.mul <|
      ((contDiff_roundedCrossingRadius hr).add contDiff_id).div_const 2

lemma contDiff_roundedCornerTraceY
    (vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (roundedCornerTraceY vertical center r) := by
  unfold roundedCornerTraceY
  exact contDiff_const.add <|
    contDiff_const.mul <|
      ((contDiff_roundedCrossingRadius hr).sub contDiff_id).div_const 2

lemma deriv_roundedCornerTraceX
    (horizontal : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    deriv (roundedCornerTraceX horizontal center r) t =
      horizontal.areaSign *
        ((deriv (roundedCrossingRadius r) t + 1) / 2) := by
  have hR := (contDiff_roundedCrossingRadius hr).differentiable
    (by simp) t |>.hasDerivAt
  have hderiv :=
    (((hR.add (hasDerivAt_id t)).div_const 2).const_mul
      horizontal.areaSign).const_add center.1
  exact hderiv.deriv

lemma deriv_roundedCornerTraceY
    (vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    deriv (roundedCornerTraceY vertical center r) t =
      vertical.areaSign *
        ((deriv (roundedCrossingRadius r) t - 1) / 2) := by
  have hR := (contDiff_roundedCrossingRadius hr).differentiable
    (by simp) t |>.hasDerivAt
  have hderiv :=
    (((hR.sub (hasDerivAt_id t)).div_const 2).const_mul
      vertical.areaSign).const_add center.2
  exact hderiv.deriv

lemma roundedCornerTrace_speed_le
    (horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) (Kr : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ)) :
    ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt
          ((deriv (roundedCornerTraceX horizontal center r) t) ^ 2 +
            (deriv (roundedCornerTraceY vertical center r) t) ^ 2) ≤
        (Kr : ℝ) := by
  intro t ht
  let q := deriv (roundedCrossingRadius r) t
  have hsx := OccupiedSide.areaSign_mul_self horizontal
  have hsy := OccupiedSide.areaSign_mul_self vertical
  rw [deriv_roundedCornerTraceX horizontal center hr,
    deriv_roundedCornerTraceY vertical center hr]
  change Real.sqrt
      ((horizontal.areaSign * ((q + 1) / 2)) ^ 2 +
        (vertical.areaSign * ((q - 1) / 2)) ^ 2) ≤ (Kr : ℝ)
  have hinside :
      (horizontal.areaSign * ((q + 1) / 2)) ^ 2 +
          (vertical.areaSign * ((q - 1) / 2)) ^ 2 =
        (1 + q ^ 2) / 2 := by
    cases horizontal <;> cases vertical <;>
      simp only [OccupiedSide.areaSign_below, OccupiedSide.areaSign_above] <;>
      ring
  rw [hinside]
  exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg q])).trans (hKr t ht)

/-- Complete weighted cost of the altered rounded-corner frontier is `O(r)`. -/
theorem weightedTraceCost_frontier_roundedCorner_inter_core_le
    {lam : ℝ} (hlam : 1 < lam)
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} (hr : 0 < r) (Kr : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ)) :
    weightedTraceCost lam
        (frontier
            {p | roundedCornerValue sector horizontal vertical center r p < 0} ∩
          roundedCornerCore horizontal vertical center r) ≤
      ENNReal.ofReal lam * (Kr : ENNReal) * ENNReal.ofReal (4 * r) := by
  apply (weightedTraceCost_mono lam
    (frontier_roundedCorner_inter_core_subset_trace
      sector horizontal vertical center hr)).trans
  rw [roundedCornerTrace_eq]
  simpa only [show 2 * r - -2 * r = 4 * r by ring] using
    (weightedTraceCost_planeParam_Icc_le_global hlam
      ((contDiff_roundedCornerTraceX horizontal center hr).differentiable (by simp))
      ((contDiff_roundedCornerTraceY vertical center hr).differentiable (by simp))
      (roundedCornerTrace_speed_le horizontal vertical center hr Kr hKr))

lemma roundedCornerCore_coordinate_bounds
    (horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r : ℝ} {p : PlanePoint}
    (hp : p ∈ roundedCornerCore horizontal vertical center r) :
    |p.1 - center.1| ≤ 5 * r / 2 ∧
      |p.2 - center.2| ≤ 5 * r / 2 := by
  have ht := abs_le.mp hp.1
  have hs := abs_le.mp hp.2
  have hX :
      |orientedCornerX horizontal center p| ≤ 5 * r / 2 := by
    rw [abs_le]
    unfold orientedCornerT at ht
    unfold orientedCornerS at hs
    constructor <;> nlinarith
  have hY :
      |orientedCornerY vertical center p| ≤ 5 * r / 2 := by
    rw [abs_le]
    unfold orientedCornerT at ht
    unfold orientedCornerS at hs
    constructor <;> nlinarith
  constructor
  · cases horizontal with
    | below => simpa [orientedCornerX] using hX
    | above => simpa [orientedCornerX, abs_sub_comm] using hX
  · cases vertical with
    | below => simpa [orientedCornerY] using hY
    | above => simpa [orientedCornerY, abs_sub_comm] using hY

/-- A sufficiently small coordinate core lies in the requested Euclidean
junction ball. -/
theorem roundedCornerCore_subset_junctionBall
    (horizontal vertical : OccupiedSide) (center : PlanePoint)
    {r rho : ℝ} (hsmall : 5 * r ≤ rho) :
    roundedCornerCore horizontal vertical center r ⊆
      junctionBall center rho := by
  intro p hp
  have hcoord := roundedCornerCore_coordinate_bounds horizontal vertical center hp
  change dist (planeEuclideanHomeomorph p)
      (planeEuclideanHomeomorph center) ≤ rho
  exact (dist_planeEuclideanHomeomorph_le_coordinate_sum
    p.1 p.2 center.1 center.2).trans (by
      rw [Real.dist_eq, Real.dist_eq]
      linarith)


/-- The complete altered-frontier cost of a shrinking rounded corner tends to
zero, uniformly in the occupied sector and both coordinate orientations. -/
theorem tendsto_weightedTraceCost_roundedCorner_alteredFrontier_zero
    {lam : ℝ} (hlam : 1 < lam)
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n =>
      let r := symmetricConnectorRadius R n
      weightedTraceCost lam
        (frontier
            {p | roundedCornerValue sector horizontal vertical center r p < 0} ∩
          roundedCornerCore horizontal vertical center r))
      atTop (𝓝 0) := by
  obtain ⟨Kr, hKr⟩ := exists_roundedCrossingRadius_deriv_bound
  let C : ENNReal := ENNReal.ofReal lam * (Kr : ENNReal)
  have hrzero := tendsto_symmetricConnectorRadius_zero R
  have hfourReal :
      Tendsto (fun n => 4 * symmetricConnectorRadius R n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrzero
  have hfour :
      Tendsto (fun n => ENNReal.ofReal (4 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hfourReal
  have hupper :
      Tendsto (fun n =>
        C * ENNReal.ofReal (4 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hfour
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    exact bot_le
  · intro n
    simpa only [C] using
      (weightedTraceCost_frontier_roundedCorner_inter_core_le
        hlam sector horizontal vertical center
        (symmetricConnectorRadius_pos hR n) Kr
        (hKr (symmetricConnectorRadius_pos hR n)))

/-- Actual `C∞` repair family for a clean one- or three-sector rectangle
corner.  The same construction handles all four corner orientations. -/
theorem exists_vanishing_smoothCornerSectorRepair
    {lam : ℝ} (hlam : 1 < lam)
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {R : ℝ} (hR : 0 < R) :
    ∃ (U modification : ℕ → Set PlanePoint),
      (∀ n, IsSmoothDomain (U n)) ∧
      (∀ n, IsClosed (modification n)) ∧
      (∀ n,
        U n ∆ openCornerSector sector horizontal vertical center ⊆
          modification n) ∧
      (∀ rho, 0 < rho →
        ∀ᶠ n : ℕ in atTop,
          modification n ⊆ junctionBall center rho) ∧
      Tendsto (fun n =>
        volume (U n ∆
          openCornerSector sector horizontal vertical center))
        atTop (𝓝 0) ∧
      (∀ n p, p ∉ modification n →
        (p ∈ U n ↔
          p ∈ openCornerSector sector horizontal vertical center)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
  let r : ℕ → ℝ := symmetricConnectorRadius R
  let U : ℕ → Set PlanePoint := fun n =>
    {p | roundedCornerValue sector horizontal vertical center (r n) p < 0}
  let modification : ℕ → Set PlanePoint := fun n =>
    roundedCornerCore horizontal vertical center (r n)
  have hUsmooth : ∀ n, IsSmoothDomain (U n) := by
    intro n
    exact isSmoothDomain_roundedCorner sector horizontal vertical center
      (symmetricConnectorRadius_pos hR n)
  have hmodificationClosed : ∀ n, IsClosed (modification n) := by
    intro n
    exact isClosed_roundedCornerCore horizontal vertical center (r n)
  have hmodify : ∀ n,
      U n ∆ openCornerSector sector horizontal vertical center ⊆
        modification n := by
    intro n
    exact roundedCorner_symmDiff_openCornerSector_subset_core
      sector horizontal vertical center
      (symmetricConnectorRadius_pos hR n)
  have hball : ∀ rho, 0 < rho →
      ∀ᶠ n : ℕ in atTop,
        modification n ⊆ junctionBall center rho := by
    intro rho hrho
    have hfive :
        Tendsto (fun n => 5 * symmetricConnectorRadius R n)
          atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_symmetricConnectorRadius_zero R)
    have hevent :
        ∀ᶠ n : ℕ in atTop, 5 * symmetricConnectorRadius R n < rho :=
      hfive.eventually (Iio_mem_nhds hrho)
    filter_upwards [hevent] with n hn
    exact roundedCornerCore_subset_junctionBall horizontal vertical center hn.le
  have hvolume :
      Tendsto (fun n =>
        volume (U n ∆
          openCornerSector sector horizontal vertical center))
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro epsilon hepsilon
    have hballVolume := tendsto_volume_junctionBall_zero center
    rw [ENNReal.tendsto_atTop_zero] at hballVolume
    obtain ⟨m, hm⟩ := hballVolume epsilon hepsilon
    have hevent := hball (junctionRadius m) (junctionRadius_pos m)
    rcases eventually_atTop.1 hevent with ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (measure_mono ((hmodify n).trans (hN n hn))).trans (hm m le_rfl)⟩
  have hexterior : ∀ n p, p ∉ modification n →
      (p ∈ U n ↔
        p ∈ openCornerSector sector horizontal vertical center) := by
    intro n p hpNotModification
    have hpNotDiff :
        p ∉ U n ∆ openCornerSector sector horizontal vertical center :=
      fun hp => hpNotModification (hmodify n hp)
    simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hpNotDiff
    exact ⟨hpNotDiff.1, hpNotDiff.2⟩
  have hcost :
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
    simpa only [U, modification, r] using
      (tendsto_weightedTraceCost_roundedCorner_alteredFrontier_zero
        hlam sector horizontal vertical center hR)
  exact ⟨U, modification, hUsmooth, hmodificationClosed, hmodify, hball,
    hvolume, hexterior, hcost⟩

/-- Finite-radius, finite-budget clean-corner repair, selecting one member of
the vanishing family. -/
theorem exists_smoothCornerSectorRepair
    {lam : ℝ} (hlam : 1 < lam)
    (sector horizontal vertical : OccupiedSide) (center : PlanePoint)
    {R rho epsilon : ℝ} (hR : 0 < R)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (U modification : Set PlanePoint),
      0 < r ∧ r < R ∧
      IsSmoothDomain U ∧
      IsClosed modification ∧
      U ∆ openCornerSector sector horizontal vertical center ⊆ modification ∧
      modification ⊆ junctionBall center rho ∧
      (∀ p, p ∉ modification →
        (p ∈ U ↔
          p ∈ openCornerSector sector horizontal vertical center)) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  obtain ⟨U, modification, hUsmooth, hmodificationClosed, hmodify, hball,
    _hvolume, hexterior, hcost⟩ :=
    exists_vanishing_smoothCornerSectorRepair
      hlam sector horizontal vertical center hR
  have heventRadius :
      ∀ᶠ n : ℕ in atTop, symmetricConnectorRadius R n < R :=
    (tendsto_symmetricConnectorRadius_zero R).eventually (Iio_mem_nhds hR)
  have heventBall := hball rho hrho
  have heventCost :
      ∀ᶠ n : ℕ in atTop,
        weightedTraceCost lam (frontier (U n) ∩ modification n) <
          ENNReal.ofReal epsilon :=
    hcost.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  obtain ⟨n, hnRadius, hnBall, hnCost⟩ :=
    (heventRadius.and (heventBall.and heventCost)).exists
  let r := symmetricConnectorRadius R n
  exact ⟨r, U n, modification n, symmetricConnectorRadius_pos hR n,
    hnRadius, hUsmooth n, hmodificationClosed n, hmodify n, hnBall,
    hexterior n, hnCost⟩


/-- Every rectangle corner has one oriented coordinate neighborhood on which
the rectangle interior is exactly the one-sector model and the rectangle
exterior is exactly the three-sector model.  The neighborhood excludes the two
opposite rectangle faces; no generic-position premise is used. -/
theorem exists_orientedCorner_local_models_closedCutRectangle
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) {p : PlanePoint}
    (hpCorner : p ∈ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint)) :
    ∃ (horizontal vertical : OccupiedSide) (N : Set PlanePoint),
      IsOpen N ∧ p ∈ N ∧
      interior (closedCutRectangle l r d u) ∩ N =
        openCornerSector .below horizontal vertical p ∩ N ∧
      interior ((closedCutRectangle l r d u)ᶜ) ∩ N =
        openCornerSector .above horizontal vertical p ∩ N := by
  simp only [mem_insert_iff, mem_singleton_iff] at hpCorner
  rcases hpCorner with rfl | rfl | rfl | rfl
  · let N : Set PlanePoint :=
      Prod.fst ⁻¹' Iio r ∩ Prod.snd ⁻¹' Iio u
    refine ⟨.below, .below, N,
      (isOpen_Iio.preimage continuous_fst).inter
        (isOpen_Iio.preimage continuous_snd), ?_, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Iio] using hlr,
        by simpa only [mem_preimage, mem_Iio] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [N, mem_inter_iff, mem_prod, mem_Ioo, mem_preimage, mem_Iio,
        openCornerSector_below_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_below, one_mul]
      constructor
      · rintro ⟨⟨⟨hxl, hxr⟩, ⟨hyd, hyu⟩⟩, hxr', hyu'⟩
        exact ⟨⟨by linarith, by linarith⟩, hxr', hyu'⟩
      · rintro ⟨⟨hx, hy⟩, hxr, hyu⟩
        exact ⟨⟨⟨by linarith, hxr⟩, ⟨by linarith, hyu⟩⟩, hxr, hyu⟩
    · rw [show interior ((closedCutRectangle l r d u)ᶜ) =
          (closedCutRectangle l r d u)ᶜ by
        exact (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      simp only [closedCutRectangle, N, mem_inter_iff, mem_compl_iff,
        mem_prod, mem_Icc, mem_preimage, mem_Iio,
        openCornerSector_above_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_below, one_mul]
      constructor
      · rintro ⟨hnot, hxr, hyu⟩
        refine ⟨?_, hxr, hyu⟩
        by_contra h
        push Not at h
        exact hnot ⟨⟨by linarith, hxr.le⟩, ⟨by linarith, hyu.le⟩⟩
      · rintro ⟨hxy, hxr, hyu⟩
        refine ⟨?_, hxr, hyu⟩
        intro hW
        rcases hxy with hx | hy
        · linarith [hW.1.1]
        · linarith [hW.2.1]
  · let N : Set PlanePoint :=
      Prod.fst ⁻¹' Iio r ∩ Prod.snd ⁻¹' Ioi d
    refine ⟨.below, .above, N,
      (isOpen_Iio.preimage continuous_fst).inter
        (isOpen_Ioi.preimage continuous_snd), ?_, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Iio] using hlr,
        by simpa only [mem_preimage, mem_Ioi] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [N, mem_inter_iff, mem_prod, mem_Ioo, mem_preimage, mem_Iio,
        mem_Ioi, openCornerSector_below_mem_iff, orientedCornerX,
        orientedCornerY, OccupiedSide.areaSign_below,
        OccupiedSide.areaSign_above, one_mul, neg_mul]
      constructor
      · rintro ⟨⟨⟨hxl, hxr⟩, ⟨hyd, hyu⟩⟩, hxr', hyd'⟩
        exact ⟨⟨by linarith, by linarith⟩, hxr', hyd'⟩
      · rintro ⟨⟨hx, hy⟩, hxr, hyd⟩
        exact ⟨⟨⟨by linarith, hxr⟩, ⟨hyd, by linarith⟩⟩, hxr, hyd⟩
    · rw [show interior ((closedCutRectangle l r d u)ᶜ) =
          (closedCutRectangle l r d u)ᶜ by
        exact (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      simp only [closedCutRectangle, N, mem_inter_iff, mem_compl_iff,
        mem_prod, mem_Icc, mem_preimage, mem_Iio, mem_Ioi,
        openCornerSector_above_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_below, OccupiedSide.areaSign_above,
        one_mul, neg_mul]
      constructor
      · rintro ⟨hnot, hxr, hyd⟩
        refine ⟨?_, hxr, hyd⟩
        by_contra h
        push Not at h
        exact hnot ⟨⟨by linarith, hxr.le⟩, ⟨hyd.le, by linarith⟩⟩
      · rintro ⟨hxy, hxr, hyd⟩
        refine ⟨?_, hxr, hyd⟩
        intro hW
        rcases hxy with hx | hy
        · linarith [hW.1.1]
        · linarith [hW.2.2]
  · let N : Set PlanePoint :=
      Prod.fst ⁻¹' Ioi l ∩ Prod.snd ⁻¹' Iio u
    refine ⟨.above, .below, N,
      (isOpen_Ioi.preimage continuous_fst).inter
        (isOpen_Iio.preimage continuous_snd), ?_, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Ioi] using hlr,
        by simpa only [mem_preimage, mem_Iio] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [N, mem_inter_iff, mem_prod, mem_Ioo, mem_preimage, mem_Iio,
        mem_Ioi, openCornerSector_below_mem_iff, orientedCornerX,
        orientedCornerY, OccupiedSide.areaSign_below,
        OccupiedSide.areaSign_above, one_mul, neg_mul]
      constructor
      · rintro ⟨⟨⟨hxl, hxr⟩, ⟨hyd, hyu⟩⟩, hxl', hyu'⟩
        exact ⟨⟨by linarith, by linarith⟩, hxl', hyu'⟩
      · rintro ⟨⟨hx, hy⟩, hxl, hyu⟩
        exact ⟨⟨⟨hxl, by linarith⟩, ⟨by linarith, hyu⟩⟩, hxl, hyu⟩
    · rw [show interior ((closedCutRectangle l r d u)ᶜ) =
          (closedCutRectangle l r d u)ᶜ by
        exact (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      simp only [closedCutRectangle, N, mem_inter_iff, mem_compl_iff,
        mem_prod, mem_Icc, mem_preimage, mem_Iio, mem_Ioi,
        openCornerSector_above_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_below, OccupiedSide.areaSign_above,
        one_mul, neg_mul]
      constructor
      · rintro ⟨hnot, hxl, hyu⟩
        refine ⟨?_, hxl, hyu⟩
        by_contra h
        push Not at h
        exact hnot ⟨⟨hxl.le, by linarith⟩, ⟨by linarith, hyu.le⟩⟩
      · rintro ⟨hxy, hxl, hyu⟩
        refine ⟨?_, hxl, hyu⟩
        intro hW
        rcases hxy with hx | hy
        · linarith [hW.1.2]
        · linarith [hW.2.1]
  · let N : Set PlanePoint :=
      Prod.fst ⁻¹' Ioi l ∩ Prod.snd ⁻¹' Ioi d
    refine ⟨.above, .above, N,
      (isOpen_Ioi.preimage continuous_fst).inter
        (isOpen_Ioi.preimage continuous_snd), ?_, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Ioi] using hlr,
        by simpa only [mem_preimage, mem_Ioi] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [N, mem_inter_iff, mem_prod, mem_Ioo, mem_preimage, mem_Ioi,
        openCornerSector_below_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_above, neg_mul]
      constructor
      · rintro ⟨⟨⟨hxl, hxr⟩, ⟨hyd, hyu⟩⟩, hxl', hyd'⟩
        exact ⟨⟨by linarith, by linarith⟩, hxl', hyd'⟩
      · rintro ⟨⟨hx, hy⟩, hxl, hyd⟩
        exact ⟨⟨⟨hxl, by linarith⟩, ⟨hyd, by linarith⟩⟩, hxl, hyd⟩
    · rw [show interior ((closedCutRectangle l r d u)ᶜ) =
          (closedCutRectangle l r d u)ᶜ by
        exact (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      simp only [closedCutRectangle, N, mem_inter_iff, mem_compl_iff,
        mem_prod, mem_Icc, mem_preimage, mem_Ioi,
        openCornerSector_above_mem_iff, orientedCornerX, orientedCornerY,
        OccupiedSide.areaSign_above, neg_mul]
      constructor
      · rintro ⟨hnot, hxl, hyd⟩
        refine ⟨?_, hxl, hyd⟩
        by_contra h
        push Not at h
        exact hnot ⟨⟨hxl.le, by linarith⟩, ⟨hyd.le, by linarith⟩⟩
      · rintro ⟨hxy, hxl, hyd⟩
        refine ⟨?_, hxl, hyd⟩
        intro hW
        rcases hxy with hx | hy
        · linarith [hW.1.2]
        · linarith [hW.2.2]

/-- A clean selected-splice corner—one through which neither input frontier
passes—is locally exactly one of the oriented one- or three-sector models.
This attaches the abstract corner model to the actual `selectedRawSplice`
carrier and retains all four cut-corner orientations. -/
theorem exists_selectedRawSplice_cleanCorner_local_model
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    (hA : ∀ n, IsOpen (A n)) (hG : ∀ n, IsOpen (G n))
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    {n : ℕ} {p : PlanePoint}
    (hpCorner : p ∈ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint))
    (hpFront : p ∈ frontier (selectedRawSplice A G l r d u n))
    (hpA : p ∉ frontier (A n)) (hpG : p ∉ frontier (G n)) :
    ∃ (sector horizontal vertical : OccupiedSide) (N : Set PlanePoint),
      IsOpen N ∧ p ∈ N ∧
      selectedRawSplice A G l r d u n ∩ N =
        openCornerSector sector horizontal vertical p ∩ N := by
  obtain ⟨_hcut, hcase⟩ :=
    selectedRawSplice_corner_mem_cutTrace_and_local_cases
      A G l r d u hA hG hlr hdu hpCorner hpFront
  obtain ⟨horizontal, vertical, Ncorner, hNcorner, hpNcorner,
      hinterior, hexterior⟩ :=
    exists_orientedCorner_local_models_closedCutRectangle
      (hlr n) (hdu n) hpCorner
  rcases hcase with hinput | hinside | houtside
  · exact False.elim (hinput.elim hpA hpG)
  · rcases hinside with ⟨Nraw, hNraw, hpNraw, hraw⟩
    refine ⟨.below, horizontal, vertical, Nraw ∩ Ncorner,
      hNraw.inter hNcorner, ⟨hpNraw, hpNcorner⟩, ?_⟩
    calc
      selectedRawSplice A G l r d u n ∩ (Nraw ∩ Ncorner) =
          (selectedRawSplice A G l r d u n ∩ Nraw) ∩ Ncorner := by
            ext q
            simp only [mem_inter_iff]
            tauto
      _ = (interior (closedCutRectangle (l n) (r n) (d n) (u n)) ∩
            Nraw) ∩ Ncorner := by rw [hraw]
      _ = (interior (closedCutRectangle (l n) (r n) (d n) (u n)) ∩
            Ncorner) ∩ Nraw := by
              ext q
              simp only [mem_inter_iff]
              tauto
      _ = (openCornerSector .below horizontal vertical p ∩ Ncorner) ∩
            Nraw := by rw [hinterior]
      _ = openCornerSector .below horizontal vertical p ∩
            (Nraw ∩ Ncorner) := by
              ext q
              simp only [mem_inter_iff]
              tauto
  · rcases houtside with ⟨Nraw, hNraw, hpNraw, hraw⟩
    refine ⟨.above, horizontal, vertical, Nraw ∩ Ncorner,
      hNraw.inter hNcorner, ⟨hpNraw, hpNcorner⟩, ?_⟩
    calc
      selectedRawSplice A G l r d u n ∩ (Nraw ∩ Ncorner) =
          (selectedRawSplice A G l r d u n ∩ Nraw) ∩ Ncorner := by
            ext q
            simp only [mem_inter_iff]
            tauto
      _ = (interior ((closedCutRectangle
            (l n) (r n) (d n) (u n))ᶜ) ∩ Nraw) ∩ Ncorner := by rw [hraw]
      _ = (interior ((closedCutRectangle
            (l n) (r n) (d n) (u n))ᶜ) ∩ Ncorner) ∩ Nraw := by
              ext q
              simp only [mem_inter_iff]
              tauto
      _ = (openCornerSector .above horizontal vertical p ∩ Ncorner) ∩
            Nraw := by rw [hexterior]
      _ = openCornerSector .above horizontal vertical p ∩
            (Nraw ∩ Ncorner) := by
              ext q
              simp only [mem_inter_iff]
              tauto

/-- Every open neighborhood of a point contains one positive-radius pulled-back
Euclidean junction ball. -/
lemma exists_junctionBall_subset_open
    {N : Set PlanePoint} (hN : IsOpen N) {p : PlanePoint} (hp : p ∈ N) :
    ∃ rho : ℝ, 0 < rho ∧ junctionBall p rho ⊆ N := by
  have hevent := eventually_neighborhood_subset_open
    ({p} : Finset PlanePoint) hN (by
      intro q hq
      have hqp : q = p := by
        simpa only [Finset.coe_singleton, mem_singleton_iff] using hq
      simpa only [hqp] using hp)
  obtain ⟨m, hm⟩ := hevent.exists
  refine ⟨junctionRadius m, junctionRadius_pos m, ?_⟩
  intro q hq
  apply hm
  simp only [neighborhood, Finset.mem_singleton, iUnion_iUnion_eq_left]
  exact hq

/-- Quantitative `C∞` repair of an actual clean selected-splice corner.  The
new local carrier agrees with the actual selected splice throughout the
containing junction ball outside its explicit modification set, and the
complete altered weighted frontier has the requested budget. -/
theorem exists_smoothSelectedRawSpliceCleanCornerRepair
    {lam : ℝ} (hlam : 1 < lam)
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    (hA : ∀ n, IsOpen (A n)) (hG : ∀ n, IsOpen (G n))
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    {n : ℕ} {p : PlanePoint}
    (hpCorner : p ∈ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint))
    (hpFront : p ∈ frontier (selectedRawSplice A G l r d u n))
    (hpA : p ∉ frontier (A n)) (hpG : p ∉ frontier (G n))
    {R epsilon : ℝ} (hR : 0 < R) (hepsilon : 0 < epsilon) :
    ∃ (sector horizontal vertical : OccupiedSide) (N : Set PlanePoint)
        (rho rCorner : ℝ) (U modification : Set PlanePoint),
      IsOpen N ∧ p ∈ N ∧ 0 < rho ∧ junctionBall p rho ⊆ N ∧
      selectedRawSplice A G l r d u n ∩ N =
        openCornerSector sector horizontal vertical p ∩ N ∧
      0 < rCorner ∧ rCorner < R ∧ IsSmoothDomain U ∧
      IsClosed modification ∧
      (U ∆ selectedRawSplice A G l r d u n) ∩ junctionBall p rho ⊆
        modification ∧
      modification ⊆ junctionBall p (rho / 2) ∧
      (∀ q ∈ N, q ∉ modification →
        (q ∈ U ↔ q ∈ selectedRawSplice A G l r d u n)) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  obtain ⟨sector, horizontal, vertical, N, hN, hpN, hlocal⟩ :=
    exists_selectedRawSplice_cleanCorner_local_model
      A G l r d u hA hG hlr hdu hpCorner hpFront hpA hpG
  obtain ⟨rho, hrho, hball⟩ := exists_junctionBall_subset_open hN hpN
  obtain ⟨rCorner, U, modification, hrCorner, hrCornerR, hUsmooth,
      hmodificationClosed, hmodify, hmodificationBall, hexterior, hcost⟩ :=
    exists_smoothCornerSectorRepair
      hlam sector horizontal vertical p hR (by positivity : 0 < rho / 2)
        hepsilon
  refine ⟨sector, horizontal, vertical, N, rho, rCorner, U, modification,
    hN, hpN, hrho, hball, hlocal, hrCorner, hrCornerR, hUsmooth,
    hmodificationClosed, ?_, hmodificationBall, ?_, hcost⟩
  · intro q hq
    apply hmodify
    have hqN : q ∈ N := hball hq.2
    have hlocalq := Set.ext_iff.mp hlocal q
    have hrawSector :
        q ∈ selectedRawSplice A G l r d u n ↔
          q ∈ openCornerSector sector horizontal vertical p := by
      simpa only [mem_inter_iff, hqN, and_true] using hlocalq
    rw [Set.mem_inter_iff, Set.mem_symmDiff] at hq
    rw [Set.mem_symmDiff]
    rcases hq.1 with hq | hq
    · exact Or.inl ⟨hq.1, fun hs => hq.2 (hrawSector.mpr hs)⟩
    · exact Or.inr ⟨hrawSector.mp hq.1, hq.2⟩
  · intro q hqN hqModification
    have hlocalq := Set.ext_iff.mp hlocal q
    have hrawSector :
        q ∈ selectedRawSplice A G l r d u n ↔
          q ∈ openCornerSector sector horizontal vertical p := by
      simpa only [mem_inter_iff, hqN, and_true] using hlocalq
    exact (hexterior q hqModification).trans hrawSector.symm

lemma junctionSphere_disjoint_half_junctionBall
    (p : PlanePoint) {rho : ℝ} (hrho : 0 < rho) :
    Disjoint (junctionSphere p rho) (junctionBall p (rho / 2)) := by
  rw [Set.disjoint_left]
  intro q hqSphere hqBall
  change dist (planeEuclideanHomeomorph q)
      (planeEuclideanHomeomorph p) = rho at hqSphere
  change dist (planeEuclideanHomeomorph q)
      (planeEuclideanHomeomorph p) ≤ rho / 2 at hqBall
  linarith

/-- Graft the quantitative clean-corner model into the actual selected raw
splice across a larger closed ball.  Exact agreement on the annular collar
makes the graft open; all carrier change stays in the inner half-ball.  Its
complete frontier is covered by unchanged raw frontier, the explicitly
budgeted rounded trace, and the outer junction sphere. -/
theorem exists_openGraftedSelectedRawSpliceCleanCornerRepair
    {lam : ℝ} (hlam : 1 < lam)
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    (hA : ∀ n, IsOpen (A n)) (hG : ∀ n, IsOpen (G n))
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    {n : ℕ} {p : PlanePoint}
    (hpCorner : p ∈ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint))
    (hpFront : p ∈ frontier (selectedRawSplice A G l r d u n))
    (hpA : p ∉ frontier (A n)) (hpG : p ∉ frontier (G n))
    {R epsilon : ℝ} (hR : 0 < R) (hepsilon : 0 < epsilon) :
    ∃ (rho : ℝ) (repaired modification auxiliary : Set PlanePoint),
      0 < rho ∧ IsOpen repaired ∧ IsClosed modification ∧
      repaired ∆ selectedRawSplice A G l r d u n ⊆ modification ∧
      modification ⊆ junctionBall p (rho / 2) ∧
      (∀ q, q ∉ modification →
        (q ∈ repaired ↔ q ∈ selectedRawSplice A G l r d u n)) ∧
      frontier repaired ⊆
        (frontier (selectedRawSplice A G l r d u n) ∩
          (junctionBall p rho)ᶜ) ∪ auxiliary ∧
      auxiliary =
        (frontier (selectedRawSplice A G l r d u n) ∩
            junctionBall p rho) ∪
          (frontier repaired ∩ modification) ∪ junctionSphere p rho ∧
      weightedTraceCost lam auxiliary ≤
        (weightedTraceCost lam
            (frontier (selectedRawSplice A G l r d u n) ∩
              junctionBall p rho) +
          ENNReal.ofReal epsilon) +
        weightedTraceCost lam (junctionSphere p rho) := by
  obtain ⟨sector, horizontal, vertical, N, rho, rCorner, U, modification,
      hN, hpN, hrho, hball, hlocal, hrCorner, hrCornerR, hUsmooth,
      hmodificationClosed, hlocalModify, hmodificationHalf, hexact, hcost⟩ :=
    exists_smoothSelectedRawSpliceCleanCornerRepair
      hlam A G l r d u hA hG hlr hdu hpCorner hpFront hpA hpG hR hepsilon
  let raw := selectedRawSplice A G l r d u n
  let W := junctionBall p rho
  let inner := junctionBall p (rho / 2)
  let collar := N ∩ innerᶜ
  let repaired := spliceIn raw U W
  let auxiliary :=
    (frontier raw ∩ W) ∪ (frontier repaired ∩ modification) ∪
      junctionSphere p rho
  have hrawOpen : IsOpen raw := by
    dsimp only [raw, selectedRawSplice]
    exact isOpen_openSpliceIn _ _ _
  have hinnerClosed : IsClosed inner :=
    isClosed_junctionBall p (rho / 2)
  have hcollarOpen : IsOpen collar := hN.inter hinnerClosed.isOpen_compl
  have hsphereDisjoint :
      Disjoint (junctionSphere p rho) inner := by
    simpa only [inner] using junctionSphere_disjoint_half_junctionBall p hrho
  have hfrontierCollar : frontier W ⊆ collar := by
    intro q hq
    have hqSphere : q ∈ junctionSphere p rho := by
      exact frontier_junctionBall_subset_junctionSphere p rho hq
    have hqW : q ∈ W := by
      exact junctionSphere_subset_junctionBall p rho hqSphere
    have hqN : q ∈ N := hball hqW
    have hqNotInner : q ∉ inner :=
      Set.disjoint_left.1 hsphereDisjoint hqSphere
    exact ⟨hqN, hqNotInner⟩
  have hagreeCollar : raw ∩ collar = U ∩ collar := by
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hqRaw, hqN, hqNotInner⟩
      have hqNotModification : q ∉ modification :=
        fun hqModification => hqNotInner (hmodificationHalf hqModification)
      exact ⟨(hexact q hqN hqNotModification).mpr hqRaw,
        hqN, hqNotInner⟩
    · rintro ⟨hqU, hqN, hqNotInner⟩
      have hqNotModification : q ∉ modification :=
        fun hqModification => hqNotInner (hmodificationHalf hqModification)
      exact ⟨(hexact q hqN hqNotModification).mp hqU,
        hqN, hqNotInner⟩
  have hrepairedOpen : IsOpen repaired := by
    rw [show repaired =
        (U ∩ interior W) ∪ (raw ∩ interior Wᶜ) ∪ (raw ∩ collar) by
      exact spliceIn_eq_open_union_of_agree_near_frontier
        hfrontierCollar hagreeCollar]
    exact ((hUsmooth.isOpen.inter isOpen_interior).union
      (hrawOpen.inter isOpen_interior)).union
        (hrawOpen.inter hcollarOpen)
  have hrepairedModify : repaired ∆ raw ⊆ modification := by
    intro q hq
    by_cases hqW : q ∈ W
    · have hqN : q ∈ N := hball hqW
      by_contra hqModification
      have hqEq := hexact q hqN hqModification
      have hsplice : q ∈ repaired ↔ q ∈ U := by
        simp only [repaired, spliceIn, mem_union, Set.mem_sdiff,
          mem_inter_iff, hqW, not_true_eq_false, and_false, and_true,
          false_or]
      rw [Set.mem_symmDiff] at hq
      rw [hsplice] at hq
      tauto
    · have hsplice : q ∈ repaired ↔ q ∈ raw := by
        simp only [repaired, spliceIn, mem_union, Set.mem_sdiff,
          mem_inter_iff, hqW, not_false_eq_true, and_true, and_false,
          or_false]
      rw [Set.mem_symmDiff] at hq
      tauto
  have hrepairedExterior : ∀ q, q ∉ modification →
      (q ∈ repaired ↔ q ∈ raw) := by
    intro q hqModification
    have hqNotDiff : q ∉ repaired ∆ raw :=
      fun hqDiff => hqModification (hrepairedModify hqDiff)
    simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hqNotDiff
    exact ⟨hqNotDiff.1, hqNotDiff.2⟩
  let localAgreement := N ∩ modificationᶜ
  have hlocalAgreementOpen : IsOpen localAgreement :=
    hN.inter hmodificationClosed.isOpen_compl
  have hrawUAgreement : raw ∩ localAgreement = U ∩ localAgreement := by
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hqRaw, hqN, hqNotModification⟩
      exact ⟨(hexact q hqN hqNotModification).mpr hqRaw,
        hqN, hqNotModification⟩
    · rintro ⟨hqU, hqN, hqNotModification⟩
      exact ⟨(hexact q hqN hqNotModification).mp hqU,
        hqN, hqNotModification⟩
  have hfrontierAgreement :
      frontier raw ∩ localAgreement = frontier U ∩ localAgreement :=
    frontier_inter_eq_of_inter_open_eq hlocalAgreementOpen hrawUAgreement
  have hfrontier : frontier repaired ⊆
      (frontier raw ∩ Wᶜ) ∪ auxiliary := by
    intro q hq
    have hpiece := frontier_spliceIn_subset_piecewise raw U W hq
    rcases hpiece with (hqRaw | hqU) | hqCut
    · exact Or.inl ⟨hqRaw.1, interior_subset hqRaw.2⟩
    · by_cases hqModification : q ∈ modification
      · exact Or.inr <| Or.inl <| Or.inr ⟨hq, hqModification⟩
      · have hqW : q ∈ W := interior_subset hqU.2
        have hqN : q ∈ N := hball hqW
        have hqRawLocal : q ∈ frontier raw ∩ localAgreement := by
          rw [hfrontierAgreement]
          exact ⟨hqU.1, hqN, hqModification⟩
        exact Or.inr <| Or.inl <| Or.inl ⟨hqRawLocal.1, hqW⟩
    · exact Or.inr <| Or.inr <|
        frontier_junctionBall_subset_junctionSphere p rho hqCut.1
  have hcostAuxiliary : weightedTraceCost lam auxiliary ≤
      (weightedTraceCost lam (frontier raw ∩ W) + ENNReal.ofReal epsilon) +
        weightedTraceCost lam (junctionSphere p rho) := by
    calc
      weightedTraceCost lam auxiliary ≤
          (weightedTraceCost lam (frontier raw ∩ W) +
            weightedTraceCost lam (frontier repaired ∩ modification)) +
              weightedTraceCost lam (junctionSphere p rho) := by
        exact (weightedTraceCost_union_le lam _ _).trans
          (add_le_add (weightedTraceCost_union_le lam _ _) le_rfl)
      _ ≤ (weightedTraceCost lam (frontier raw ∩ W) +
            ENNReal.ofReal epsilon) +
              weightedTraceCost lam (junctionSphere p rho) := by
        exact add_le_add (add_le_add le_rfl (by
          have hfrontierLocal :
              frontier repaired ∩ modification ⊆ frontier U ∩ modification := by
            intro q hq
            have hqInner : q ∈ inner := hmodificationHalf hq.2
            have hqInnerDist : dist (planeEuclideanHomeomorph q)
                (planeEuclideanHomeomorph p) ≤ rho / 2 := by
              exact hqInner
            have hqW : q ∈ W := by
              change dist (planeEuclideanHomeomorph q)
                  (planeEuclideanHomeomorph p) ≤ rho
              linarith [hqInnerDist]
            have hlocalInside :
                repaired ∩ interior W = U ∩ interior W := by
              exact spliceIn_inter_interior raw U W
            have hqInterior : q ∈ interior W := by
              let openBall := planeEuclideanHomeomorph ⁻¹'
                Metric.ball (planeEuclideanHomeomorph p) rho
              have hqOpenBall : q ∈ openBall := by
                change dist (planeEuclideanHomeomorph q)
                    (planeEuclideanHomeomorph p) < rho
                linarith [hqInnerDist]
              have hopenBall : IsOpen openBall :=
                planeEuclideanHomeomorph.continuous.isOpen_preimage _ Metric.isOpen_ball
              have hopenBallSubset : openBall ⊆ W := by
                intro z hz
                exact Metric.ball_subset_closedBall hz
              exact interior_maximal hopenBallSubset hopenBall hqOpenBall
            have hfrontierInside :
                frontier repaired ∩ interior W = frontier U ∩ interior W :=
              frontier_inter_eq_of_inter_open_eq isOpen_interior hlocalInside
            have hqU : q ∈ frontier U ∩ interior W := by
              rw [← hfrontierInside]
              exact ⟨hq.1, hqInterior⟩
            exact ⟨hqU.1, hq.2⟩
          exact (weightedTraceCost_mono lam hfrontierLocal).trans hcost.le))
          le_rfl
  exact ⟨rho, repaired, modification, auxiliary, hrho, hrepairedOpen,
    hmodificationClosed, hrepairedModify, hmodificationHalf,
    hrepairedExterior, hfrontier, rfl, hcostAuxiliary⟩

/-- Coordinate cuts chosen after excluding the finitely many vertical
intersection heights make every selected-splice corner clean.  Consequently
the actual graft theorem applies at every corner that lies on the raw splice
frontier; input-boundary corner cases are impossible for these cuts. -/
theorem selectedRawSplice_all_corners_have_openGraftedRepair_of_cornerFreeCuts
    {lam : ℝ} (hlam : 1 < lam)
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    (hA : ∀ n, IsOpen (A n)) (hG : ∀ n, IsOpen (G n))
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    {n : ℕ}
    (hcornerFree : ∀ p ∈ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint),
      p ∉ frontier (A n) ∧ p ∉ frontier (G n)) :
    ∀ p ∈ ({(l n, d n), (l n, u n),
        (r n, d n), (r n, u n)} : Set PlanePoint),
      p ∈ frontier (selectedRawSplice A G l r d u n) →
      ∀ {R epsilon : ℝ}, 0 < R → 0 < epsilon →
        ∃ (rho : ℝ) (repaired modification auxiliary : Set PlanePoint),
          0 < rho ∧ IsOpen repaired ∧ IsClosed modification ∧
          repaired ∆ selectedRawSplice A G l r d u n ⊆ modification ∧
          modification ⊆ junctionBall p (rho / 2) ∧
          (∀ q, q ∉ modification →
            (q ∈ repaired ↔ q ∈ selectedRawSplice A G l r d u n)) ∧
          frontier repaired ⊆
            (frontier (selectedRawSplice A G l r d u n) ∩
              (junctionBall p rho)ᶜ) ∪ auxiliary ∧
          auxiliary =
            (frontier (selectedRawSplice A G l r d u n) ∩
                junctionBall p rho) ∪
              (frontier repaired ∩ modification) ∪ junctionSphere p rho ∧
          weightedTraceCost lam auxiliary ≤
            (weightedTraceCost lam
                (frontier (selectedRawSplice A G l r d u n) ∩
                  junctionBall p rho) +
              ENNReal.ofReal epsilon) +
            weightedTraceCost lam (junctionSphere p rho) := by
  intro p hpCorner hpFront R epsilon hR hepsilon
  exact exists_openGraftedSelectedRawSpliceCleanCornerRepair
    hlam A G l r d u hA hG hlr hdu hpCorner hpFront
      (hcornerFree p hpCorner).1 (hcornerFree p hpCorner).2 hR hepsilon

/-- The coordinate direction of a noncorner rectangular splice face. -/
inductive SpliceCutAxis
  | vertical
  | horizontal

/-- Which coordinate side of an implicit boundary graph is occupied.
`negative` means the defining function increases in the transverse coordinate,
so its negative sublevel occupies the lower/left side; `positive` is the
opposite orientation. -/
inductive SpliceGraphOccupiedSide
  | negative
  | positive
  deriving DecidableEq

/-- The exact defining-function/implicit-graph germ supplied by a regular cut
certificate, including the occupied side detected by the transverse
derivative.  The graph is a genuine global `C∞` representative that agrees
with the source boundary on one fixed neighborhood of the junction. -/
def HasOrientedSmoothBoundaryGraphGermOnSide
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (U : Set PlanePoint) (p : PlanePoint) : Prop :=
  match axis with
  | .vertical =>
      ∃ (g : PlanePoint → ℝ) (φ : ℝ → ℝ),
        ContDiffAt ℝ ∞ g p ∧ fderiv ℝ g p (0, 1) ≠ 0 ∧
        ContDiff ℝ ∞ φ ∧ φ p.1 = p.2 ∧
        (∀ᶠ q in 𝓝 p,
          (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ φ q.1 = q.2)) ∧
        match side with
        | .negative => 0 < fderiv ℝ g p (0, 1)
        | .positive => fderiv ℝ g p (0, 1) < 0
  | .horizontal =>
      ∃ (g : PlanePoint → ℝ) (φ : ℝ → ℝ),
        ContDiffAt ℝ ∞ g p ∧ fderiv ℝ g p (1, 0) ≠ 0 ∧
        ContDiff ℝ ∞ φ ∧ φ p.2 = p.1 ∧
        (∀ᶠ q in 𝓝 p,
          (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ φ q.2 = q.1)) ∧
        match side with
        | .negative => 0 < fderiv ℝ g p (1, 0)
        | .positive => fderiv ℝ g p (1, 0) < 0

private theorem eventually_sublevel_iff_below_graph_of_vertical_fderiv_pos
    {g : PlanePoint → ℝ} {φ : ℝ → ℝ} {p : PlanePoint}
    (hg : ContDiffAt ℝ ∞ g p) (hφ : ContDiff ℝ ∞ φ)
    (hφp : φ p.1 = p.2)
    (hzero : ∀ᶠ q in 𝓝 p, g q = 0 ↔ φ q.1 = q.2)
    (hpos : 0 < fderiv ℝ g p (0, 1)) :
    ∀ᶠ q in 𝓝 p, g q < 0 ↔ q.2 < φ q.1 := by
  have hg1 : ContDiffAt ℝ 1 g p := hg.of_le (by simp)
  have hsmooth : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 1 g q :=
    hg1.eventually (by simp)
  have hderiv : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ g q (0, 1) := by
    have hc : ContinuousAt (fun q => fderiv ℝ g q (0, 1)) p :=
      (hg1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
    exact hc.eventually (Ioi_mem_nhds hpos)
  have hgood : ∀ᶠ q in 𝓝 p,
      ContDiffAt ℝ 1 g q ∧ 0 < fderiv ℝ g q (0, 1) ∧
        (g q = 0 ↔ φ q.1 = q.2) :=
    hsmooth.and (hderiv.and hzero)
  rcases Metric.eventually_nhds_iff.mp hgood with ⟨ε, hε, hgood⟩
  have hhalf : 0 < ε / 2 := by positivity
  have hφTendsto :
      Tendsto (fun q : PlanePoint => φ q.1) (𝓝 p) (𝓝 p.2) := by
    rw [← hφp]
    exact hφ.continuous.continuousAt.comp continuousAt_fst
  have hqClose : ∀ᶠ q : PlanePoint in 𝓝 p, q ∈ ball p (ε / 2) :=
    Metric.ball_mem_nhds p hhalf
  have hφClose :
      ∀ᶠ q : PlanePoint in 𝓝 p, φ q.1 ∈ ball p.2 (ε / 2) :=
    hφTendsto.eventually (Metric.ball_mem_nhds p.2 hhalf)
  filter_upwards [hqClose, hφClose] with q hqClose hφClose
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hqClose
  rw [Metric.mem_ball] at hφClose
  have point_good (y : ℝ) (hy : y ∈ uIcc q.2 (φ q.1)) :
      ContDiffAt ℝ 1 g (q.1, y) ∧
        0 < fderiv ℝ g (q.1, y) (0, 1) ∧
        (g (q.1, y) = 0 ↔ φ q.1 = y) := by
    have hyBall : y ∈ ball p.2 (ε / 2) := by
      rcases Set.mem_uIcc.mp hy with hy | hy
      · exact (convex_ball p.2 (ε / 2)).ordConnected.out
          hqClose.2 hφClose hy
      · exact (convex_ball p.2 (ε / 2)).ordConnected.out
          hφClose hqClose.2 hy
    apply hgood
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · exact hqClose.1.trans (by linarith)
    · rw [Metric.mem_ball] at hyBall
      exact hyBall.trans (by linarith)
  have hcontinuous : ContinuousOn (fun y : ℝ => g (q.1, y))
      (uIcc q.2 (φ q.1)) := by
    intro y hy
    have hyGood := (point_good y hy).1
    exact (hyGood.continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hmono : StrictMonoOn (fun y : ℝ => g (q.1, y))
      (uIcc q.2 (φ q.1)) := by
    apply strictMonoOn_of_deriv_pos (convex_uIcc _ _) hcontinuous
    intro y hy
    have hyMem : y ∈ uIcc q.2 (φ q.1) := interior_subset hy
    have hyGood := point_good y hyMem
    have hline :
        HasDerivAt (fun z : ℝ => ((q.1, z) : PlanePoint)) (0, 1) y :=
      (hasDerivAt_const y q.1).prodMk (hasDerivAt_id y)
    have hcomp := hyGood.1.differentiableAt one_ne_zero |>.hasFDerivAt
      |>.comp_hasDerivAt y hline
    rw [show deriv (fun y : ℝ => g (q.1, y)) y =
      fderiv ℝ g (q.1, y) (0, 1) by
        simpa only [Function.comp_def] using hcomp.deriv]
    exact hyGood.2.1
  have hqMem : q.2 ∈ uIcc q.2 (φ q.1) := left_mem_uIcc
  have hφMem : φ q.1 ∈ uIcc q.2 (φ q.1) := right_mem_uIcc
  have hgraphZero : g (q.1, φ q.1) = 0 :=
    (point_good (φ q.1) hφMem).2.2.mpr rfl
  constructor
  · intro hgq
    change g (q.1, q.2) < 0 at hgq
    by_contra hnot
    have hle : φ q.1 ≤ q.2 := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq, hgraphZero] at hgq
      exact (lt_irrefl 0 hgq)
    · have hinc := hmono hφMem hqMem hlt
      change g (q.1, φ q.1) < g (q.1, q.2) at hinc
      rw [hgraphZero] at hinc
      exact (not_lt_of_ge hinc.le) hgq
  · intro hlt
    have hinc := hmono hqMem hφMem hlt
    change g (q.1, q.2) < g (q.1, φ q.1) at hinc
    change g (q.1, q.2) < 0
    rwa [hgraphZero] at hinc

private theorem eventually_sublevel_iff_above_graph_of_vertical_fderiv_neg
    {g : PlanePoint → ℝ} {φ : ℝ → ℝ} {p : PlanePoint}
    (hg : ContDiffAt ℝ ∞ g p) (hφ : ContDiff ℝ ∞ φ)
    (hφp : φ p.1 = p.2)
    (hzero : ∀ᶠ q in 𝓝 p, g q = 0 ↔ φ q.1 = q.2)
    (hneg : fderiv ℝ g p (0, 1) < 0) :
    ∀ᶠ q in 𝓝 p, g q < 0 ↔ φ q.1 < q.2 := by
  have hnegSmooth : ContDiffAt ℝ ∞ (fun q => -g q) p := hg.neg
  have hnegZero :
      ∀ᶠ q in 𝓝 p, -g q = 0 ↔ φ q.1 = q.2 := by
    filter_upwards [hzero] with q hq
    simpa only [neg_eq_zero] using hq
  have hnegDeriv :
      fderiv ℝ (fun q => -g q) p (0, 1) =
        -fderiv ℝ g p (0, 1) := by
    have hfd := hg.differentiableAt (by simp) |>.hasFDerivAt.neg
    have heq := congrArg (fun D : PlanePoint →L[ℝ] ℝ => D (0, 1))
      hfd.fderiv
    change fderiv ℝ (-g) p (0, 1) = -fderiv ℝ g p (0, 1)
    simpa only [neg_apply] using heq
  have hreverse :
      ∀ᶠ q in 𝓝 p, -g q < 0 ↔ q.2 < φ q.1 := by
    apply eventually_sublevel_iff_below_graph_of_vertical_fderiv_pos
      hnegSmooth hφ hφp hnegZero
    rw [hnegDeriv]
    linarith
  filter_upwards [hreverse, hzero] with q hrev hz
  constructor
  · intro hgq
    by_contra hnot
    have hle : q.2 ≤ φ q.1 := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hgzero := hz.mpr heq.symm
      linarith
    · have hpositive : 0 < g q := by
        have := hrev.mpr hlt
        simpa only [neg_lt_zero] using this
      linarith
  · intro hφq
    by_contra hnot
    have hnonneg : 0 ≤ g q := le_of_not_gt hnot
    rcases hnonneg.eq_or_lt with heq | hpos
    · have hgraph := hz.mp heq.symm
      linarith
    · have hbelow : q.2 < φ q.1 := hrev.mp (by
        simpa only [neg_lt_zero] using hpos)
      linarith

/-- A vertical oriented defining-function germ is exactly the corresponding
occupied graph side on one neighborhood of its base point. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.exists_vertical_graphDomain_germ
    {side : SpliceGraphOccupiedSide} {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .vertical side U p) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ φ p.1 = p.2 ∧
      match side with
      | .negative => ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < φ q.1
      | .positive => ∀ᶠ q in 𝓝 p, q ∈ U ↔ φ q.1 < q.2 := by
  cases side with
  | negative =>
      rcases germ with
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hpositive⟩
      have hgraph :=
        eventually_sublevel_iff_below_graph_of_vertical_fderiv_pos
          hg hφ hφp (hlocal.mono fun q hq => hq.2) hpositive
      refine ⟨φ, hφ, hφp, ?_⟩
      filter_upwards [hlocal, hgraph] with q hq hqgraph
      exact hq.1.trans hqgraph
  | positive =>
      rcases germ with
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hnegative⟩
      have hgraph :=
        eventually_sublevel_iff_above_graph_of_vertical_fderiv_neg
          hg hφ hφp (hlocal.mono fun q hq => hq.2) hnegative
      refine ⟨φ, hφ, hφp, ?_⟩
      filter_upwards [hlocal, hgraph] with q hq hqgraph
      exact hq.1.trans hqgraph

/-- A horizontal oriented defining-function germ is exactly the corresponding
occupied graph side on one neighborhood of its base point. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.exists_horizontal_graphDomain_germ
    {side : SpliceGraphOccupiedSide} {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .horizontal side U p) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ φ p.2 = p.1 ∧
      match side with
      | .negative => ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.1 < φ q.2
      | .positive => ∀ᶠ q in 𝓝 p, q ∈ U ↔ φ q.2 < q.1 := by
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  let u : PlanePoint := (p.2, p.1)
  let Us : Set PlanePoint := e ⁻¹' U
  rcases germ with
    ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hside⟩
  let gs : PlanePoint → ℝ := g ∘ e
  have hgs : ContDiffAt ℝ ∞ gs u := by
    simpa [gs, e, u] using hg.comp u e.contDiff.contDiffAt
  have hgsFDeriv :
      HasFDerivAt gs
        (fderiv ℝ g p ∘L (e : PlanePoint →L[ℝ] PlanePoint)) u := by
    have hgfd := hg.differentiableAt (by simp) |>.hasFDerivAt
    simpa [gs, e, u] using hgfd.comp u e.hasFDerivAt
  have htransverseSwap :
      fderiv ℝ gs u (0, 1) = fderiv ℝ g p (1, 0) := by
    rw [hgsFDeriv.fderiv]
    simp [e, ContinuousLinearMap.comp_apply]
  have hlocalSwap :
      ∀ᶠ q in 𝓝 u,
        (q ∈ Us ↔ gs q < 0) ∧ (gs q = 0 ↔ φ q.1 = q.2) := by
    have heTendsto : Tendsto e (𝓝 u) (𝓝 p) := by
      have heup : e u = p := by
        apply Prod.ext <;> rfl
      rw [← heup]
      exact e.continuousAt
    have hs := heTendsto.eventually hlocal
    simpa [Us, gs, e, u] using hs
  have germSwap :
      HasOrientedSmoothBoundaryGraphGermOnSide .vertical side Us u := by
    refine ⟨gs, φ, hgs, ?_, hφ, by simpa only [u] using hφp,
      hlocalSwap, ?_⟩
    · rw [htransverseSwap]
      exact htransverse
    · rw [htransverseSwap]
      exact hside
  obtain ⟨ψ, hψ, hψu, hψgerm⟩ :=
    germSwap.exists_vertical_graphDomain_germ
  refine ⟨ψ, hψ, by simpa only [u] using hψu, ?_⟩
  have heTendsto : Tendsto e (𝓝 p) (𝓝 u) := by
    have hepu : e p = u := by
      apply Prod.ext <;> rfl
    rw [← hepu]
    exact e.continuousAt
  cases side with
  | negative =>
      have hs := heTendsto.eventually hψgerm
      simpa [Us, e, u] using hs
  | positive =>
      have hs := heTendsto.eventually hψgerm
      simpa [Us, e, u] using hs

/-- An oriented smooth boundary graph germ determines its exact occupied graph
side on one fixed neighborhood, in either coordinate orientation. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.exists_eventually_occupiedGraphDomain
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
      match axis with
      | .vertical =>
          φ p.1 = p.2 ∧
            match side with
            | .negative => ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < φ q.1
            | .positive => ∀ᶠ q in 𝓝 p, q ∈ U ↔ φ q.1 < q.2
      | .horizontal =>
          φ p.2 = p.1 ∧
            match side with
            | .negative => ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.1 < φ q.2
            | .positive => ∀ᶠ q in 𝓝 p, q ∈ U ↔ φ q.2 < q.1 := by
  cases axis with
  | vertical =>
      simpa using germ.exists_vertical_graphDomain_germ
  | horizontal =>
      simpa using germ.exists_horizontal_graphDomain_germ

/-- An oriented boundary graph germ with its occupied side existentially
hidden. -/
def HasOrientedSmoothBoundaryGraphGerm
    (axis : SpliceCutAxis) (U : Set PlanePoint) (p : PlanePoint) : Prop :=
  ∃ side, HasOrientedSmoothBoundaryGraphGermOnSide axis side U p

/-- Swapping the two splice inputs and complementing the window leaves the
canonical open splice unchanged. -/
theorem openSpliceIn_swap_compl
    (A G W : Set PlanePoint) :
    openSpliceIn A G W = openSpliceIn G A Wᶜ := by
  unfold openSpliceIn
  congr 1
  ext q
  by_cases hqW : q ∈ W <;> simp [spliceIn, hqW]

/-- A `first` oriented input germ has an exact local curvilinear-sector model
for the canonical open splice.  Since the second input has no boundary at the
junction, its local sector is exactly `univ` or `∅`. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.exists_first_openSplice_local_sector
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {A G W : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side A p)
    (hG : IsOpen G) (hpG : p ∉ frontier G) :
    ∃ (g : PlanePoint → ℝ) (N : Set PlanePoint),
      IsOpen N ∧ p ∈ N ∧
      ((p ∈ G ∧
          openSpliceIn A G W ∩ N =
            openSpliceIn {q | g q < 0} univ W ∩ N) ∨
       (p ∉ G ∧
          openSpliceIn A G W ∩ N =
            openSpliceIn {q | g q < 0} ∅ W ∩ N)) := by
  classical
  obtain ⟨g, hAgerm⟩ :
      ∃ g : PlanePoint → ℝ, ∀ᶠ q in 𝓝 p, (q ∈ A ↔ g q < 0) := by
    cases axis with
    | vertical =>
        rcases germ with
          ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hside⟩
        exact ⟨g, hlocal.mono fun q hq => hq.1⟩
    | horizontal =>
        rcases germ with
          ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hside⟩
        exact ⟨g, hlocal.mono fun q hq => hq.1⟩
  have localize
      (H : Set PlanePoint)
      (hGgerm : ∀ᶠ q in 𝓝 p, (q ∈ G ↔ q ∈ H)) :
      ∃ N : Set PlanePoint, IsOpen N ∧ p ∈ N ∧
        openSpliceIn A G W ∩ N =
          openSpliceIn {q | g q < 0} H W ∩ N := by
    have hlocal : ∀ᶠ q in 𝓝 p,
        (q ∈ A ↔ q ∈ {z : PlanePoint | g z < 0}) ∧
          (q ∈ G ↔ q ∈ H) := hAgerm.and hGgerm
    rcases _root_.mem_nhds_iff.mp hlocal with
      ⟨N, hNsub, hNopen, hpN⟩
    refine ⟨N, hNopen, hpN, ?_⟩
    change interior (spliceIn A G W) ∩ N =
      interior (spliceIn {q | g q < 0} H W) ∩ N
    have hraw : spliceIn A G W ∩ N =
        spliceIn {q | g q < 0} H W ∩ N := by
      ext q
      by_cases hqN : q ∈ N
      · have hq := hNsub hqN
        have hqA : q ∈ A ↔ g q < 0 := hq.1
        simp only [spliceIn, mem_inter_iff, mem_union, Set.mem_sdiff,
          Set.mem_ofPred_eq, hqN, and_true]
        rw [hqA, hq.2]
      · simp only [mem_inter_iff, hqN, and_false]
    calc
      interior (spliceIn A G W) ∩ N =
          interior (spliceIn A G W) ∩ interior N := by
            rw [interior_eq_iff_isOpen.mpr hNopen]
      _ = interior (spliceIn A G W ∩ N) := interior_inter.symm
      _ = interior (spliceIn {q | g q < 0} H W ∩ N) :=
        congrArg interior hraw
      _ = interior (spliceIn {q | g q < 0} H W) ∩ interior N :=
        interior_inter
      _ = interior (spliceIn {q | g q < 0} H W) ∩ N := by
        rw [interior_eq_iff_isOpen.mpr hNopen]
  by_cases hpGin : p ∈ G
  · have hGgerm : ∀ᶠ q in 𝓝 p,
        (q ∈ G ↔ q ∈ (univ : Set PlanePoint)) := by
      filter_upwards [hG.mem_nhds hpGin] with q hqG
      exact ⟨fun _ => mem_univ q, fun _ => hqG⟩
    obtain ⟨N, hNopen, hpN, heq⟩ := localize univ hGgerm
    exact ⟨g, N, hNopen, hpN, Or.inl ⟨hpGin, heq⟩⟩
  · have hpRegion : p ∈ interior G ∪ interior Gᶜ := by
      have hp' : p ∈ (frontier G)ᶜ := hpG
      rwa [compl_frontier_eq_union_interior] at hp'
    have hpGc : p ∈ interior Gᶜ := hpRegion.resolve_left
      (fun hpInt => hpGin (interior_subset hpInt))
    have hGgerm : ∀ᶠ q in 𝓝 p,
        (q ∈ G ↔ q ∈ (∅ : Set PlanePoint)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_interior hpGc] with q hqGc
      constructor
      · exact fun hqG => ((interior_subset hqGc) hqG).elim
      · exact fun hqEmpty => hqEmpty.elim
    obtain ⟨N, hNopen, hpN, heq⟩ := localize ∅ hGgerm
    exact ⟨g, N, hNopen, hpN, Or.inr ⟨hpGin, heq⟩⟩

/-- A `second` oriented input germ has an exact local curvilinear-sector
model for the canonical open splice.  The first input is locally exactly
`univ` or `∅`. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.exists_second_openSplice_local_sector
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {A G W : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side G p)
    (hA : IsOpen A) (hpA : p ∉ frontier A) :
    ∃ (g : PlanePoint → ℝ) (N : Set PlanePoint),
      IsOpen N ∧ p ∈ N ∧
      ((p ∈ A ∧
          openSpliceIn A G W ∩ N =
            openSpliceIn univ {q | g q < 0} W ∩ N) ∨
       (p ∉ A ∧
          openSpliceIn A G W ∩ N =
            openSpliceIn ∅ {q | g q < 0} W ∩ N)) := by
  obtain ⟨g, N, hNopen, hpN, hcases⟩ :=
    germ.exists_first_openSplice_local_sector
      (A := G) (G := A) (W := Wᶜ) hA hpA
  refine ⟨g, N, hNopen, hpN, ?_⟩
  rcases hcases with ⟨hpAin, heq⟩ | ⟨hpAout, heq⟩
  · refine Or.inl ⟨hpAin, ?_⟩
    calc
      openSpliceIn A G W ∩ N =
          openSpliceIn G A Wᶜ ∩ N := by
            rw [openSpliceIn_swap_compl]
      _ = openSpliceIn {q | g q < 0} univ Wᶜ ∩ N := heq
      _ = openSpliceIn univ {q | g q < 0} W ∩ N := by
        rw [openSpliceIn_swap_compl]
        simp only [compl_compl]
  · refine Or.inr ⟨hpAout, ?_⟩
    calc
      openSpliceIn A G W ∩ N =
          openSpliceIn G A Wᶜ ∩ N := by
            rw [openSpliceIn_swap_compl]
      _ = openSpliceIn {q | g q < 0} ∅ Wᶜ ∩ N := heq
      _ = openSpliceIn ∅ {q | g q < 0} W ∩ N := by
        rw [openSpliceIn_swap_compl]
        simp only [compl_compl]

/-- Exhaustive oriented input-boundary incidence at a noncorner splice
junction.  The double-input constructors distinguish equal occupied sides
from opposite occupied sides without assuming mutual transversality. -/
inductive SelectedSpliceInputGermCase
    (axis : SpliceCutAxis) (A G : Set PlanePoint) (p : PlanePoint) : Prop
  | first
      (sideA : SpliceGraphOccupiedSide)
      (hA : p ∈ frontier A) (hG : p ∉ frontier G)
      (germA : HasOrientedSmoothBoundaryGraphGermOnSide axis sideA A p)
  | second
      (sideG : SpliceGraphOccupiedSide)
      (hA : p ∉ frontier A) (hG : p ∈ frontier G)
      (germG : HasOrientedSmoothBoundaryGraphGermOnSide axis sideG G p)
  | bothSame
      (side : SpliceGraphOccupiedSide)
      (hA : p ∈ frontier A) (hG : p ∈ frontier G)
      (germA : HasOrientedSmoothBoundaryGraphGermOnSide axis side A p)
      (germG : HasOrientedSmoothBoundaryGraphGermOnSide axis side G p)
  | bothOpposite
      (sideA sideG : SpliceGraphOccupiedSide)
      (hA : p ∈ frontier A) (hG : p ∈ frontier G)
      (differentSides : sideA ≠ sideG)
      (germA : HasOrientedSmoothBoundaryGraphGermOnSide axis sideA A p)
      (germG : HasOrientedSmoothBoundaryGraphGermOnSide axis sideG G p)

/-- Complete local data forced at every noncorner junction of an internally
selected rectangular splice: one oriented smooth cut half-plane and the
exhaustive one- or two-input regular graph germs. -/
structure OpenSpliceNoncornerRegularGermData
    (A G : Set PlanePoint) (l r d u : ℝ) (p : PlanePoint) where
  axis : SpliceCutAxis
  cutNeighborhood : Set PlanePoint
  cutInside : Set PlanePoint
  cutOutside : Set PlanePoint
  raw_frontier :
    p ∈ frontier (openSpliceIn A G (closedCutRectangle l r d u))
  cutNeighborhood_open : IsOpen cutNeighborhood
  point_mem_cutNeighborhood : p ∈ cutNeighborhood
  cutInside_smooth : IsSmoothDomain cutInside
  cutOutside_smooth : IsSmoothDomain cutOutside
  window_inside_local :
    interior (closedCutRectangle l r d u) ∩ cutNeighborhood =
      cutInside ∩ cutNeighborhood
  window_outside_local :
    interior ((closedCutRectangle l r d u)ᶜ) ∩ cutNeighborhood =
      cutOutside ∩ cutNeighborhood
  inputGerms : SelectedSpliceInputGermCase axis A G p

/-- The four unchanged regular-cut certificates exhaust every noncorner
junction of the actual open splice.  The conclusion separates single-input
curvilinear germs from double-input switches and classifies the double-input
occupied-side relation as same or opposite without deriving mutual
transversality. -/
theorem exists_openSplice_noncorner_regularGermData
    {A G : Set PlanePoint}
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ l r d u : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : l ∈ Ioo a₀ a₁) (hr : r ∈ Ioo b₀ b₁)
    (hd : d ∈ Ioo c₀ c₁) (hu : u ∈ Ioo d₀ d₁)
    (hL : IsRegularFiniteVerticalSpliceCut A G
      (closedCutRectangle a₀ a₁ c₀ d₁) l)
    (hR : IsRegularFiniteVerticalSpliceCut A G
      (closedCutRectangle b₀ b₁ c₀ d₁) r)
    (hD : IsRegularFiniteHorizontalSpliceCut A G
      (closedCutRectangle a₀ b₁ c₀ c₁) d)
    (hU : IsRegularFiniteHorizontalSpliceCut A G
      (closedCutRectangle a₀ b₁ d₀ d₁) u)
    {p : PlanePoint}
    (hpJ : p ∈ spliceJunctionSet A G l r d u)
    (hpCorner : p ∉ ({(l, d), (l, u), (r, d), (r, u)} :
      Set PlanePoint))
    (hpFront :
      p ∈ frontier (openSpliceIn A G (closedCutRectangle l r d u))) :
    Nonempty (OpenSpliceNoncornerRegularGermData A G l r d u p) := by
  have hlr : l < r := hl.2.trans (hab.trans hr.1)
  have hdu : d < u := hd.2.trans (hcd.trans hu.1)
  have hpCross :
      p ∈ (frontier A ∪ frontier G) ∩
        frontier (closedCutRectangle l r d u) :=
    Or.resolve_right hpJ hpCorner
  have hpInputs : p ∈ frontier A ∪ frontier G := hpCross.1
  have hpWindowFrontier :
      p ∈ frontier (closedCutRectangle l r d u) := hpCross.2
  have hpWindow : p ∈ closedCutRectangle l r d u :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset hpWindowFrontier
  obtain ⟨V, inside, outside, hV, hpV, hinsideSmooth, houtsideSmooth,
      hinside, houtside⟩ :=
    exists_local_halfplane_models_closedCutRectangle
      hlr hdu hpWindowFrontier hpCorner
  have verticalInputCase
      (K : Set PlanePoint) (x : ℝ)
      (hregA : IsVerticalRegularBoundaryValue A K x)
      (hregG : IsVerticalRegularBoundaryValue G K x)
      (hpK : p ∈ K) (hpLine : p ∈ verticalLine x) :
      SelectedSpliceInputGermCase .vertical A G p := by
    have orientedGerm
        (U : Set PlanePoint)
        (hreg : IsVerticalRegularBoundaryValue U K x)
        (hpU : p ∈ frontier U) :
        ∃ side, HasOrientedSmoothBoundaryGraphGermOnSide .vertical side U p := by
      obtain ⟨g, φ, hg, htransverse, hφ, hφp, hlocal⟩ :=
        local_oriented_smooth_graph_of_vertical_regular
          hreg ⟨⟨hpU, hpK⟩, hpLine⟩
      rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
      · exact ⟨.positive, g, φ, hg, htransverse, hφ, hφp, hlocal, hnegative⟩
      · exact ⟨.negative, g, φ, hg, htransverse, hφ, hφp, hlocal, hpositive⟩
    rcases hpInputs with hpA | hpG
    · by_cases hpG' : p ∈ frontier G
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA
        obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG'
        by_cases hsides : sideA = sideG
        · subst sideG
          exact .bothSame sideA hpA hpG' germA germG
        · exact .bothOpposite sideA sideG hpA hpG' hsides germA germG
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA
        exact .first sideA hpA hpG' germA
    · by_cases hpA' : p ∈ frontier A
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA'
        obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG
        by_cases hsides : sideA = sideG
        · subst sideG
          exact .bothSame sideA hpA' hpG germA germG
        · exact .bothOpposite sideA sideG hpA' hpG hsides germA germG
      · obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG
        exact .second sideG hpA' hpG germG
  have horizontalInputCase
      (K : Set PlanePoint) (y : ℝ)
      (hregA : IsHorizontalRegularBoundaryValue A K y)
      (hregG : IsHorizontalRegularBoundaryValue G K y)
      (hpK : p ∈ K) (hpLine : p ∈ horizontalLine y) :
      SelectedSpliceInputGermCase .horizontal A G p := by
    have orientedGerm
        (U : Set PlanePoint)
        (hreg : IsHorizontalRegularBoundaryValue U K y)
        (hpU : p ∈ frontier U) :
        ∃ side, HasOrientedSmoothBoundaryGraphGermOnSide .horizontal side U p := by
      obtain ⟨g, φ, hg, htransverse, hφ, hφp, hlocal⟩ :=
        local_oriented_smooth_graph_of_horizontal_regular
          hreg ⟨⟨hpU, hpK⟩, hpLine⟩
      rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
      · exact ⟨.positive, g, φ, hg, htransverse, hφ, hφp, hlocal, hnegative⟩
      · exact ⟨.negative, g, φ, hg, htransverse, hφ, hφp, hlocal, hpositive⟩
    rcases hpInputs with hpA | hpG
    · by_cases hpG' : p ∈ frontier G
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA
        obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG'
        by_cases hsides : sideA = sideG
        · subst sideG
          exact .bothSame sideA hpA hpG' germA germG
        · exact .bothOpposite sideA sideG hpA hpG' hsides germA germG
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA
        exact .first sideA hpA hpG' germA
    · by_cases hpA' : p ∈ frontier A
      · obtain ⟨sideA, germA⟩ := orientedGerm A hregA hpA'
        obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG
        by_cases hsides : sideA = sideG
        · subst sideG
          exact .bothSame sideA hpA' hpG germA germG
        · exact .bothOpposite sideA sideG hpA' hpG hsides germA germG
      · obtain ⟨sideG, germG⟩ := orientedGerm G hregG hpG
        exact .second sideG hpA' hpG germG
  have hfaces :=
    frontier_closedCutRectangle_subset_lines hlr hdu hpWindowFrontier
  rcases hfaces with ((hpLeft | hpRight) | hpLower) | hpUpper
  · have hpX : p.1 = l := hpLeft
    have hpK : p ∈ closedCutRectangle a₀ a₁ c₀ d₁ := by
      exact ⟨⟨by simpa only [hpX] using hl.1.le,
          by simpa only [hpX] using hl.2.le⟩,
        ⟨(hd.1.trans_le hpWindow.2.1).le,
          hpWindow.2.2.trans (hu.2.le)⟩⟩
    exact ⟨{
      axis := .vertical
      cutNeighborhood := V
      cutInside := inside
      cutOutside := outside
      raw_frontier := hpFront
      cutNeighborhood_open := hV
      point_mem_cutNeighborhood := hpV
      cutInside_smooth := hinsideSmooth
      cutOutside_smooth := houtsideSmooth
      window_inside_local := hinside
      window_outside_local := houtside
      inputGerms := verticalInputCase _ _ hL.1 hL.2.1 hpK hpLeft }⟩
  · have hpX : p.1 = r := hpRight
    have hpK : p ∈ closedCutRectangle b₀ b₁ c₀ d₁ := by
      exact ⟨⟨by simpa only [hpX] using hr.1.le,
          by simpa only [hpX] using hr.2.le⟩,
        ⟨(hd.1.trans_le hpWindow.2.1).le,
          hpWindow.2.2.trans (hu.2.le)⟩⟩
    exact ⟨{
      axis := .vertical
      cutNeighborhood := V
      cutInside := inside
      cutOutside := outside
      raw_frontier := hpFront
      cutNeighborhood_open := hV
      point_mem_cutNeighborhood := hpV
      cutInside_smooth := hinsideSmooth
      cutOutside_smooth := houtsideSmooth
      window_inside_local := hinside
      window_outside_local := houtside
      inputGerms := verticalInputCase _ _ hR.1 hR.2.1 hpK hpRight }⟩
  · have hpY : p.2 = d := hpLower
    have hpK : p ∈ closedCutRectangle a₀ b₁ c₀ c₁ := by
      exact ⟨⟨(hl.1.trans_le hpWindow.1.1).le,
          hpWindow.1.2.trans (hr.2.le)⟩,
        ⟨by simpa only [hpY] using hd.1.le,
          by simpa only [hpY] using hd.2.le⟩⟩
    exact ⟨{
      axis := .horizontal
      cutNeighborhood := V
      cutInside := inside
      cutOutside := outside
      raw_frontier := hpFront
      cutNeighborhood_open := hV
      point_mem_cutNeighborhood := hpV
      cutInside_smooth := hinsideSmooth
      cutOutside_smooth := houtsideSmooth
      window_inside_local := hinside
      window_outside_local := houtside
      inputGerms := horizontalInputCase _ _ hD.1 hD.2.1 hpK hpLower }⟩
  · have hpY : p.2 = u := hpUpper
    have hpK : p ∈ closedCutRectangle a₀ b₁ d₀ d₁ := by
      exact ⟨⟨(hl.1.trans_le hpWindow.1.1).le,
          hpWindow.1.2.trans (hr.2.le)⟩,
        ⟨by simpa only [hpY] using hu.1.le,
          by simpa only [hpY] using hu.2.le⟩⟩
    exact ⟨{
      axis := .horizontal
      cutNeighborhood := V
      cutInside := inside
      cutOutside := outside
      raw_frontier := hpFront
      cutNeighborhood_open := hV
      point_mem_cutNeighborhood := hpV
      cutInside_smooth := hinsideSmooth
      cutOutside_smooth := houtsideSmooth
      window_inside_local := hinside
      window_outside_local := houtside
      inputGerms := horizontalInputCase _ _ hU.1 hU.2.1 hpK hpUpper }⟩

/-- Sequence-level specialization for the literal `selectedRawSplice` and
`selectedSpliceJunctions` produced by the finite-cost selector. -/
theorem exists_selectedRawSplice_noncorner_regularGermData
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : ∀ n, l n ∈ Ioo a₀ a₁) (hr : ∀ n, r n ∈ Ioo b₀ b₁)
    (hd : ∀ n, d n ∈ Ioo c₀ c₁) (hu : ∀ n, u n ∈ Ioo d₀ d₁)
    (hL : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ a₁ c₀ d₁) (l n))
    (hR : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle b₀ b₁ c₀ d₁) (r n))
    (hD : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ c₀ c₁) (d n))
    (hU : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ d₀ d₁) (u n))
    {n : ℕ} {p : PlanePoint}
    (hpJ : p ∈ selectedSpliceJunctions A G l r d u n)
    (hpCorner : p ∉ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint))
    (hpFront : p ∈ frontier (selectedRawSplice A G l r d u n)) :
    Nonempty
      (OpenSpliceNoncornerRegularGermData
        (A n) (G n) (l n) (r n) (d n) (u n) p) := by
  exact exists_openSplice_noncorner_regularGermData
    hab hcd (hl n) (hr n) (hd n) (hu n)
      (hL n) (hR n) (hD n) (hU n)
      (by simpa only [selectedSpliceJunctions] using hpJ)
      hpCorner
      (by simpa only [selectedRawSplice] using hpFront)
end CMVRelaxation.FiniteJunctionRepair
