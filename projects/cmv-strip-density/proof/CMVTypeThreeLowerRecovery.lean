/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSharpRecovery
import TypeThreeAssembly

/-!
# Lower-contact recovery for type-(iii) assemblies

This module starts the branch-complete recovery at the semicircular transition.
The target is the literal closed radius-two disk centered at `(0, 1)`; its
approximant is the corresponding open disk, not the closed carrier itself.
-/

open Set Filter MeasureTheory
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation.TypeThreeRecovery

/-- Squared horizontal width of the radius-two disk centered at `(0, 1)`. -/
def semicircularDiskQ (y : ℝ) : ℝ :=
  4 - (y - 1) ^ 2

/-- The smooth open radius-two disk at its actual type-(iii) placement. -/
def semicircularOpenDisk : Set PlanePoint :=
  squaredWidthDomain semicircularDiskQ

/-- The literal closed target represented by the semicircular assembly. -/
def semicircularClosedDisk : Set PlanePoint :=
  {p | p.1 ^ 2 ≤ semicircularDiskQ p.2}

@[simp] theorem mem_semicircularOpenDisk (p : PlanePoint) :
    p ∈ semicircularOpenDisk ↔ p.1 ^ 2 + (p.2 - 1) ^ 2 < 4 := by
  change p.1 ^ 2 < 4 - (p.2 - 1) ^ 2 ↔ _
  constructor <;> intro h <;> linarith

@[simp] theorem mem_semicircularClosedDisk (p : PlanePoint) :
    p ∈ semicircularClosedDisk ↔ p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4 := by
  change p.1 ^ 2 ≤ 4 - (p.2 - 1) ^ 2 ↔ _
  constructor <;> intro h <;> linarith

/-- The approximating disk is open and has one global regular defining
function, including at its top and bottom poles. -/
theorem isSmoothDomain_semicircularOpenDisk :
    IsSmoothDomain semicircularOpenDisk := by
  apply isSmoothDomain_squaredWidth
  · unfold semicircularDiskQ
    fun_prop
  · intro y hy
    have hderiv :
        HasDerivAt semicircularDiskQ (-2 * (y - 1)) y := by
      have hraw := (hasDerivAt_const y 4).sub
        (((hasDerivAt_id y).sub_const 1).pow 2)
      simpa [semicircularDiskQ, Pi.sub_apply] using! hraw
    rw [hderiv.deriv]
    intro hzero
    unfold semicircularDiskQ at hy
    nlinarith

/-- The open/closed discrepancy is contained in the circle and hence has
zero planar volume. -/
theorem characteristicDistance_semicircularOpen_closed :
    characteristicDistance semicircularOpenDisk semicircularClosedDisk = 0 := by
  have hcircle :
      volume {p : PlanePoint | p.1 ^ 2 = semicircularDiskQ p.2} = 0 :=
    FrozenCanonicalCap.volume_squaredWidthBoundary semicircularDiskQ (by
      unfold semicircularDiskQ
      fun_prop)
  unfold characteristicDistance
  apply le_antisymm
  · calc
      volume (semicircularOpenDisk ∆ semicircularClosedDisk) ≤
          volume {p : PlanePoint | p.1 ^ 2 = semicircularDiskQ p.2} := by
        apply measure_mono
        intro p hp
        simp only [Set.mem_symmDiff] at hp
        rcases hp with hp | hp
        · exfalso
          apply hp.2
          change p.1 ^ 2 ≤ semicircularDiskQ p.2
          exact hp.1.le
        · change p.1 ^ 2 = semicircularDiskQ p.2
          exact le_antisymm hp.1 (le_of_not_gt hp.2)
      _ = 0 := hcircle
  · exact bot_le

/-- Constant smooth recovery of the placed open disk. -/
def semicircularDiskConstantSequence : SmoothSequence where
  carrier _ := semicircularOpenDisk
  smooth _ := isSmoothDomain_semicircularOpenDisk

/-- The constant open-disk sequence converges to the literal closed disk, using
only the null circle bridge between the two representatives. -/
theorem semicircularDiskConstantSequence_converges_closed :
    semicircularDiskConstantSequence.ConvergesTo semicircularClosedDisk := by
  unfold SmoothSequence.ConvergesTo
  simp [semicircularDiskConstantSequence,
    characteristicDistance_semicircularOpen_closed]

/-- At `h = 1/2`, the complete closed type-(iii) carrier is exactly the
radius-two disk centered at `(0, 1)`. -/
theorem carrier_eq_semicircularClosedDisk
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h = 1 / 2) :
    a.carrier = semicircularClosedDisk := by
  have hR : a.radius = 2 := by
    rw [TypeThreeAssembly.radius, hh]
    norm_num
  have hW : a.sideHalfWidth = 0 :=
    a.sideHalfWidth_eq_zero_iff.mpr hh
  have hL : a.leftCenter = (0, 1) := by
    simp [TypeThreeAssembly.leftCenter, hW, hR]
    norm_num
  have hRt : a.rightCenter = (0, 1) := by
    simp [TypeThreeAssembly.rightCenter, hW, hR]
    norm_num
  have hU : a.upperCenter = (0, 1) := by
    rw [TypeThreeAssembly.upperCenter, hR,
      a.outerAngle_semicircular hh, Real.cos_pi_div_two]
    norm_num
  have hrect (p : PlanePoint) :
      p ∈ a.rectangleCarrier ↔
        ((0 : ℝ) ≤ p.1 ∧ p.1 ≤ 0) ∧ (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 := by
    simp only [TypeThreeAssembly.rectangleCarrier, Set.mem_inter_iff,
      Set.mem_ofPred_eq, hW, neg_zero]
  have hleft (p : PlanePoint) :
      p ∈ a.leftSegmentCarrier ↔
        p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4 ∧ p.1 ≤ 0 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 := by
    simp only [TypeThreeAssembly.leftSegmentCarrier, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    rw [hL, hR]
    norm_num
  have hright (p : PlanePoint) :
      p ∈ a.rightSegmentCarrier ↔
        p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4 ∧ 0 ≤ p.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 := by
    simp only [TypeThreeAssembly.rightSegmentCarrier, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    rw [hRt, hR]
    norm_num
  have hcap (p : PlanePoint) :
      p ∈ a.outerCap.carrier ↔
        p.1 ^ 2 + (p.2 - 1) ^ 2 ≤ 4 ∧ 1 ≤ p.2 := by
    simp only [OneSidedCircularCap.carrier,
      OneSidedCircularCap.radiusSquaredAt]
    rw [a.outerCap_center, a.outerCap_radius, hU, hR]
    norm_num [TypeThreeAssembly.outerCap]
  ext p
  simp only [TypeThreeAssembly.carrier, TypeThreeAssembly.coreCarrier,
    Set.mem_union]
  rw [hrect p, hleft p, hright p, hcap p,
    mem_semicircularClosedDisk]
  constructor
  · rintro (((hrect' | hleft') | hright') | hcap')
    · rcases hrect' with ⟨hx, hy⟩
      have hxeq : p.1 = 0 := le_antisymm hx.2 hx.1
      rw [hxeq]
      nlinarith [sq_nonneg (p.2 - 1)]
    · exact hleft'.1
    · exact hright'.1
    · exact hcap'.1
  · intro hp
    by_cases hy : 1 ≤ p.2
    · exact Or.inr ⟨hp, hy⟩
    · have hyUpper : p.2 ≤ 1 := le_of_not_ge hy
      have hyLower : (-1 : ℝ) ≤ p.2 := by
        nlinarith [sq_nonneg p.1]
      by_cases hx : p.1 ≤ 0
      · exact Or.inl (Or.inl (Or.inr
          ⟨hp, hx, hyLower, hyUpper⟩))
      · exact Or.inl (Or.inr
          ⟨hp, le_of_not_ge hx, hyLower, hyUpper⟩)

/-- The disk branch is recovered at the actual vertical placement.  No vertical
translation invariance of the strip density is used. -/
theorem semicircularDiskConstantSequence_converges_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h = 1 / 2) :
    semicircularDiskConstantSequence.ConvergesTo a.carrier := by
  rw [carrier_eq_semicircularClosedDisk a hh]
  exact semicircularDiskConstantSequence_converges_closed


/-! ## Nondegenerate lower-contact geometry -/

/-- Assembly-dependent scale separating each lower replacement window from
the opposite join and keeping its radical uniformly inside the source circle. -/
def lowerSafeScale {lam : ℝ} (a : TypeThreeAssembly lam) : ℝ :=
  min (a.sideHalfWidth / 4) (min (a.radius / 4) (1 / 4))

theorem lowerSafeScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    0 < lowerSafeScale a := by
  rw [lowerSafeScale, lt_min_iff, lt_min_iff]
  exact ⟨div_pos (a.sideHalfWidth_pos hh) (by norm_num),
    div_pos a.radius_pos (by norm_num), by norm_num⟩

theorem lowerSafeScale_le_width_quarter
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    lowerSafeScale a ≤ a.sideHalfWidth / 4 :=
  min_le_left _ _

theorem lowerSafeScale_le_radius_quarter
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    lowerSafeScale a ≤ a.radius / 4 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem lowerSafeScale_le_quarter
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    lowerSafeScale a ≤ 1 / 4 :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- Rise of either lower side circle above the density-one interface, in the
outward horizontal coordinate `u`. -/
def lowerCircleRise {lam : ℝ} (a : TypeThreeAssembly lam) (u : ℝ) : ℝ :=
  a.radius - √(a.radius ^ 2 - u ^ 2)

private lemma lower_window_u_bounds
    {lam : ℝ} (a : TypeThreeAssembly lam) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a) :
    u ≤ a.radius ∧ u ≤ 1 / 4 := by
  constructor
  · have hquarter : u ≤ a.radius / 4 :=
      hu.trans (lowerSafeScale_le_radius_quarter a)
    nlinarith [a.radius_pos]
  · exact hu.trans (lowerSafeScale_le_quarter a)

theorem lowerCircleRise_nonneg
    {lam : ℝ} (a : TypeThreeAssembly lam) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a) :
    0 ≤ lowerCircleRise a u := by
  have huR := (lower_window_u_bounds a hu0 hu).1
  have hrad : 0 ≤ a.radius ^ 2 - u ^ 2 := by
    nlinarith [a.radius_pos]
  have hsqrt0 : 0 ≤ √(a.radius ^ 2 - u ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq :
      (√(a.radius ^ 2 - u ^ 2)) ^ 2 = a.radius ^ 2 - u ^ 2 :=
    Real.sq_sqrt hrad
  unfold lowerCircleRise
  nlinarith

/-- Rationalized circle rise.  This exact cancellation is the source of the
extra factor of the window scale in the lower replacement trace. -/
theorem lowerCircleRise_eq_div
    {lam : ℝ} (a : TypeThreeAssembly lam) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a) :
    lowerCircleRise a u =
      u ^ 2 / (a.radius + √(a.radius ^ 2 - u ^ 2)) := by
  have huR := (lower_window_u_bounds a hu0 hu).1
  have hrad : 0 ≤ a.radius ^ 2 - u ^ 2 := by
    nlinarith [a.radius_pos]
  have hsqrtSq :
      (√(a.radius ^ 2 - u ^ 2)) ^ 2 = a.radius ^ 2 - u ^ 2 :=
    Real.sq_sqrt hrad
  have hden : 0 < a.radius + √(a.radius ^ 2 - u ^ 2) :=
    add_pos_of_pos_of_nonneg a.radius_pos (Real.sqrt_nonneg _)
  apply (eq_div_iff hden.ne').2
  unfold lowerCircleRise
  nlinarith

theorem lowerCircleRise_le_u
    {lam : ℝ} (a : TypeThreeAssembly lam) {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a) :
    lowerCircleRise a u ≤ u := by
  have huR := (lower_window_u_bounds a hu0 hu).1
  have hrad : 0 ≤ a.radius ^ 2 - u ^ 2 := by
    nlinarith [a.radius_pos]
  have hsqrt0 : 0 ≤ √(a.radius ^ 2 - u ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq :
      (√(a.radius ^ 2 - u ^ 2)) ^ 2 = a.radius ^ 2 - u ^ 2 :=
    Real.sq_sqrt hrad
  have hRu : 0 ≤ a.radius - u := by linarith
  have hsq :
      (a.radius - u) ^ 2 ≤
        (√(a.radius ^ 2 - u ^ 2)) ^ 2 := by
    rw [hsqrtSq]
    nlinarith
  have hle : a.radius - u ≤ √(a.radius ^ 2 - u ^ 2) :=
    (sq_le_sq₀ hRu hsqrt0).1 hsq
  unfold lowerCircleRise
  linarith

/-- The actual circle rise is smooth on the complete internally selected
window; the square-root pole is separated by the radius-quarter guard. -/
theorem contDiffOn_lowerCircleRise
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiffOn ℝ 1 (lowerCircleRise a) (Icc (0 : ℝ) (lowerSafeScale a)) := by
  have hbase : ContDiff ℝ ∞ (fun u : ℝ => a.radius ^ 2 - u ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  have hne : ∀ u ∈ Icc (0 : ℝ) (lowerSafeScale a),
      a.radius ^ 2 - u ^ 2 ≠ 0 := by
    intro u hu
    have huQuarter :
        u ≤ a.radius / 4 :=
      hu.2.trans (lowerSafeScale_le_radius_quarter a)
    have huR : u < a.radius := by linarith [hu.1, a.radius_pos]
    have husq : u ^ 2 < a.radius ^ 2 :=
      (sq_lt_sq₀ hu.1 a.radius_pos.le).2 huR
    have hpos : 0 < a.radius ^ 2 - u ^ 2 := by linarith
    exact hpos.ne'
  unfold lowerCircleRise
  exact contDiffOn_const.sub
    ((hbase.of_le (by simp)).contDiffOn.sqrt hne)

theorem exists_lowerCircleRise_lipschitz
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ K : ℝ≥0, LipschitzOnWith K (lowerCircleRise a)
      (Icc (0 : ℝ) (lowerSafeScale a)) := by
  exact (contDiffOn_lowerCircleRise a).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc

/-- The circle rise is `C∞` on the full open interval between its two radical
poles.  Every retained lower window lies strictly inside this interval. -/
theorem contDiffOn_lowerCircleRise_open
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiffOn ℝ ∞ (lowerCircleRise a) (Ioo (-a.radius) a.radius) := by
  have hbase : ContDiff ℝ ∞ (fun u : ℝ => a.radius ^ 2 - u ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  have hne : ∀ u ∈ Ioo (-a.radius) a.radius,
      a.radius ^ 2 - u ^ 2 ≠ 0 := by
    intro u hu
    have hfactor : 0 < (u + a.radius) * (a.radius - u) :=
      mul_pos (by linarith [hu.1]) (by linarith [hu.2])
    have hpos : 0 < a.radius ^ 2 - u ^ 2 := by nlinarith
    exact hpos.ne'
  unfold lowerCircleRise
  exact contDiffOn_const.sub (hbase.contDiffOn.sqrt hne)



/-- Flat-to-circular cutoff in the normalized outward coordinate. -/
def lowerContactWeight (t : ℝ) : ℝ :=
  Real.smoothTransition (3 * t - 1)

theorem contDiff_lowerContactWeight :
    ContDiff ℝ ∞ lowerContactWeight := by
  unfold lowerContactWeight
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul contDiff_id |>.sub contDiff_const)

theorem exists_lowerContactWeight_lipschitz :
    ∃ K : ℝ≥0, LipschitzOnWith K lowerContactWeight (Icc (0 : ℝ) 1) := by
  have hsmoothFull : ContDiffOn ℝ ∞ lowerContactWeight (Icc (0 : ℝ) 1) :=
    contDiff_lowerContactWeight.contDiffOn
  have hsmooth : ContDiffOn ℝ 1 lowerContactWeight (Icc (0 : ℝ) 1) :=
    hsmoothFull.of_le (by simp)
  exact hsmooth.exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc

theorem lowerContactWeight_mem_Icc (t : ℝ) :
    lowerContactWeight t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem lowerContactWeight_eq_zero {t : ℝ} (ht : t ≤ 1 / 3) :
    lowerContactWeight t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem lowerContactWeight_eq_one {t : ℝ} (ht : 2 / 3 ≤ t) :
    lowerContactWeight t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith


/-- Lower boundary graph in the outward coordinate `u`.  It is flat near
`u = 0` and is the actual source-circle graph near `u = epsilon`. -/
def lowerContactGraph
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon u : ℝ) : ℝ :=
  -1 + lowerContactWeight (u / epsilon) * lowerCircleRise a u

theorem contDiffOn_lowerContactGraph
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    ContDiffOn ℝ ∞ (lowerContactGraph a epsilon)
      (Ioo (-a.radius) a.radius) := by
  have hratio : ContDiff ℝ ∞ (fun u : ℝ => u / epsilon) :=
    contDiff_id.div_const epsilon
  have hweight : ContDiffOn ℝ ∞
      (fun u : ℝ => lowerContactWeight (u / epsilon))
      (Ioo (-a.radius) a.radius) :=
    contDiff_lowerContactWeight.comp_contDiffOn hratio.contDiffOn
  unfold lowerContactGraph
  exact contDiffOn_const.add
    (hweight.mul (contDiffOn_lowerCircleRise_open a))

theorem lowerContactGraph_eq_flat
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {u : ℝ} (hu : u / epsilon ≤ 1 / 3) :
    lowerContactGraph a epsilon u = -1 := by
  rw [lowerContactGraph, lowerContactWeight_eq_zero hu]
  ring

theorem lowerContactGraph_eq_circle
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {u : ℝ} (hu : 2 / 3 ≤ u / epsilon) :
    lowerContactGraph a epsilon u = -1 + lowerCircleRise a u := by
  rw [lowerContactGraph, lowerContactWeight_eq_one hu]
  ring

theorem lowerContactGraph_scaled
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (t : ℝ) :
    lowerContactGraph a epsilon (epsilon * t) =
      -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t) := by
  rw [lowerContactGraph, show epsilon * t / epsilon = t by
    field_simp [hepsilon.ne']]

/-- Outward horizontal coordinate for either reflected lower contact. -/
def signedLowerOutwardCoordinate
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign : ℝ) (p : PlanePoint) : ℝ :=
  horizontalSign * p.1 - a.sideHalfWidth

/-- Open local epigraph represented by one lower replacement graph. -/
def signedLowerLocalDomain
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) : Set PlanePoint :=
  {p | lowerContactGraph a epsilon
      (signedLowerOutwardCoordinate a horizontalSign p) < p.2}

/-- Neighborhood on which the circle radical, and hence the local lower
defining function, is `C∞`. -/
def signedLowerGraphNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign : ℝ) : Set PlanePoint :=
  {p | signedLowerOutwardCoordinate a horizontalSign p ∈
    Ioo (-a.radius) a.radius}

theorem isOpen_signedLowerLocalDomain
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) :
    IsOpen (signedLowerLocalDomain a horizontalSign epsilon) := by
  apply isOpen_lt
  · unfold lowerContactGraph lowerContactWeight lowerCircleRise
      signedLowerOutwardCoordinate
    fun_prop
  · exact continuous_snd

/-- Literal local regular-defining-function certificate for the lower
surgery.  It applies at the flat join, through the cutoff, and at the outer
window edge; the vertical derivative is `-1`, independent of the circle
parameters. -/
theorem signedLowerLocalDomain_regular_at
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) {p : PlanePoint}
    (hp : p ∈ signedLowerGraphNeighborhood a horizontalSign)
    (heq : lowerContactGraph a epsilon
      (signedLowerOutwardCoordinate a horizontalSign p) = p.2) :
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      signedLowerLocalDomain a horizontalSign epsilon ∩ V =
        V ∩ {q | g q < 0} := by
  let coord : PlanePoint → ℝ :=
    fun q => signedLowerOutwardCoordinate a horizontalSign q
  let V : Set PlanePoint := coord ⁻¹' Ioo (-a.radius) a.radius
  let g : PlanePoint → ℝ :=
    fun q => lowerContactGraph a epsilon (coord q) - q.2
  let d : ℝ := deriv (lowerContactGraph a epsilon) (coord p)
  let D : PlanePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ d).comp
        (horizontalSign • ContinuousLinearMap.fst ℝ ℝ ℝ) -
      ContinuousLinearMap.snd ℝ ℝ ℝ
  have hcoordSmooth : ContDiff ℝ ∞ coord := by
    dsimp [coord]
    unfold signedLowerOutwardCoordinate
    fun_prop
  have hopenV : IsOpen V := by
    exact isOpen_Ioo.preimage hcoordSmooth.continuous
  have hpV : p ∈ V := by
    simpa [V, coord, signedLowerGraphNeighborhood] using hp
  have hgraph :=
    contDiffOn_lowerContactGraph a epsilon
  have hgraphComp : ContDiffOn ℝ ∞
      (fun q : PlanePoint => lowerContactGraph a epsilon (coord q)) V := by
    change ContDiffOn ℝ ∞ (lowerContactGraph a epsilon ∘ coord)
      (coord ⁻¹' Ioo (-a.radius) a.radius)
    exact hgraph.comp hcoordSmooth.contDiffOn (fun q hq => hq)
  have hgSmooth : ContDiffOn ℝ ∞ g V := by
    dsimp only [g]
    exact hgraphComp.sub contDiffOn_snd
  have hgraphAt : ContDiffAt ℝ ∞
      (lowerContactGraph a epsilon) (coord p) :=
    hgraph.contDiffAt (isOpen_Ioo.mem_nhds hpV)
  have hgraphDeriv :
      HasDerivAt (lowerContactGraph a epsilon) d (coord p) := by
    exact (hgraphAt.differentiableAt (by simp)).hasDerivAt
  have hcoordDeriv :
      HasFDerivAt coord
        (horizontalSign • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    dsimp only [coord]
    unfold signedLowerOutwardCoordinate
    have hcoordBase :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul horizontalSign
    simpa using hcoordBase.sub_const a.sideHalfWidth
  have hderiv : HasFDerivAt g D p := by
    have hcomp := hgraphDeriv.hasFDerivAt.comp p hcoordDeriv
    dsimp only [g]
    simpa [D, d, Function.comp_apply] using!
      hcomp.sub (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg
      (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hzero
    simp [D] at happ
  refine ⟨V, g, D, hopenV, hpV, hgSmooth, ?_, hderiv, hD, ?_⟩
  · dsimp only [g, coord]
    rw [heq]
    ring
  · ext q
    simp only [signedLowerLocalDomain, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    dsimp only [g, coord]
    constructor
    · rintro ⟨hq, hqV⟩
      exact ⟨hqV, by linarith⟩
    · rintro ⟨hqV, hq⟩
      exact ⟨by linarith, hqV⟩

/-- Buffered local window around one bottom join.  Its vertical extent is fixed
inside the strip; its horizontal width is proportional to `epsilon`. -/
def signedLowerPatchWindow
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) : Set PlanePoint :=
  {p | signedLowerOutwardCoordinate a horizontalSign p ∈
      Ioo (-epsilon / 6) (7 * epsilon / 6)} ∩
    {p | p.2 ∈ Ioo (-(3 / 2 : ℝ)) 0}

theorem isOpen_signedLowerPatchWindow
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) :
    IsOpen (signedLowerPatchWindow a horizontalSign epsilon) := by
  have hcoord : Continuous
      (signedLowerOutwardCoordinate a horizontalSign) := by
    unfold signedLowerOutwardCoordinate
    fun_prop
  exact (isOpen_Ioo.preimage hcoord).inter
    (isOpen_Ioo.preimage continuous_snd)

/-- The right buffered window is an explicit rectangle of width
`4 * epsilon / 3`. -/
theorem signedLowerPatchWindow_one
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    signedLowerPatchWindow a 1 epsilon =
      Ioo (a.sideHalfWidth - epsilon / 6)
          (a.sideHalfWidth + 7 * epsilon / 6) ×ˢ
        Ioo (-(3 / 2 : ℝ)) 0 := by
  ext p
  simp only [signedLowerPatchWindow, signedLowerOutwardCoordinate,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo,
    Set.mem_prod]
  constructor
  · rintro ⟨hcoord, hvertical⟩
    exact ⟨⟨by nlinarith [hcoord.1], by nlinarith [hcoord.2]⟩,
      hvertical⟩
  · rintro ⟨hhorizontal, hvertical⟩
    exact ⟨⟨by nlinarith [hhorizontal.1],
      by nlinarith [hhorizontal.2]⟩, hvertical⟩

/-- The left buffered window is the reflected explicit rectangle. -/
theorem signedLowerPatchWindow_neg_one
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    signedLowerPatchWindow a (-1) epsilon =
      Ioo (-a.sideHalfWidth - 7 * epsilon / 6)
          (-a.sideHalfWidth + epsilon / 6) ×ˢ
        Ioo (-(3 / 2 : ℝ)) 0 := by
  ext p
  simp only [signedLowerPatchWindow, signedLowerOutwardCoordinate,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo,
    Set.mem_prod]
  constructor
  · rintro ⟨hcoord, hvertical⟩
    exact ⟨⟨by nlinarith [hcoord.2], by nlinarith [hcoord.1]⟩,
      hvertical⟩
  · rintro ⟨hhorizontal, hvertical⟩
    exact ⟨⟨by nlinarith [hhorizontal.2],
      by nlinarith [hhorizontal.1]⟩, hvertical⟩

/-- Either buffered window has planar volume exactly `2 * epsilon` when the
scale is nonnegative. -/
theorem volume_signedLowerPatchWindow
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign : ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsign : horizontalSign = 1 ∨ horizontalSign = -1) :
    volume (signedLowerPatchWindow a horizontalSign epsilon) =
      ENNReal.ofReal (2 * epsilon) := by
  rcases hsign with rfl | rfl
  · rw [signedLowerPatchWindow_one, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_mul]
    · congr 1
      ring
    · nlinarith [hepsilon]
  · rw [signedLowerPatchWindow_neg_one, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_mul]
    · congr 1
      ring
    · nlinarith [hepsilon]

/-- One local added patch, bounded so that it cannot alter the upper contacts
or any remote part of the carrier. -/
def signedLowerPatch
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) : Set PlanePoint :=
  signedLowerLocalDomain a horizontalSign epsilon ∩
    signedLowerPatchWindow a horizontalSign epsilon

theorem isOpen_signedLowerPatch
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) :
    IsOpen (signedLowerPatch a horizontalSign epsilon) :=
  (isOpen_signedLowerLocalDomain a horizontalSign epsilon).inter
    (isOpen_signedLowerPatchWindow a horizontalSign epsilon)

/-- Actual lower-only surgery: retain the target interior and add the two
buffered epigraph patches.  The untouched upper contacts are intentionally not
claimed smooth at this stage. -/
def lowerSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set PlanePoint :=
  interior a.carrier ∪
    (signedLowerPatch a 1 epsilon ∪ signedLowerPatch a (-1) epsilon)

theorem isOpen_lowerSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    IsOpen (lowerSurgeryDomain a epsilon) :=
  isOpen_interior.union
    ((isOpen_signedLowerPatch a 1 epsilon).union
      (isOpen_signedLowerPatch a (-1) epsilon))

/-- Outside the two explicit buffered windows, the open surgery agrees exactly
with the target interior.  No open set is equated with the closed carrier. -/
theorem lowerSurgeryDomain_diff_windows :
    {lam : ℝ} → (a : TypeThreeAssembly lam) → (epsilon : ℝ) →
    lowerSurgeryDomain a epsilon \
        (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon) =
      interior a.carrier \
        (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon)
  | _, a, epsilon => by
      ext p
      simp only [lowerSurgeryDomain, signedLowerPatch, Set.mem_sdiff,
        Set.mem_union, Set.mem_inter_iff]
      aesop

/-- Relative to the target interior, every changed point lies in one of the
two shrinking windows. -/
theorem lowerSurgeryDomain_symmDiff_interior_subset_windows
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    lowerSurgeryDomain a epsilon ∆ interior a.carrier ⊆
      signedLowerPatchWindow a 1 epsilon ∪
        signedLowerPatchWindow a (-1) epsilon := by
  intro p hp
  simp only [Set.mem_symmDiff, lowerSurgeryDomain, signedLowerPatch,
    Set.mem_union, Set.mem_inter_iff] at hp
  rcases hp with hp | hp
  · rcases hp.1 with htarget | hright | hleft
    · exact False.elim (hp.2 htarget)
    · exact Or.inl hright.2
    · exact Or.inr hleft.2
  · exact False.elim (hp.2 (Or.inl hp.1))

/-- The lower surgery differs from the target interior by at most the total
area of its two buffered windows. -/
theorem characteristicDistance_lowerSurgeryDomain_interior_le
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    characteristicDistance (lowerSurgeryDomain a epsilon)
        (interior a.carrier) ≤
      ENNReal.ofReal (4 * epsilon) := by
  unfold characteristicDistance
  calc
    volume (lowerSurgeryDomain a epsilon ∆ interior a.carrier) ≤
        volume (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon) :=
      measure_mono
        (lowerSurgeryDomain_symmDiff_interior_subset_windows a epsilon)
    _ ≤ volume (signedLowerPatchWindow a 1 epsilon) +
        volume (signedLowerPatchWindow a (-1) epsilon) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (2 * epsilon) +
        ENNReal.ofReal (2 * epsilon) := by
      rw [volume_signedLowerPatchWindow a 1 hepsilon (Or.inl rfl),
        volume_signedLowerPatchWindow a (-1) hepsilon (Or.inr rfl)]
    _ = ENNReal.ofReal (4 * epsilon) := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * epsilon)]
      · congr 1
        ring
      · nlinarith [hepsilon]

/-- Positive scales for the lower-only surgery on both nondegenerate branches. -/
def lowerRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) : ℝ :=
  lowerSafeScale a / ((n : ℝ) + 1)

theorem lowerRecoveryScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) (n : ℕ) :
    0 < lowerRecoveryScale a n :=
  div_pos (lowerSafeScale_pos a hh) (by positivity)

theorem lowerRecoveryScale_le
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) :
    lowerRecoveryScale a n ≤ lowerSafeScale a := by
  unfold lowerRecoveryScale
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hscale : 0 ≤ lowerSafeScale a := by
    unfold lowerSafeScale
    exact le_min
      (div_nonneg a.sideHalfWidth_nonneg (by norm_num))
      (le_min (div_nonneg a.radius_pos.le (by norm_num)) (by norm_num))
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  nlinarith

theorem tendsto_lowerRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Tendsto (lowerRecoveryScale a) atTop (𝓝 0) := by
  unfold lowerRecoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)


/-- The shrinking lower surgery converges in characteristic-function distance
to the target interior. -/
theorem tendsto_characteristicDistance_lowerSurgeryDomain_interior
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    Tendsto
      (fun n => characteristicDistance
        (lowerSurgeryDomain a (lowerRecoveryScale a n))
        (interior a.carrier))
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun n : ℕ => ENNReal.ofReal (4 * lowerRecoveryScale a n))
      atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ => 4 * lowerRecoveryScale a n)
        atTop (𝓝 (4 * 0)) :=
      tendsto_const_nhds.mul (tendsto_lowerRecoveryScale a)
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n =>
      characteristicDistance_lowerSurgeryDomain_interior_le a
        (lowerRecoveryScale_pos a hh n).le)

/-- A continuously varying shifted squared-width level has zero planar
volume: every horizontal fiber has at most two points. -/
theorem volume_shiftedSquaredWidthBoundary
    (centerX : ℝ) (q : ℝ → ℝ) (hq : Continuous q) :
    volume {p : PlanePoint | (p.1 - centerX) ^ 2 = q p.2} = 0 := by
  have hmeasurable :
      MeasurableSet {p : PlanePoint | (p.1 - centerX) ^ 2 = q p.2} := by
    exact (isClosed_eq
      ((continuous_fst.sub continuous_const).pow 2)
      (hq.comp continuous_snd)).measurableSet
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm hmeasurable]
  have hfiber : ∀ y : ℝ,
      volume ((fun x : ℝ => (x, y)) ⁻¹'
        {p : PlanePoint | (p.1 - centerX) ^ 2 = q p.2}) = 0 := by
    intro y
    change volume {x : ℝ | (x - centerX) ^ 2 = q y} = 0
    by_cases hqy : 0 ≤ q y
    · apply Set.Finite.measure_zero
      refine ({centerX + √(q y), centerX - √(q y)} :
        Set ℝ).toFinite.subset ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hsqrt : (√(q y)) ^ 2 = q y := Real.sq_sqrt hqy
      have hroot :
          x - centerX = √(q y) ∨ x - centerX = -√(q y) := by
        rw [← hsqrt] at hx
        exact (sq_eq_sq_iff_eq_or_eq_neg).mp hx
      rcases hroot with hroot | hroot
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have hempty : {x : ℝ | (x - centerX) ^ 2 = q y} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hqy (by nlinarith [sq_nonneg (x - centerX)])
      simp [hempty]
  simp_rw [hfiber]
  simp

/-- A horizontal coordinate level has zero planar volume. -/
theorem volume_horizontalLevel (y : ℝ) :
    volume {p : PlanePoint | p.2 = y} = 0 := by
  have hset :
      {p : PlanePoint | p.2 = y} =
        (Set.univ : Set ℝ) ×ˢ ({y} : Set ℝ) := by
    ext p
    simp
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- The coordinate frontier of every actual type-(iii) carrier is planar
Lebesgue-null. -/
theorem volume_frontier_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    volume (frontier a.carrier) = 0 := by
  have hleft : volume a.leftArcTrace = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        (p.1 - a.leftCenter.1) ^ 2 =
          a.radius ^ 2 - (p.2 - a.leftCenter.2) ^ 2})
    · intro p hp
      change
        (p.1 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 = a.radius ^ 2 ∧
          p.1 ≤ a.leftCenter.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hp
      change (p.1 - a.leftCenter.1) ^ 2 =
        a.radius ^ 2 - (p.2 - a.leftCenter.2) ^ 2
      nlinarith [hp.1]
    · exact volume_shiftedSquaredWidthBoundary a.leftCenter.1
        (fun y => a.radius ^ 2 - (y - a.leftCenter.2) ^ 2)
        (by fun_prop)
  have hright : volume a.rightArcTrace = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        (p.1 - a.rightCenter.1) ^ 2 =
          a.radius ^ 2 - (p.2 - a.rightCenter.2) ^ 2})
    · intro p hp
      change
        (p.1 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 = a.radius ^ 2 ∧
          a.rightCenter.1 ≤ p.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hp
      change (p.1 - a.rightCenter.1) ^ 2 =
        a.radius ^ 2 - (p.2 - a.rightCenter.2) ^ 2
      nlinarith [hp.1]
    · exact volume_shiftedSquaredWidthBoundary a.rightCenter.1
        (fun y => a.radius ^ 2 - (y - a.rightCenter.2) ^ 2)
        (by fun_prop)
  have hupper :
      volume (OneSidedCircularCap.arcTrace a.outerCap) = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint |
        (p.1 - a.outerCap.center.1) ^ 2 =
          a.outerCap.radius ^ 2 -
            (p.2 - a.outerCap.center.2) ^ 2})
    · intro p hp
      change a.outerCap.radiusSquaredAt p = a.outerCap.radius ^ 2 ∧ _ at hp
      have hcircle := hp.1
      rw [OneSidedCircularCap.radiusSquaredAt] at hcircle
      change (p.1 - a.outerCap.center.1) ^ 2 =
        a.outerCap.radius ^ 2 -
          (p.2 - a.outerCap.center.2) ^ 2
      nlinarith [hcircle]
    · exact volume_shiftedSquaredWidthBoundary a.outerCap.center.1
        (fun y => a.outerCap.radius ^ 2 -
          (y - a.outerCap.center.2) ^ 2)
        (by fun_prop)
  have hbottom : volume a.bottomSegmentCarrier = 0 := by
    apply measure_mono_null
      (t := {p : PlanePoint | p.2 = -1})
    · exact fun _ hp => hp.1
    · exact volume_horizontalLevel (-1)
  rw [a.frontier_carrier, TypeThreeAssembly.boundaryTrace]
  apply le_antisymm ?_ bot_le
  calc
    volume (a.leftArcTrace ∪
        (a.rightArcTrace ∪
          (OneSidedCircularCap.arcTrace a.outerCap ∪
            a.bottomSegmentCarrier))) ≤
        volume a.leftArcTrace +
          volume (a.rightArcTrace ∪
            (OneSidedCircularCap.arcTrace a.outerCap ∪
              a.bottomSegmentCarrier)) :=
      measure_union_le _ _
    _ ≤ volume a.leftArcTrace +
        (volume a.rightArcTrace +
          volume (OneSidedCircularCap.arcTrace a.outerCap ∪
            a.bottomSegmentCarrier)) := by
      gcongr
      exact measure_union_le _ _
    _ ≤ volume a.leftArcTrace +
        (volume a.rightArcTrace +
          (volume (OneSidedCircularCap.arcTrace a.outerCap) +
            volume a.bottomSegmentCarrier)) := by
      gcongr
      exact measure_union_le _ _
    _ = 0 := by rw [hleft, hright, hupper, hbottom]; simp

/-- The target interior and literal closed type-(iii) carrier agree almost
everywhere. -/
theorem interior_carrier_ae_eq_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    interior a.carrier =ᵐ[volume] a.carrier := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpInterior, hpNotCarrier⟩
      exact (hpNotCarrier (interior_subset hpInterior)).elim
    · exact measure_empty
  · apply measure_mono_null (t := frontier a.carrier)
    · rintro p ⟨hpCarrier, hpNotInterior⟩
      rw [mem_frontier_iff_notMem_interior hpCarrier]
      exact hpNotInterior
    · exact volume_frontier_carrier a

/-- The same explicit `4 * epsilon` estimate holds against the literal closed
carrier, not only its open representative. -/
theorem characteristicDistance_lowerSurgeryDomain_carrier_le
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    characteristicDistance (lowerSurgeryDomain a epsilon) a.carrier ≤
      ENNReal.ofReal (4 * epsilon) := by
  rw [← characteristicDistance_congr_ae
    (lowerSurgeryDomain a epsilon) (interior_carrier_ae_eq_carrier a)]
  exact characteristicDistance_lowerSurgeryDomain_interior_le a hepsilon

/-- The shrinking lower surgery converges globally to the literal closed
type-(iii) carrier. -/
theorem tendsto_characteristicDistance_lowerSurgeryDomain_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    Tendsto
      (fun n => characteristicDistance
        (lowerSurgeryDomain a (lowerRecoveryScale a n)) a.carrier)
      atTop (𝓝 0) := by
  have hfun :
      (fun n => characteristicDistance
        (lowerSurgeryDomain a (lowerRecoveryScale a n)) a.carrier) =
      (fun n => characteristicDistance
        (lowerSurgeryDomain a (lowerRecoveryScale a n))
          (interior a.carrier)) := by
    funext n
    exact (characteristicDistance_congr_ae
      (lowerSurgeryDomain a (lowerRecoveryScale a n))
      (interior_carrier_ae_eq_carrier a)).symm
  rw [hfun]
  exact tendsto_characteristicDistance_lowerSurgeryDomain_interior a hh
/-- Right replacement trace.  It keeps the lower interface fixed near the
join and is the actual right source circle near the outer window edge. -/
def rightLowerContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon t : ℝ) : PlanePoint :=
  (a.sideHalfWidth + epsilon * t,
    -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t))

/-- Horizontal reflection of the right lower replacement trace. -/
def leftLowerContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon t : ℝ) : PlanePoint :=
  (-a.sideHalfWidth - epsilon * t,
    -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t))

/-- Both reflected lower traces are represented by a unit horizontal sign. -/
def signedLowerContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon t : ℝ) : PlanePoint :=
  (horizontalSign * (a.sideHalfWidth + epsilon * t),
    -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t))

theorem signedLowerContactTrace_one
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon t : ℝ) :
    signedLowerContactTrace a 1 epsilon t =
      rightLowerContactTrace a epsilon t := by
  simp [signedLowerContactTrace, rightLowerContactTrace]

theorem signedLowerContactTrace_neg_one
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon t : ℝ) :
    signedLowerContactTrace a (-1) epsilon t =
      leftLowerContactTrace a epsilon t := by
  apply Prod.ext
  · simp [signedLowerContactTrace, leftLowerContactTrace]
    ring
  · simp [signedLowerContactTrace, leftLowerContactTrace]


/-- Every point of either retained lower replacement trace carries the literal
local regular defining-function certificate, including `t = 0` and `t = 1`. -/
theorem signedLowerContactTrace_regular_at
    {lam : ℝ} (a : TypeThreeAssembly lam) {horizontalSign epsilon t : ℝ}
    (hsign : |horizontalSign| = 1)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ signedLowerContactTrace a horizontalSign epsilon t ∈ V ∧
      ContDiffOn ℝ ∞ g V ∧
      g (signedLowerContactTrace a horizontalSign epsilon t) = 0 ∧
      HasFDerivAt g D
        (signedLowerContactTrace a horizontalSign epsilon t) ∧
      D ≠ 0 ∧
      signedLowerLocalDomain a horizontalSign epsilon ∩ V =
        V ∩ {q | g q < 0} := by
  have hsignSq : horizontalSign ^ 2 = 1 := by
    calc
      horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hsign]; norm_num
  have hcoord :
      signedLowerOutwardCoordinate a horizontalSign
          (signedLowerContactTrace a horizontalSign epsilon t) =
        epsilon * t := by
    unfold signedLowerOutwardCoordinate signedLowerContactTrace
    dsimp only
    calc
      horizontalSign * (horizontalSign *
          (a.sideHalfWidth + epsilon * t)) - a.sideHalfWidth =
        horizontalSign ^ 2 * (a.sideHalfWidth + epsilon * t) -
          a.sideHalfWidth := by ring
      _ = epsilon * t := by rw [hsignSq]; ring
  have hu0 : 0 ≤ epsilon * t := mul_nonneg hepsilon.le ht.1
  have hue : epsilon * t ≤ lowerSafeScale a :=
    (mul_le_of_le_one_right hepsilon.le ht.2).trans hepsilon_le
  have huR : epsilon * t < a.radius := by
    have hquarter := hue.trans (lowerSafeScale_le_radius_quarter a)
    linarith [a.radius_pos]
  have hp :
      signedLowerContactTrace a horizontalSign epsilon t ∈
        signedLowerGraphNeighborhood a horizontalSign := by
    change signedLowerOutwardCoordinate a horizontalSign
      (signedLowerContactTrace a horizontalSign epsilon t) ∈
        Ioo (-a.radius) a.radius
    rw [hcoord]
    exact ⟨by linarith [a.radius_pos], huR⟩
  have heq :
      lowerContactGraph a epsilon
          (signedLowerOutwardCoordinate a horizontalSign
            (signedLowerContactTrace a horizontalSign epsilon t)) =
        (signedLowerContactTrace a horizontalSign epsilon t).2 := by
    rw [hcoord, lowerContactGraph_scaled a hepsilon t]
    rfl
  exact signedLowerLocalDomain_regular_at a horizontalSign epsilon hp heq

/-- Every reflected lower replacement trace has Euclidean Lipschitz constant
`O(epsilon)`.  The exact circle-rise cancellation prevents a cutoff derivative
from producing a fixed nonvanishing length. -/
theorem exists_scaled_signedLowerContactTrace_lipschitz
    {lam : ℝ} (a : TypeThreeAssembly lam) {horizontalSign : ℝ}
    (hsign : |horizontalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
      epsilon ≤ lowerSafeScale a →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ =>
          planeEuclideanHomeomorph
            (signedLowerContactTrace a horizontalSign epsilon t))
        (Icc (0 : ℝ) 1) := by
  rcases exists_lowerCircleRise_lipschitz a with ⟨Kr, hKr⟩
  rcases exists_lowerContactWeight_lipschitz with ⟨Kw, hKw⟩
  let K : ℝ≥0 := 1 + Kr + Kw
  refine ⟨K, ?_⟩
  intro epsilon hepsilon hepsilon_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  have het0 : 0 ≤ epsilon * t := mul_nonneg hepsilon.le ht.1
  have heu0 : 0 ≤ epsilon * u := mul_nonneg hepsilon.le hu.1
  have het : epsilon * t ≤ lowerSafeScale a := by
    exact (mul_le_of_le_one_right hepsilon.le ht.2).trans hepsilon_le
  have heu : epsilon * u ≤ lowerSafeScale a := by
    exact (mul_le_of_le_one_right hepsilon.le hu.2).trans hepsilon_le
  let rt := lowerCircleRise a (epsilon * t)
  let ru := lowerCircleRise a (epsilon * u)
  let wt := lowerContactWeight t
  let wu := lowerContactWeight u
  have hargument :
      |epsilon * t - epsilon * u| = epsilon * |t - u| := by
    rw [show epsilon * t - epsilon * u = epsilon * (t - u) by ring,
      abs_mul, abs_of_pos hepsilon]
  have hrise :
      |rt - ru| ≤ (Kr : ℝ) * (epsilon * |t - u|) := by
    have h := hKr.dist_le_mul (epsilon * t) ⟨het0, het⟩
      (epsilon * u) ⟨heu0, heu⟩
    simpa only [Real.dist_eq, hargument, rt, ru] using h
  have hweight :
      |wt - wu| ≤ (Kw : ℝ) * |t - u| := by
    have h := hKw.dist_le_mul t ht u hu
    simpa only [Real.dist_eq, wt, wu] using h
  have hwt : |wt| ≤ 1 := by
    rw [abs_of_nonneg (lowerContactWeight_mem_Icc t).1]
    exact (lowerContactWeight_mem_Icc t).2
  have hru0 : 0 ≤ ru := lowerCircleRise_nonneg a heu0 heu
  have hrule : ru ≤ epsilon := by
    calc
      ru ≤ epsilon * u := lowerCircleRise_le_u a heu0 heu
      _ ≤ epsilon := mul_le_of_le_one_right hepsilon.le hu.2
  have hru : |ru| ≤ epsilon := by
    rw [abs_of_nonneg hru0]
    exact hrule
  have hvertical :
      |wt * rt - wu * ru| ≤
        ((Kr : ℝ) + (Kw : ℝ)) * (epsilon * |t - u|) := by
    calc
      |wt * rt - wu * ru| =
          |wt * (rt - ru) + (wt - wu) * ru| := by
        congr 1
        ring
      _ ≤ |wt * (rt - ru)| + |(wt - wu) * ru| := abs_add_le _ _
      _ = |wt| * |rt - ru| + |wt - wu| * |ru| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * ((Kr : ℝ) * (epsilon * |t - u|)) +
          ((Kw : ℝ) * |t - u|) * epsilon := by
        gcongr
      _ = ((Kr : ℝ) + (Kw : ℝ)) * (epsilon * |t - u|) := by
        ring
  have hx :
      dist
          (horizontalSign * (a.sideHalfWidth + epsilon * t))
          (horizontalSign * (a.sideHalfWidth + epsilon * u)) =
        epsilon * dist t u := by
    rw [Real.dist_eq, Real.dist_eq,
      show horizontalSign * (a.sideHalfWidth + epsilon * t) -
          horizontalSign * (a.sideHalfWidth + epsilon * u) =
        horizontalSign * epsilon * (t - u) by ring,
      abs_mul, abs_mul, hsign, one_mul, abs_of_pos hepsilon]
  have hy :
      dist
          (-1 + wt * rt)
          (-1 + wu * ru) ≤
        ((Kr : ℝ) + (Kw : ℝ)) * (epsilon * dist t u) := by
    rw [Real.dist_eq, show
      (-1 + wt * rt) - (-1 + wu * ru) = wt * rt - wu * ru by ring,
      Real.dist_eq]
    exact hvertical
  calc
    dist
        (planeEuclideanHomeomorph
          (signedLowerContactTrace a horizontalSign epsilon t))
        (planeEuclideanHomeomorph
          (signedLowerContactTrace a horizontalSign epsilon u)) ≤
      dist
          (horizontalSign * (a.sideHalfWidth + epsilon * t))
          (horizontalSign * (a.sideHalfWidth + epsilon * u)) +
        dist (-1 + wt * rt) (-1 + wu * ru) := by
      apply FrozenSquaredRecovery.dist_planeEuclideanHomeomorph_le
    _ ≤ epsilon * dist t u +
        ((Kr : ℝ) + (Kw : ℝ)) * (epsilon * dist t u) :=
      add_le_add hx.le hy
    _ = (((K * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u) := by
      change epsilon * dist t u +
          ((Kr : ℝ) + (Kw : ℝ)) * (epsilon * dist t u) =
        ((1 + (Kr : ℝ) + (Kw : ℝ)) * (epsilon.toNNReal : ℝ)) *
          dist t u
      rw [Real.coe_toNNReal epsilon hepsilon.le]
      ring

/-- Union of the two actual lower replacement traces in the Euclidean
realization used by `smoothCost`. -/
def lowerReplacementTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    Set EuclideanPlane :=
  (fun t : ℝ =>
      planeEuclideanHomeomorph (signedLowerContactTrace a 1 epsilon t)) ''
      Icc (0 : ℝ) 1 ∪
    (fun t : ℝ =>
      planeEuclideanHomeomorph (signedLowerContactTrace a (-1) epsilon t)) ''
      Icc (0 : ℝ) 1

/-- The complete pair of lower replacement traces has vanishing Euclidean
`H¹`: one finite assembly-dependent coefficient times `epsilon`. -/
theorem exists_scaled_lowerReplacementTrace_hausdorffMeasure
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ lowerSafeScale a →
        (μH[1] : Measure EuclideanPlane) (lowerReplacementTrace a epsilon) ≤
          C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_signedLowerContactTrace_lipschitz a
      (horizontalSign := (1 : ℝ)) (by norm_num) with ⟨Kr, hKr⟩
  rcases exists_scaled_signedLowerContactTrace_lipschitz a
      (horizontalSign := (-1 : ℝ)) (by norm_num) with ⟨Kl, hKl⟩
  let C : ℝ≥0∞ := (Kr : ℝ≥0∞) + (Kl : ℝ≥0∞)
  refine ⟨C, (ENNReal.add_lt_top).2
    ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩, ?_⟩
  intro epsilon hepsilon hepsilon_le
  have hr := (hKr hepsilon hepsilon_le).hausdorffMeasure_image_le
    (d := (1 : ℝ)) (by norm_num)
  have hl := (hKl hepsilon hepsilon_le).hausdorffMeasure_image_le
    (d := (1 : ℝ)) (by norm_num)
  have hr' :
      (μH[1] : Measure EuclideanPlane)
          ((fun t : ℝ =>
            planeEuclideanHomeomorph
              (signedLowerContactTrace a 1 epsilon t)) '' Icc (0 : ℝ) 1) ≤
        ((Kr * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.rpow_one, hausdorffMeasure_real,
      Real.volume_Icc] using hr
  have hl' :
      (μH[1] : Measure EuclideanPlane)
          ((fun t : ℝ =>
            planeEuclideanHomeomorph
              (signedLowerContactTrace a (-1) epsilon t)) '' Icc (0 : ℝ) 1) ≤
        ((Kl * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.rpow_one, hausdorffMeasure_real,
      Real.volume_Icc] using hl
  calc
    (μH[1] : Measure EuclideanPlane) (lowerReplacementTrace a epsilon) ≤
        (μH[1] : Measure EuclideanPlane)
            ((fun t : ℝ =>
              planeEuclideanHomeomorph
                (signedLowerContactTrace a 1 epsilon t)) '' Icc (0 : ℝ) 1) +
          (μH[1] : Measure EuclideanPlane)
            ((fun t : ℝ =>
              planeEuclideanHomeomorph
                (signedLowerContactTrace a (-1) epsilon t)) ''
                  Icc (0 : ℝ) 1) := by
      exact measure_union_le _ _
    _ ≤ ((Kr * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) +
          ((Kl * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) :=
      add_le_add hr' hl'
    _ = C * (epsilon.toNNReal : ℝ≥0∞) := by
      dsimp [C]
      ring

theorem lowerContactTrace_height_mem_Icc
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (-1 : ℝ) ≤
        -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t) ∧
      -1 + lowerContactWeight t * lowerCircleRise a (epsilon * t) ≤ 1 := by
  have hu0 : 0 ≤ epsilon * t := mul_nonneg hepsilon0.le ht.1
  have hue : epsilon * t ≤ lowerSafeScale a := by
    calc
      epsilon * t ≤ epsilon := mul_le_of_le_one_right hepsilon0.le ht.2
      _ ≤ lowerSafeScale a := hepsilon
  have huQuarter := (lower_window_u_bounds a hu0 hue).2
  have hr0 := lowerCircleRise_nonneg a hu0 hue
  have hru := lowerCircleRise_le_u a hu0 hue
  have hw := lowerContactWeight_mem_Icc t
  have hprod0 :
      0 ≤ lowerContactWeight t * lowerCircleRise a (epsilon * t) :=
    mul_nonneg hw.1 hr0
  have hprodle :
      lowerContactWeight t * lowerCircleRise a (epsilon * t) ≤
        lowerCircleRise a (epsilon * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw.2) hr0]
  constructor <;> nlinarith

theorem stripDensity_rightLowerContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    StripDensity lam (rightLowerContactTrace a epsilon t) = 1 := by
  have hy := lowerContactTrace_height_mem_Icc a hepsilon0 hepsilon ht
  rw [StripDensity, if_pos]
  exact abs_le.mpr hy

theorem stripDensity_leftLowerContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    StripDensity lam (leftLowerContactTrace a epsilon t) = 1 := by
  have hy := lowerContactTrace_height_mem_Icc a hepsilon0 hepsilon ht
  rw [StripDensity, if_pos]
  exact abs_le.mpr hy

theorem rightLowerContactTrace_eq_flat
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {t : ℝ} (ht : t ≤ 1 / 3) :
    rightLowerContactTrace a epsilon t =
      (a.sideHalfWidth + epsilon * t, -1) := by
  rw [rightLowerContactTrace, lowerContactWeight_eq_zero ht]
  simp

theorem leftLowerContactTrace_eq_flat
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {t : ℝ} (ht : t ≤ 1 / 3) :
    leftLowerContactTrace a epsilon t =
      (-a.sideHalfWidth - epsilon * t, -1) := by
  rw [leftLowerContactTrace, lowerContactWeight_eq_zero ht]
  simp

theorem rightLowerContactTrace_eq_circle
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {t : ℝ} (ht : 2 / 3 ≤ t) :
    rightLowerContactTrace a epsilon t =
      (a.sideHalfWidth + epsilon * t,
        -1 + lowerCircleRise a (epsilon * t)) := by
  rw [rightLowerContactTrace, lowerContactWeight_eq_one ht]
  simp

theorem leftLowerContactTrace_eq_circle
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ)
    {t : ℝ} (ht : 2 / 3 ≤ t) :
    leftLowerContactTrace a epsilon t =
      (-a.sideHalfWidth - epsilon * t,
        -1 + lowerCircleRise a (epsilon * t)) := by
  rw [leftLowerContactTrace, lowerContactWeight_eq_one ht]
  simp

theorem rightLowerContactTrace_mem_rightArcTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (2 / 3 : ℝ) 1) :
    rightLowerContactTrace a epsilon t ∈ a.rightArcTrace := by
  rw [rightLowerContactTrace_eq_circle a epsilon ht.1]
  have hu0 : 0 ≤ epsilon * t :=
    mul_nonneg hepsilon0.le (by linarith [ht.1])
  have hue : epsilon * t ≤ lowerSafeScale a := by
    calc
      epsilon * t ≤ epsilon := mul_le_of_le_one_right hepsilon0.le ht.2
      _ ≤ lowerSafeScale a := hepsilon
  have hrad : 0 ≤ a.radius ^ 2 - (epsilon * t) ^ 2 := by
    have huR := (lower_window_u_bounds a hu0 hue).1
    nlinarith [a.radius_pos]
  have hsqrtSq :
      (√(a.radius ^ 2 - (epsilon * t) ^ 2)) ^ 2 =
        a.radius ^ 2 - (epsilon * t) ^ 2 :=
    Real.sq_sqrt hrad
  have hr0 := lowerCircleRise_nonneg a hu0 hue
  have hru := lowerCircleRise_le_u a hu0 hue
  have huQuarter := (lower_window_u_bounds a hu0 hue).2
  have hy :
      (-1 : ℝ) ≤ -1 + lowerCircleRise a (epsilon * t) ∧
        -1 + lowerCircleRise a (epsilon * t) ≤ 1 := by
    constructor <;> nlinarith
  change
    ((a.sideHalfWidth + epsilon * t) - a.rightCenter.1) ^ 2 +
          ((-1 + lowerCircleRise a (epsilon * t)) -
            a.rightCenter.2) ^ 2 = a.radius ^ 2 ∧
      a.rightCenter.1 ≤ a.sideHalfWidth + epsilon * t ∧
      (-1 : ℝ) ≤ -1 + lowerCircleRise a (epsilon * t) ∧
      -1 + lowerCircleRise a (epsilon * t) ≤ 1
  refine ⟨?_, ?_, hy.1, hy.2⟩
  · simp only [TypeThreeAssembly.rightCenter]
    unfold lowerCircleRise
    nlinarith
  · simp only [TypeThreeAssembly.rightCenter]
    nlinarith

theorem leftLowerContactTrace_mem_leftArcTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ lowerSafeScale a)
    (ht : t ∈ Icc (2 / 3 : ℝ) 1) :
    leftLowerContactTrace a epsilon t ∈ a.leftArcTrace := by
  rw [leftLowerContactTrace_eq_circle a epsilon ht.1]
  have hu0 : 0 ≤ epsilon * t :=
    mul_nonneg hepsilon0.le (by linarith [ht.1])
  have hue : epsilon * t ≤ lowerSafeScale a := by
    calc
      epsilon * t ≤ epsilon := mul_le_of_le_one_right hepsilon0.le ht.2
      _ ≤ lowerSafeScale a := hepsilon
  have hrad : 0 ≤ a.radius ^ 2 - (epsilon * t) ^ 2 := by
    have huR := (lower_window_u_bounds a hu0 hue).1
    nlinarith [a.radius_pos]
  have hsqrtSq :
      (√(a.radius ^ 2 - (epsilon * t) ^ 2)) ^ 2 =
        a.radius ^ 2 - (epsilon * t) ^ 2 :=
    Real.sq_sqrt hrad
  have hr0 := lowerCircleRise_nonneg a hu0 hue
  have hru := lowerCircleRise_le_u a hu0 hue
  have huQuarter := (lower_window_u_bounds a hu0 hue).2
  have hy :
      (-1 : ℝ) ≤ -1 + lowerCircleRise a (epsilon * t) ∧
        -1 + lowerCircleRise a (epsilon * t) ≤ 1 := by
    constructor <;> nlinarith
  change
    ((-a.sideHalfWidth - epsilon * t) - a.leftCenter.1) ^ 2 +
          ((-1 + lowerCircleRise a (epsilon * t)) -
            a.leftCenter.2) ^ 2 = a.radius ^ 2 ∧
      -a.sideHalfWidth - epsilon * t ≤ a.leftCenter.1 ∧
      (-1 : ℝ) ≤ -1 + lowerCircleRise a (epsilon * t) ∧
      -1 + lowerCircleRise a (epsilon * t) ≤ 1
  refine ⟨?_, ?_, hy.1, hy.2⟩
  · simp only [TypeThreeAssembly.leftCenter]
    unfold lowerCircleRise
    nlinarith
  · simp only [TypeThreeAssembly.leftCenter]
    nlinarith

end CMVRelaxation.TypeThreeRecovery
