/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTypeThreeUpperRecovery

/-!
# Global smooth recovery for type-(iii) assemblies

This module glues the already checked lower-contact and upper-contact surgeries
into actual `SmoothSequence` values.  Closed change supports sit strictly inside
the buffered windows; outside them the surgery is literally the target interior.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation.TypeThreeRecovery

private theorem regularBoundaryCertificate_of_local_eq
    {U M V : Set PlanePoint} {p : PlanePoint}
    (hVopen : IsOpen V) (hpV : p ∈ V)
    (hlocal : U ∩ V = M ∩ V) (hp : p ∈ frontier U)
    (hmodel : ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      M ∩ W = W ∩ {q | g q < 0}) :
    ∃ (N : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiffOn ℝ ∞ g N ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      U ∩ N = N ∩ {q | g q < 0} := by
  have hpUV : p ∈ frontier U ∩ V := ⟨hp, hpV⟩
  rw [← frontier_inter_open_inter hVopen, hlocal,
    frontier_inter_open_inter hVopen] at hpUV
  rcases hmodel with ⟨W, g, D, hWopen, hpW, hg, hgp, hDerv, hD, hMW⟩
  refine ⟨V ∩ W, g, D, hVopen.inter hWopen, ⟨hpV, hpW⟩,
    hg.mono inter_subset_right, hgp, hDerv, hD, ?_⟩
  calc
    U ∩ (V ∩ W) = (U ∩ V) ∩ W := by ext q; simp only [mem_inter_iff]; tauto
    _ = (M ∩ V) ∩ W := by rw [hlocal]
    _ = V ∩ (M ∩ W) := by ext q; simp only [mem_inter_iff]; tauto
    _ = V ∩ (W ∩ {q | g q < 0}) := by rw [hMW]
    _ = (V ∩ W) ∩ {q | g q < 0} := by
      ext q
      simp only [mem_inter_iff]
      tauto

private theorem regularBoundaryCertificate_of_local_eq_of_smooth
    {U M V : Set PlanePoint} {p : PlanePoint}
    (hVopen : IsOpen V) (hpV : p ∈ V)
    (hlocal : U ∩ V = M ∩ V) (hp : p ∈ frontier U)
    (hM : IsSmoothDomain M) :
    ∃ (N : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiffOn ℝ ∞ g N ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      U ∩ N = N ∩ {q | g q < 0} := by
  have hpUV : p ∈ frontier U ∩ V := ⟨hp, hpV⟩
  rw [← frontier_inter_open_inter hVopen, hlocal,
    frontier_inter_open_inter hVopen] at hpUV
  exact regularBoundaryCertificate_of_local_eq hVopen hpV hlocal hp
    (hM.regular_boundary p hpUV.1)

private theorem squaredWidthDomain_regular_at_of_pos
    {q : ℝ → ℝ} {V : Set PlanePoint} {p : PlanePoint}
    (hVopen : IsOpen V) (hpV : p ∈ V)
    (hqAt : ContDiffAt ℝ ∞ q p.2)
    (hqV : ContDiffOn ℝ ∞ (fun z : PlanePoint => q z.2) V)
    (heq : p.1 ^ 2 = q p.2) (hqpos : 0 < q p.2) :
    ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      squaredWidthDomain q ∩ W = W ∩ {z | g z < 0} := by
  let g : PlanePoint → ℝ := fun z => z.1 ^ 2 - q z.2
  let d : ℝ := deriv q p.2
  let D : PlanePoint →L[ℝ] ℝ :=
    (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      (ContinuousLinearMap.toSpanSingleton ℝ d).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hqDeriv : HasDerivAt q d p.2 :=
    (hqAt.differentiableAt (by simp)).hasDerivAt
  have hderiv : HasFDerivAt g D p := by
    change HasFDerivAt
      ((fun z : PlanePoint => z.1 ^ 2) - q ∘ Prod.snd) D p
    simpa [D, d] using
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).sub
        (hqDeriv.hasFDerivAt.comp p
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  have hp1 : p.1 ≠ 0 := by
    intro hpzero
    rw [hpzero] at heq
    norm_num at heq
    linarith
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg
      (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hzero
    have : 2 * p.1 = 0 := by simpa [D] using happ
    exact hp1 (by linarith)
  refine ⟨V, g, D, hVopen, hpV, ?_, ?_, hderiv, hD, ?_⟩
  · dsimp only [g]
    exact (contDiffOn_fst.pow 2).sub hqV
  · dsimp only [g]
    linarith
  · ext z
    change ((z.1 ^ 2 < q z.2) ∧ z ∈ V) ↔
      (z ∈ V ∧ z.1 ^ 2 - q z.2 < 0)
    constructor
    · rintro ⟨hz, hzV⟩
      exact ⟨hzV, sub_neg.mpr hz⟩
    · rintro ⟨hzV, hz⟩
      exact ⟨sub_neg.mp hz, hzV⟩

lemma upperSideRadicand_pos_of_mem_Ioo
    {lam : ℝ} (a : TypeThreeAssembly lam) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    0 < upperSideRadicand a y := by
  unfold upperSideRadicand
  have hR := a.one_lt_radius
  have hfirst : 0 < y + 1 := by linarith [hy.1]
  have hsecond : 0 < 2 * a.radius - 1 - y := by
    linarith [hy.2, hR]
  nlinarith [mul_pos hfirst hsecond]

lemma contDiffOn_upperSideSquare_strip
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiffOn ℝ ∞ (upperSideSquare a) (Ioo (-1 : ℝ) 1) := by
  have hne : ∀ y ∈ Ioo (-1 : ℝ) 1,
      upperSideRadicand a y ≠ 0 := by
    intro y hy
    exact (upperSideRadicand_pos_of_mem_Ioo a hy).ne'
  unfold upperSideSquare
  exact (contDiffOn_const.add
    ((contDiff_upperSideRadicand a).contDiffOn.sqrt hne)).pow 2

private lemma carrier_y_ge_neg_one
    {lam : ℝ} (a : TypeThreeAssembly lam) {p : PlanePoint}
    (hp : p ∈ a.carrier) : (-1 : ℝ) ≤ p.2 := by
  rcases hp with hcore | hcap
  · rcases hcore with (hrect | hleft) | hright
    · exact hrect.2.1
    · exact hleft.2.2.1
    · exact hright.2.2.1
  · have hy : (1 : ℝ) ≤ p.2 := by
      simpa [TypeThreeAssembly.outerCap, OneSidedCircularCap.carrier] using hcap.2
    linarith

lemma interior_carrier_y_gt_neg_one
    {lam : ℝ} (a : TypeThreeAssembly lam) {p : PlanePoint}
    (hp : p ∈ interior a.carrier) : (-1 : ℝ) < p.2 := by
  have hpNhd : interior a.carrier ∈ 𝓝 p := isOpen_interior.mem_nhds hp
  rcases Metric.mem_nhds_iff.mp hpNhd with ⟨r, hr, hball⟩
  let z : PlanePoint := (p.1, p.2 - r / 2)
  have hzball : z ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [z]
    simp only [sub_self, abs_zero]
    rw [show p.2 - r / 2 - p.2 = -(r / 2) by ring,
      abs_neg, abs_of_pos (div_pos hr (by norm_num)),
      max_eq_right (by positivity)]
    linarith
  have hz := carrier_y_ge_neg_one a (interior_subset (hball hzball))
  dsimp [z] at hz
  linarith

private theorem mem_interior_of_above_lowerCircle
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign u : ℝ} {p : PlanePoint}
    (hsign : |horizontalSign| = 1)
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a)
    (hcoord : signedLowerOutwardCoordinate a horizontalSign p = u)
    (hy0 : p.2 < 0)
    (habove : -1 + lowerCircleRise a u < p.2) :
    p ∈ interior a.carrier := by
  have hsignSq : horizontalSign ^ 2 = 1 := by
    calc
      horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hsign]; norm_num
  have hsignx : horizontalSign * p.1 = a.sideHalfWidth + u := by
    unfold signedLowerOutwardCoordinate at hcoord
    linarith
  have hx : p.1 = horizontalSign * (a.sideHalfWidth + u) := by
    calc
      p.1 = horizontalSign ^ 2 * p.1 := by rw [hsignSq]; ring
      _ = horizontalSign * (horizontalSign * p.1) := by ring
      _ = horizontalSign * (a.sideHalfWidth + u) := by rw [hsignx]
  have huR : u ≤ a.radius := by
    have hquarter := hu.trans (lowerSafeScale_le_radius_quarter a)
    nlinarith [a.radius_pos]
  have hradU : 0 ≤ a.radius ^ 2 - u ^ 2 := by
    nlinarith [a.radius_pos]
  let rootU := √(a.radius ^ 2 - u ^ 2)
  have hrootU0 : 0 ≤ rootU := Real.sqrt_nonneg _
  have hrootUSq : rootU ^ 2 = a.radius ^ 2 - u ^ 2 :=
    Real.sq_sqrt hradU
  have hydown : a.radius - 1 - rootU < p.2 := by
    unfold lowerCircleRise at habove
    dsimp [rootU]
    linarith
  have hyup : p.2 < a.radius - 1 + rootU := by
    linarith [a.one_lt_radius]
  have hinside :
      u ^ 2 + (p.2 - (a.radius - 1)) ^ 2 < a.radius ^ 2 := by
    nlinarith
  have hylo : (-1 : ℝ) < p.2 := by
    have hrise := lowerCircleRise_nonneg a hu0 hu
    linarith
  have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := ⟨hylo, by linarith⟩
  have hradY := upperSideRadicand_pos_of_mem_Ioo a hyStrip
  let rootY := √(upperSideRadicand a p.2)
  have hrootY0 : 0 ≤ rootY := Real.sqrt_nonneg _
  have hrootYSq : rootY ^ 2 = upperSideRadicand a p.2 :=
    Real.sq_sqrt hradY.le
  have huRoot : u < rootY := by
    unfold upperSideRadicand at hrootYSq
    nlinarith
  have hwidth :
      (a.sideHalfWidth + u) ^ 2 <
        (a.sideHalfWidth + rootY) ^ 2 := by
    nlinarith [a.sideHalfWidth_nonneg]
  apply (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).2
  rw [hx, mul_pow, hsignSq, one_mul]
  simpa only [upperSideSquare, rootY] using hwidth

/-- Closed region containing every genuinely added point of one lower patch. -/
def signedLowerChangeSupport
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) : Set PlanePoint :=
  {p | signedLowerOutwardCoordinate a horizontalSign p ∈
      Icc 0 (2 * epsilon / 3)} ∩
    {p | p.2 ∈ Icc (-1 : ℝ) (-1 + 2 * epsilon / 3)}

lemma isClosed_signedLowerChangeSupport
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) :
    IsClosed (signedLowerChangeSupport a horizontalSign epsilon) := by
  have hcoord : Continuous
      (signedLowerOutwardCoordinate a horizontalSign) := by
    unfold signedLowerOutwardCoordinate
    fun_prop
  exact (isClosed_Icc.preimage hcoord).inter
    (isClosed_Icc.preimage continuous_snd)

private theorem lowerCircle_lt_y_of_mem_interior
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign u : ℝ} {p : PlanePoint}
    (hsign : |horizontalSign| = 1)
    (hu0 : 0 ≤ u) (hu : u ≤ lowerSafeScale a)
    (hcoord : signedLowerOutwardCoordinate a horizontalSign p = u)
    (hy0 : p.2 < 0) (hp : p ∈ interior a.carrier) :
    -1 + lowerCircleRise a u < p.2 := by
  have hsignSq : horizontalSign ^ 2 = 1 := by
    calc
      horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hsign]; norm_num
  have hsignx : horizontalSign * p.1 = a.sideHalfWidth + u := by
    unfold signedLowerOutwardCoordinate at hcoord
    linarith
  have hx : p.1 = horizontalSign * (a.sideHalfWidth + u) := by
    calc
      p.1 = horizontalSign ^ 2 * p.1 := by rw [hsignSq]; ring
      _ = horizontalSign * (horizontalSign * p.1) := by ring
      _ = horizontalSign * (a.sideHalfWidth + u) := by rw [hsignx]
  have hylo := interior_carrier_y_gt_neg_one a hp
  have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := ⟨hylo, by linarith⟩
  have hpSide :=
    (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).1 hp
  have hradY := upperSideRadicand_pos_of_mem_Ioo a hyStrip
  let rootY := √(upperSideRadicand a p.2)
  have hrootY0 : 0 ≤ rootY := Real.sqrt_nonneg _
  have hrootYSq : rootY ^ 2 = upperSideRadicand a p.2 :=
    Real.sq_sqrt hradY.le
  have huRootY : u < rootY := by
    rw [hx, mul_pow, hsignSq, one_mul] at hpSide
    unfold upperSideSquare at hpSide
    change (a.sideHalfWidth + u) ^ 2 <
      (a.sideHalfWidth + rootY) ^ 2 at hpSide
    nlinarith [a.sideHalfWidth_nonneg]
  have huR : u ≤ a.radius := by
    have hquarter := hu.trans (lowerSafeScale_le_radius_quarter a)
    nlinarith [a.radius_pos]
  have hradU : 0 ≤ a.radius ^ 2 - u ^ 2 := by
    nlinarith [a.radius_pos]
  let rootU := √(a.radius ^ 2 - u ^ 2)
  have hrootU0 : 0 ≤ rootU := Real.sqrt_nonneg _
  have hrootUSq : rootU ^ 2 = a.radius ^ 2 - u ^ 2 :=
    Real.sq_sqrt hradU
  have hinside :
      u ^ 2 + (p.2 - (a.radius - 1)) ^ 2 < a.radius ^ 2 := by
    unfold upperSideRadicand at hrootYSq
    nlinarith
  have hydown : a.radius - 1 - rootU < p.2 := by
    have hdneg : p.2 - (a.radius - 1) < 0 := by
      linarith [a.one_lt_radius]
    nlinarith
  unfold lowerCircleRise
  dsimp [rootU] at hydown ⊢
  linarith

/-- A lower patch can add points only in the closed transition rectangle.
The flat and circular buffer lanes are already target-interior points. -/
theorem signedLowerPatch_sdiff_interior_subset_changeSupport
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {horizontalSign epsilon : ℝ}
    (hsign : |horizontalSign| = 1)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ lowerSafeScale a / 2) :
    signedLowerPatch a horizontalSign epsilon \ interior a.carrier ⊆
      signedLowerChangeSupport a horizontalSign epsilon := by
  intro p hp
  rcases hp with ⟨⟨hlocal, hwindow⟩, hnotInterior⟩
  let u := signedLowerOutwardCoordinate a horizontalSign p
  change u ∈ Ioo (-epsilon / 6) (7 * epsilon / 6) ∧
    p.2 ∈ Ioo (-(3 / 2 : ℝ)) 0 at hwindow
  change lowerContactGraph a epsilon u < p.2 at hlocal
  have huSafe : u ≤ lowerSafeScale a := by
    have hsafe0 := (lowerSafeScale_pos a hh).le
    nlinarith [hwindow.1.2, hepsilon_le]
  have hsignSq : horizontalSign ^ 2 = 1 := by
    calc
      horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hsign]; norm_num
  have hsignx : horizontalSign * p.1 = a.sideHalfWidth + u := by
    dsimp [u]
    unfold signedLowerOutwardCoordinate
    ring_nf
  have hx : p.1 = horizontalSign * (a.sideHalfWidth + u) := by
    calc
      p.1 = horizontalSign ^ 2 * p.1 := by rw [hsignSq]; ring
      _ = horizontalSign * (horizontalSign * p.1) := by ring
      _ = horizontalSign * (a.sideHalfWidth + u) := by rw [hsignx]
  have hu0 : 0 ≤ u := by
    by_contra h
    have huneg : u < 0 := lt_of_not_ge h
    have hratio : u / epsilon ≤ 1 / 3 := by
      have : u / epsilon < 0 := div_neg_of_neg_of_pos huneg hepsilon
      linarith
    rw [lowerContactGraph_eq_flat a epsilon hratio] at hlocal
    have hylo : (-1 : ℝ) < p.2 := by linarith
    have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hylo, by linarith [hwindow.2.2]⟩
    have hradY := upperSideRadicand_pos_of_mem_Ioo a hyStrip
    let rootY := √(upperSideRadicand a p.2)
    have hrootYpos : 0 < rootY := Real.sqrt_pos.2 hradY
    have hwpos := a.sideHalfWidth_pos hh
    have hew : epsilon ≤ a.sideHalfWidth / 8 := by
      have hscale := lowerSafeScale_le_width_quarter a
      nlinarith
    have hwu : 0 < a.sideHalfWidth + u := by
      nlinarith [hwindow.1.1]
    have hwidth :
        (a.sideHalfWidth + u) ^ 2 <
          (a.sideHalfWidth + rootY) ^ 2 := by
      have hfac1 : 0 < rootY - u := by linarith
      have hfac2 : 0 < 2 * a.sideHalfWidth + rootY + u := by
        linarith
      nlinarith [mul_pos hfac1 hfac2]
    apply hnotInterior
    apply (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).2
    rw [hx, mul_pow, hsignSq, one_mul]
    simpa only [upperSideSquare, rootY] using hwidth
  have huUpper : u ≤ 2 * epsilon / 3 := by
    by_contra h
    have htwo : 2 / 3 ≤ u / epsilon := by
      rw [le_div_iff₀ hepsilon]
      nlinarith
    rw [lowerContactGraph_eq_circle a epsilon htwo] at hlocal
    exact hnotInterior
      (mem_interior_of_above_lowerCircle a hsign hu0 huSafe rfl
        hwindow.2.2 hlocal)
  have hrise0 := lowerCircleRise_nonneg a hu0 huSafe
  have hyLower : (-1 : ℝ) ≤ p.2 := by
    have hw0 := (lowerContactWeight_mem_Icc (u / epsilon)).1
    unfold lowerContactGraph at hlocal
    nlinarith [mul_nonneg hw0 hrise0]
  have hyUpper : p.2 ≤ -1 + 2 * epsilon / 3 := by
    by_contra h
    have hstrict : -1 + 2 * epsilon / 3 < p.2 :=
      lt_of_not_ge h
    have hriseLe := lowerCircleRise_le_u a hu0 huSafe
    apply hnotInterior
    apply mem_interior_of_above_lowerCircle a hsign hu0 huSafe rfl
      hwindow.2.2
    nlinarith
  exact ⟨⟨hu0, huUpper⟩, hyLower, hyUpper⟩



/-- Buffered neighborhood used to read one lower transition as its smooth
graph domain.  The closed change support is strictly inside this set. -/
def signedLowerModelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) : Set PlanePoint :=
  {p | signedLowerOutwardCoordinate a horizontalSign p ∈
      Ioo (-epsilon / 12) (3 * epsilon / 4)} ∩
    {p | p.2 ∈ Ioo (-(5 / 4 : ℝ)) (-(3 / 4 : ℝ))}

lemma isOpen_signedLowerModelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon : ℝ) :
    IsOpen (signedLowerModelNeighborhood a horizontalSign epsilon) := by
  have hcoord : Continuous
      (signedLowerOutwardCoordinate a horizontalSign) := by
    unfold signedLowerOutwardCoordinate
    fun_prop
  exact (isOpen_Ioo.preimage hcoord).inter
    (isOpen_Ioo.preimage continuous_snd)

lemma signedLowerChangeSupport_subset_modelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ lowerSafeScale a / 2) :
    signedLowerChangeSupport a horizontalSign epsilon ⊆
      signedLowerModelNeighborhood a horizontalSign epsilon := by
  intro p hp
  have hquarter := lowerSafeScale_le_quarter a
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    ⟨by linarith [hp.2.1], by
      nlinarith [hp.2.2, hepsilon_le, hquarter]⟩⟩

private lemma signedLowerModelNeighborhood_subset_patchWindow
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ} (hepsilon : 0 < epsilon) :
    signedLowerModelNeighborhood a horizontalSign epsilon ⊆
      signedLowerPatchWindow a horizontalSign epsilon := by
  intro p hp
  exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

private lemma upperSurgeryDomain_eq_interior_on_lowerNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    upperSurgeryDomain a epsilon ∩
        signedLowerModelNeighborhood a horizontalSign epsilon =
      interior a.carrier ∩
        signedLowerModelNeighborhood a horizontalSign epsilon := by
  ext p
  constructor
  · rintro ⟨hp, hpV⟩
    refine ⟨?_, hpV⟩
    rcases hp with hpTarget | hpBlend
    · exact hpTarget.1
    · exfalso
      have houter := hpBlend.2
      change p.2 ∈ Ioo (1 - 3 * epsilon / 2)
        (1 + epsilon / 2) at houter
      have hpHeight := hpV.2
      change p.2 ∈ Ioo (-(5 / 4 : ℝ)) (-(3 / 4 : ℝ)) at hpHeight
      have heighth := upperSafeScale_le_eighth a
      nlinarith [houter.1, hpHeight.2, hepsilon_upper, heighth]
  · rintro ⟨hp, hpV⟩
    refine ⟨Or.inl ⟨hp, ?_⟩, hpV⟩
    intro hpInner
    change p.2 ∈ Icc (1 - 4 * epsilon / 3)
      (1 + epsilon / 3) at hpInner
    have hpHeight := hpV.2
    change p.2 ∈ Ioo (-(5 / 4 : ℝ)) (-(3 / 4 : ℝ)) at hpHeight
    have heighth := upperSafeScale_le_eighth a
    nlinarith [hpInner.1, hpHeight.2, hepsilon_upper, heighth]

private lemma interior_subset_signedLowerLocalDomain_on_modelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ}
    (hsign : |horizontalSign| = 1)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ lowerSafeScale a / 2) :
    interior a.carrier ∩
        signedLowerModelNeighborhood a horizontalSign epsilon ⊆
      signedLowerLocalDomain a horizontalSign epsilon := by
  intro p hp
  rcases hp with ⟨hpInterior, hpV⟩
  let u := signedLowerOutwardCoordinate a horizontalSign p
  change u ∈ Ioo (-epsilon / 12) (3 * epsilon / 4) ∧
    p.2 ∈ Ioo (-(5 / 4 : ℝ)) (-(3 / 4 : ℝ)) at hpV
  have hylo := interior_carrier_y_gt_neg_one a hpInterior
  by_cases hu : u ≤ 0
  · have hratio : u / epsilon ≤ 1 / 3 := by
      have hdiv : u / epsilon ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hu hepsilon.le
      linarith
    change lowerContactGraph a epsilon u < p.2
    rw [lowerContactGraph_eq_flat a epsilon hratio]
    exact hylo
  · have hu0 : 0 ≤ u := le_of_not_ge hu
    have huSafe : u ≤ lowerSafeScale a := by
      have hsafe0 : 0 < lowerSafeScale a := by
        nlinarith [hepsilon, hepsilon_le]
      nlinarith [hpV.1.2, hepsilon_le]
    have hcircle := lowerCircle_lt_y_of_mem_interior a hsign hu0 huSafe rfl
      (by linarith [hpV.2.2]) hpInterior
    have hrise0 := lowerCircleRise_nonneg a hu0 huSafe
    have hw := lowerContactWeight_mem_Icc (u / epsilon)
    change lowerContactGraph a epsilon u < p.2
    unfold lowerContactGraph
    nlinarith [mul_nonneg (sub_nonneg.mpr hw.2) hrise0]

private lemma signedLowerModelNeighborhood_one_disjoint_leftPatch
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ lowerSafeScale a / 2) :
    Disjoint (signedLowerModelNeighborhood a 1 epsilon)
      (signedLowerPatch a (-1) epsilon) := by
  rw [Set.disjoint_left]
  intro p hpV hpPatch
  have hwpos := a.sideHalfWidth_pos hh
  have hwidth := lowerSafeScale_le_width_quarter a
  have hv := hpV.1
  have hpw := hpPatch.2.1
  change signedLowerOutwardCoordinate a 1 p ∈
    Ioo (-epsilon / 12) (3 * epsilon / 4) at hv
  change signedLowerOutwardCoordinate a (-1) p ∈
    Ioo (-epsilon / 6) (7 * epsilon / 6) at hpw
  norm_num [signedLowerOutwardCoordinate] at hv hpw
  nlinarith

private lemma signedLowerModelNeighborhood_neg_one_disjoint_rightPatch
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ lowerSafeScale a / 2) :
    Disjoint (signedLowerModelNeighborhood a (-1) epsilon)
      (signedLowerPatch a 1 epsilon) := by
  rw [Set.disjoint_left]
  intro p hpV hpPatch
  have hwpos := a.sideHalfWidth_pos hh
  have hwidth := lowerSafeScale_le_width_quarter a
  have hv := hpV.1
  have hpw := hpPatch.2.1
  change signedLowerOutwardCoordinate a (-1) p ∈
    Ioo (-epsilon / 12) (3 * epsilon / 4) at hv
  change signedLowerOutwardCoordinate a 1 p ∈
    Ioo (-epsilon / 6) (7 * epsilon / 6) at hpw
  norm_num [signedLowerOutwardCoordinate] at hv hpw
  nlinarith

theorem combinedSurgeryDomain_eq_rightLowerLocal_on_modelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lower : epsilon ≤ lowerSafeScale a / 2)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    combinedSurgeryDomain a epsilon ∩
        signedLowerModelNeighborhood a 1 epsilon =
      signedLowerLocalDomain a 1 epsilon ∩
        signedLowerModelNeighborhood a 1 epsilon := by
  have hupper := upperSurgeryDomain_eq_interior_on_lowerNeighborhood
    a (horizontalSign := (1 : ℝ)) hepsilon hepsilon_upper
  have hinterior :=
    interior_subset_signedLowerLocalDomain_on_modelNeighborhood
      a (horizontalSign := (1 : ℝ)) (by norm_num) hepsilon hepsilon_lower
  have hwindow := signedLowerModelNeighborhood_subset_patchWindow
    a (horizontalSign := (1 : ℝ)) hepsilon
  have hdisjoint :=
    signedLowerModelNeighborhood_one_disjoint_leftPatch
      a hh hepsilon hepsilon_lower
  ext p
  constructor
  · rintro ⟨hp, hpV⟩
    refine ⟨?_, hpV⟩
    rcases hp with hpUpper | hpRight | hpLeft
    · exact hinterior ⟨(Set.ext_iff.mp hupper p).mp ⟨hpUpper, hpV⟩ |>.1, hpV⟩
    · exact hpRight.1
    · exact False.elim (Set.disjoint_left.mp hdisjoint hpV hpLeft)
  · rintro ⟨hpLocal, hpV⟩
    exact ⟨Or.inr (Or.inl ⟨hpLocal, hwindow hpV⟩), hpV⟩

theorem combinedSurgeryDomain_eq_leftLowerLocal_on_modelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lower : epsilon ≤ lowerSafeScale a / 2)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    combinedSurgeryDomain a epsilon ∩
        signedLowerModelNeighborhood a (-1) epsilon =
      signedLowerLocalDomain a (-1) epsilon ∩
        signedLowerModelNeighborhood a (-1) epsilon := by
  have hupper := upperSurgeryDomain_eq_interior_on_lowerNeighborhood
    a (horizontalSign := (-1 : ℝ)) hepsilon hepsilon_upper
  have hinterior :=
    interior_subset_signedLowerLocalDomain_on_modelNeighborhood
      a (horizontalSign := (-1 : ℝ)) (by norm_num) hepsilon hepsilon_lower
  have hwindow := signedLowerModelNeighborhood_subset_patchWindow
    a (horizontalSign := (-1 : ℝ)) hepsilon
  have hdisjoint :=
    signedLowerModelNeighborhood_neg_one_disjoint_rightPatch
      a hh hepsilon hepsilon_lower
  ext p
  constructor
  · rintro ⟨hp, hpV⟩
    refine ⟨?_, hpV⟩
    rcases hp with hpUpper | hpRight | hpLeft
    · exact hinterior ⟨(Set.ext_iff.mp hupper p).mp ⟨hpUpper, hpV⟩ |>.1, hpV⟩
    · exact False.elim (Set.disjoint_left.mp hdisjoint hpV hpRight)
    · exact hpLeft.1
  · rintro ⟨hpLocal, hpV⟩
    exact ⟨Or.inr (Or.inr ⟨hpLocal, hwindow hpV⟩), hpV⟩

private lemma interior_mem_upperSurgeryDomain_of_y_lt_zero
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_upper : epsilon ≤ upperSafeScale a)
    {p : PlanePoint} (hp : p ∈ interior a.carrier) (hy : p.2 < 0) :
    p ∈ upperSurgeryDomain a epsilon := by
  apply Or.inl
  refine ⟨hp, ?_⟩
  intro hpInner
  change p.2 ∈ Icc (1 - 4 * epsilon / 3)
    (1 + epsilon / 3) at hpInner
  have heighth := upperSafeScale_le_eighth a
  nlinarith [hpInner.1, hepsilon_upper, heighth]

theorem combinedSurgeryDomain_sdiff_upperSurgeryDomain_subset_lowerSupports
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lower : epsilon ≤ lowerSafeScale a / 2)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    combinedSurgeryDomain a epsilon \ upperSurgeryDomain a epsilon ⊆
      signedLowerChangeSupport a 1 epsilon ∪
        signedLowerChangeSupport a (-1) epsilon := by
  intro p hp
  rcases hp.1 with hpUpper | hpRight | hpLeft
  · exact False.elim (hp.2 hpUpper)
  · apply Or.inl
    apply signedLowerPatch_sdiff_interior_subset_changeSupport
      a hh (horizontalSign := (1 : ℝ)) (by norm_num) hepsilon hepsilon_lower
    exact ⟨hpRight, fun hpInterior => hp.2
      (interior_mem_upperSurgeryDomain_of_y_lt_zero a hepsilon hepsilon_upper
        hpInterior hpRight.2.2.2)⟩
  · apply Or.inr
    apply signedLowerPatch_sdiff_interior_subset_changeSupport
      a hh (horizontalSign := (-1 : ℝ)) (by norm_num) hepsilon hepsilon_lower
    exact ⟨hpLeft, fun hpInterior => hp.2
      (interior_mem_upperSurgeryDomain_of_y_lt_zero a hepsilon hepsilon_upper
        hpInterior hpLeft.2.2.2)⟩


def belowUpperTransition (epsilon : ℝ) : Set PlanePoint :=
  Prod.snd ⁻¹' Iio (1 - epsilon)

def aboveUpperTransition : Set PlanePoint :=
  Prod.snd ⁻¹' Ioi (1 : ℝ)

def upperModelNeighborhood (epsilon : ℝ) : Set PlanePoint :=
  Prod.snd ⁻¹' Ioo (1 - 7 * epsilon / 6) (1 + epsilon / 6)

lemma isOpen_belowUpperTransition (epsilon : ℝ) :
    IsOpen (belowUpperTransition epsilon) :=
  isOpen_Iio.preimage continuous_snd

lemma isOpen_aboveUpperTransition :
    IsOpen aboveUpperTransition :=
  isOpen_Ioi.preimage continuous_snd

lemma isOpen_upperModelNeighborhood (epsilon : ℝ) :
    IsOpen (upperModelNeighborhood epsilon) :=
  isOpen_Ioo.preimage continuous_snd

theorem upperSurgeryDomain_eq_interior_belowTransition
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    upperSurgeryDomain a epsilon ∩ belowUpperTransition epsilon =
      interior a.carrier ∩ belowUpperTransition epsilon := by
  ext p
  constructor
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    rcases hp with hpTarget | hpBlend
    · exact hpTarget.1
    · have houter := hpBlend.2
      change p.2 ∈ Ioo (1 - 3 * epsilon / 2)
        (1 + epsilon / 2) at houter
      change p.2 < 1 - epsilon at hy
      have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := by
        have heighth := upperSafeScale_le_eighth a
        constructor <;> nlinarith [houter.1, hy, hepsilon_le, heighth]
      have hq := hpBlend.1
      change p.1 ^ 2 < upperBlendQ a epsilon p.2 at hq
      rw [upperBlendQ_eq_side a hepsilon hy.le] at hq
      exact (mem_interior_carrier_iff_sq_lt_upperSideSquare
        a p hyStrip).2 hq
  · rintro ⟨hp, hy⟩
    by_cases hpInner : p ∈ upperInnerBand epsilon
    · refine ⟨Or.inr ⟨?_, upperInnerBand_subset_outerBand hepsilon hpInner⟩, hy⟩
      change p.2 < 1 - epsilon at hy
      have hinner := hpInner
      change p.2 ∈ Icc (1 - 4 * epsilon / 3)
        (1 + epsilon / 3) at hinner
      have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := by
        have heighth := upperSafeScale_le_eighth a
        constructor <;> nlinarith [hinner.1, hy, hepsilon_le, heighth]
      change p.1 ^ 2 < upperBlendQ a epsilon p.2
      rw [upperBlendQ_eq_side a hepsilon hy.le]
      exact (mem_interior_carrier_iff_sq_lt_upperSideSquare
        a p hyStrip).1 hp
    · exact ⟨Or.inl ⟨hp, hpInner⟩, hy⟩

theorem upperSurgeryDomain_eq_upperBlend_on_modelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    upperSurgeryDomain a epsilon ∩ upperModelNeighborhood epsilon =
      upperBlendDomain a epsilon ∩ upperModelNeighborhood epsilon := by
  have hinner : upperModelNeighborhood epsilon ⊆ upperInnerBand epsilon := by
    intro p hp
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have houter : upperModelNeighborhood epsilon ⊆ upperOuterBand epsilon := by
    intro p hp
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  ext p
  constructor
  · rintro ⟨hp, hpV⟩
    rcases hp with hpTarget | hpBlend
    · exact False.elim (hpTarget.2 (hinner hpV))
    · exact ⟨hpBlend.1, hpV⟩
  · rintro ⟨hpBlend, hpV⟩
    exact ⟨Or.inr ⟨hpBlend, houter hpV⟩, hpV⟩

/-- Above the upper attachment, the target interior has the literal cap
squared-width description, including the implication needed near the pole. -/
theorem mem_interior_carrier_iff_sq_lt_upperCapSquare_of_one_lt
    {lam : ℝ} (a : TypeThreeAssembly lam) (p : PlanePoint)
    (hy : 1 < p.2) :
    p ∈ interior a.carrier ↔ p.1 ^ 2 < upperCapSquare a p.2 := by
  constructor
  · intro hp
    have hle := (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt
      a p hy).1 (interior_subset hp)
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : interior a.carrier ∈ 𝓝 p :=
      isOpen_interior.mem_nhds hp
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
    by_cases hx : 0 ≤ p.1
    · let z : PlanePoint := (p.1 + r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_pos (by linarith : 0 < p.1 + r / 2 - p.1)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzle :=
        (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a z hy).1
          (interior_subset (hball hzball))
      change (p.1 + r / 2) ^ 2 ≤ upperCapSquare a p.2 at hzle
      nlinarith
    · have hxneg : p.1 < 0 := lt_of_not_ge hx
      let z : PlanePoint := (p.1 - r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_neg (by linarith : p.1 - r / 2 - p.1 < 0)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzle :=
        (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a z hy).1
          (interior_subset (hball hzball))
      change (p.1 - r / 2) ^ 2 ≤ upperCapSquare a p.2 at hzle
      nlinarith
  · intro hp
    exact (mem_interior_carrier_iff_sq_lt_upperCapSquare
      a p hy (lt_of_le_of_lt (sq_nonneg p.1) hp)).2 hp

theorem upperSurgeryDomain_eq_interior_aboveTransition
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    upperSurgeryDomain a epsilon ∩ aboveUpperTransition =
      interior a.carrier ∩ aboveUpperTransition := by
  ext p
  constructor
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    rcases hp with hpTarget | hpBlend
    · exact hpTarget.1
    · change 1 < p.2 at hy
      have hq := hpBlend.1
      change p.1 ^ 2 < upperBlendQ a epsilon p.2 at hq
      rw [upperBlendQ_eq_cap a hepsilon hy.le] at hq
      exact (mem_interior_carrier_iff_sq_lt_upperCapSquare_of_one_lt
        a p hy).2 hq
  · rintro ⟨hp, hy⟩
    by_cases hpInner : p ∈ upperInnerBand epsilon
    · refine ⟨Or.inr ⟨?_, upperInnerBand_subset_outerBand hepsilon hpInner⟩, hy⟩
      change 1 < p.2 at hy
      change p.1 ^ 2 < upperBlendQ a epsilon p.2
      rw [upperBlendQ_eq_cap a hepsilon hy.le]
      exact (mem_interior_carrier_iff_sq_lt_upperCapSquare_of_one_lt
        a p hy).1 hp
    · exact ⟨Or.inl ⟨hp, hpInner⟩, hy⟩

def upperCapDomain {lam : ℝ} (a : TypeThreeAssembly lam) : Set PlanePoint :=
  squaredWidthDomain (upperCapSquare a)

theorem isSmoothDomain_upperCapDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    IsSmoothDomain (upperCapDomain a) := by
  unfold upperCapDomain
  apply isSmoothDomain_squaredWidth (contDiff_upperCapSquare a)
  intro y hy
  have hderiv :
      HasDerivAt (upperCapSquare a) (-2 * (y - a.upperCenter.2)) y := by
    have hraw := (hasDerivAt_const y (a.radius ^ 2)).sub
      (((hasDerivAt_id y).sub_const a.upperCenter.2).pow 2)
    simpa [upperCapSquare, Pi.sub_apply] using! hraw
  rw [hderiv.deriv]
  intro hzero
  unfold upperCapSquare at hy
  nlinarith [a.radius_pos]



def sideWidthDomain {lam : ℝ} (a : TypeThreeAssembly lam) : Set PlanePoint :=
  squaredWidthDomain (upperSideSquare a)

def sideModelNeighborhood : Set PlanePoint :=
  Prod.snd ⁻¹' Ioo (-1 : ℝ) 1

lemma isOpen_sideModelNeighborhood : IsOpen sideModelNeighborhood :=
  isOpen_Ioo.preimage continuous_snd

theorem interior_carrier_eq_sideWidthDomain_on_strip
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    interior a.carrier ∩ sideModelNeighborhood =
      sideWidthDomain a ∩ sideModelNeighborhood := by
  ext p
  change (p ∈ interior a.carrier ∧ p.2 ∈ Ioo (-1 : ℝ) 1) ↔
    (p.1 ^ 2 < upperSideSquare a p.2 ∧ p.2 ∈ Ioo (-1 : ℝ) 1)
  constructor
  · rintro ⟨hp, hy⟩
    exact ⟨(mem_interior_carrier_iff_sq_lt_upperSideSquare a p hy).1 hp, hy⟩
  · rintro ⟨hp, hy⟩
    exact ⟨(mem_interior_carrier_iff_sq_lt_upperSideSquare a p hy).2 hp, hy⟩

private theorem sideWidthDomain_regular_at
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {p : PlanePoint} (hp : p ∈ frontier (sideWidthDomain a))
    (hpV : p ∈ sideModelNeighborhood) :
    ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      sideWidthDomain a ∩ W = W ∩ {z | g z < 0} := by
  have hcontinuous : Continuous (upperSideSquare a) := continuous_upperSideSquare a
  have heq : p.1 ^ 2 = upperSideSquare a p.2 :=
    frontier_lt_subset_eq (continuous_fst.pow 2)
      (hcontinuous.comp continuous_snd) hp
  have hqpos : 0 < upperSideSquare a p.2 := by
    unfold upperSideSquare
    exact sq_pos_of_pos
      (add_pos_of_pos_of_nonneg (a.sideHalfWidth_pos hh) (Real.sqrt_nonneg _))
  have hqAt : ContDiffAt ℝ ∞ (upperSideSquare a) p.2 :=
    (contDiffOn_upperSideSquare_strip a).contDiffAt
      (isOpen_Ioo.mem_nhds hpV)
  have hqV : ContDiffOn ℝ ∞
      (fun z : PlanePoint => upperSideSquare a z.2)
      sideModelNeighborhood := by
    exact (contDiffOn_upperSideSquare_strip a).comp contDiffOn_snd
      (fun _ hz => hz)
  exact squaredWidthDomain_regular_at_of_pos isOpen_sideModelNeighborhood hpV
    hqAt hqV heq hqpos

def bottomHalfPlane : Set PlanePoint :=
  {p | (-1 : ℝ) < p.2}

theorem isSmoothDomain_bottomHalfPlane :
    IsSmoothDomain bottomHalfPlane := by
  constructor
  · exact isOpen_lt continuous_const continuous_snd
  · intro p hp
    have heq : (-1 : ℝ) = p.2 :=
      frontier_lt_subset_eq continuous_const continuous_snd hp
    let g : PlanePoint → ℝ := fun z => -1 - z.2
    let D : PlanePoint →L[ℝ] ℝ :=
      -(ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hderiv : HasFDerivAt g D p := by
      simpa [g, D] using!
        (hasFDerivAt_const (x := p) (-1 : ℝ)).sub
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
    have hD : D ≠ 0 := by
      intro hzero
      have happ := congrArg
        (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hzero
      simp [D] at happ
    refine ⟨Set.univ, g, D, isOpen_univ, Set.mem_univ p,
      ?_, ?_, hderiv, hD, ?_⟩
    · dsimp [g]
      fun_prop
    · dsimp [g]
      linarith
    · ext z
      change (((-1 : ℝ) < z.2) ∧ True) ↔
        (True ∧ -1 - z.2 < 0)
      constructor
      · rintro ⟨hz, -⟩
        exact ⟨trivial, by linarith⟩
      · rintro ⟨-, hz⟩
        exact ⟨by linarith, trivial⟩

def bottomModelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam) : Set PlanePoint :=
  {p | p.1 ∈ Ioo (-a.sideHalfWidth) a.sideHalfWidth} ∩
    {p | p.2 ∈ Ioo (-(3 / 2 : ℝ)) (-(1 / 2 : ℝ))}

lemma isOpen_bottomModelNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    IsOpen (bottomModelNeighborhood a) :=
  (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage continuous_snd)

theorem interior_carrier_eq_bottomHalfPlane_on_bottomNeighborhood
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    interior a.carrier ∩ bottomModelNeighborhood a =
      bottomHalfPlane ∩ bottomModelNeighborhood a := by
  ext p
  constructor
  · rintro ⟨hp, hpV⟩
    exact ⟨interior_carrier_y_gt_neg_one a hp, hpV⟩
  · rintro ⟨hy, hpV⟩
    refine ⟨?_, hpV⟩
    have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hy, by linarith [hpV.2.2]⟩
    have hrad := upperSideRadicand_pos_of_mem_Ioo a hyStrip
    let root := √(upperSideRadicand a p.2)
    have hrootPos : 0 < root := Real.sqrt_pos.2 hrad
    have hwpos := a.sideHalfWidth_pos hh
    have habs : |p.1| < a.sideHalfWidth :=
      abs_lt.mpr hpV.1
    have hwidthAbs :
        |p.1| < a.sideHalfWidth + root := by linarith
    have hwidth :
        p.1 ^ 2 < (a.sideHalfWidth + root) ^ 2 := by
      rw [sq_lt_sq, abs_of_pos (add_pos hwpos hrootPos)]
      exact hwidthAbs
    apply (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).2
    simpa only [upperSideSquare, root] using hwidth

theorem interior_carrier_eq_upperCapDomain_above
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    interior a.carrier ∩ aboveUpperTransition =
      upperCapDomain a ∩ aboveUpperTransition := by
  ext p
  change (p ∈ interior a.carrier ∧ 1 < p.2) ↔
    (p.1 ^ 2 < upperCapSquare a p.2 ∧ 1 < p.2)
  constructor
  · rintro ⟨hp, hy⟩
    exact ⟨(mem_interior_carrier_iff_sq_lt_upperCapSquare_of_one_lt
      a p hy).1 hp, hy⟩
  · rintro ⟨hp, hy⟩
    exact ⟨(mem_interior_carrier_iff_sq_lt_upperCapSquare_of_one_lt
      a p hy).2 hp, hy⟩


def lowerChangeSupports
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set PlanePoint :=
  signedLowerChangeSupport a 1 epsilon ∪
    signedLowerChangeSupport a (-1) epsilon

lemma isClosed_lowerChangeSupports
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    IsClosed (lowerChangeSupports a epsilon) :=
  (isClosed_signedLowerChangeSupport a 1 epsilon).union
    (isClosed_signedLowerChangeSupport a (-1) epsilon)

theorem combinedSurgeryDomain_eq_upperSurgeryDomain_off_lowerSupports
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lower : epsilon ≤ lowerSafeScale a / 2)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    combinedSurgeryDomain a epsilon ∩ (lowerChangeSupports a epsilon)ᶜ =
      upperSurgeryDomain a epsilon ∩ (lowerChangeSupports a epsilon)ᶜ := by
  have hdiff :=
    combinedSurgeryDomain_sdiff_upperSurgeryDomain_subset_lowerSupports
      a hh hepsilon hepsilon_lower hepsilon_upper
  ext p
  constructor
  · rintro ⟨hp, hpOutside⟩
    refine ⟨?_, hpOutside⟩
    by_contra hpUpper
    exact hpOutside (hdiff ⟨hp, hpUpper⟩)
  · rintro ⟨hp, hpOutside⟩
    exact ⟨Or.inl hp, hpOutside⟩

private theorem upperSurgeryDomain_regular_at_away_lowerSupports
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_lower : epsilon ≤ lowerSafeScale a / 2)
    (hepsilon_upper : epsilon ≤ upperSafeScale a)
    {p : PlanePoint} (hp : p ∈ frontier (upperSurgeryDomain a epsilon))
    (hpRight : p ∉ signedLowerChangeSupport a 1 epsilon)
    (hpLeft : p ∉ signedLowerChangeSupport a (-1) epsilon) :
    ∃ (N : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiffOn ℝ ∞ g N ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧
      upperSurgeryDomain a epsilon ∩ N =
        N ∩ {q | g q < 0} := by
  by_cases hyBelow : p.2 < 1 - epsilon
  · have hpBelow : p ∈ belowUpperTransition epsilon := hyBelow
    have hbelow := upperSurgeryDomain_eq_interior_belowTransition
      a hepsilon hepsilon_upper
    have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
        belowUpperTransition epsilon := ⟨hp, hpBelow⟩
    rw [← frontier_inter_open_inter
      (isOpen_belowUpperTransition epsilon), hbelow,
      frontier_inter_open_inter (isOpen_belowUpperTransition epsilon)] at hpPair
    have hpInteriorFrontier := hpPair.1
    have hpCarrierFrontier :
        p ∈ frontier a.carrier :=
      frontier_interior_subset hpInteriorFrontier
    have hpCarrier : p ∈ a.carrier :=
      a.isClosed_carrier.frontier_subset hpCarrierFrontier
    have hyLower : (-1 : ℝ) ≤ p.2 :=
      carrier_y_ge_neg_one a hpCarrier
    by_cases hyBottom : p.2 = -1
    · have hle :=
        (mem_carrier_iff_sq_le_upperSideSquare a p
          ⟨by rw [hyBottom], by rw [hyBottom]; norm_num⟩).1 hpCarrier
      have hrad : upperSideRadicand a (-1) = 0 := by
        unfold upperSideRadicand
        ring
      have hxSq : p.1 ^ 2 ≤ a.sideHalfWidth ^ 2 := by
        rw [hyBottom, upperSideSquare, hrad, Real.sqrt_zero, add_zero] at hle
        exact hle
      have hxAbs : |p.1| ≤ a.sideHalfWidth :=
        (sq_le_sq₀ (abs_nonneg p.1) a.sideHalfWidth_nonneg).1
          (by simpa only [sq_abs] using hxSq)
      have hxNeRight : p.1 ≠ a.sideHalfWidth := by
        intro hx
        apply hpRight
        rw [signedLowerChangeSupport]
        constructor
        · change signedLowerOutwardCoordinate a 1 p ∈
            Icc 0 (2 * epsilon / 3)
          norm_num [signedLowerOutwardCoordinate, hx]
          nlinarith
        · change p.2 ∈ Icc (-1 : ℝ) (-1 + 2 * epsilon / 3)
          rw [hyBottom]
          constructor <;> nlinarith
      have hxNeLeft : p.1 ≠ -a.sideHalfWidth := by
        intro hx
        apply hpLeft
        rw [signedLowerChangeSupport]
        constructor
        · change signedLowerOutwardCoordinate a (-1) p ∈
            Icc 0 (2 * epsilon / 3)
          norm_num [signedLowerOutwardCoordinate, hx]
          nlinarith
        · change p.2 ∈ Icc (-1 : ℝ) (-1 + 2 * epsilon / 3)
          rw [hyBottom]
          constructor <;> nlinarith
      have hxBounds := abs_le.mp hxAbs
      have hpBottom : p ∈ bottomModelNeighborhood a := by
        exact ⟨⟨lt_of_le_of_ne hxBounds.1 (Ne.symm hxNeLeft),
          lt_of_le_of_ne hxBounds.2 hxNeRight⟩,
          ⟨by rw [hyBottom]; norm_num, by rw [hyBottom]; norm_num⟩⟩
      have hbottom :=
        regularBoundaryCertificate_of_local_eq_of_smooth
          (isOpen_bottomModelNeighborhood a) hpBottom
          (interior_carrier_eq_bottomHalfPlane_on_bottomNeighborhood a hh)
          hpInteriorFrontier isSmoothDomain_bottomHalfPlane
      exact regularBoundaryCertificate_of_local_eq
        (isOpen_belowUpperTransition epsilon) hpBelow hbelow hp hbottom
    · have hySide : (-1 : ℝ) < p.2 :=
        lt_of_le_of_ne hyLower (Ne.symm hyBottom)
      have hpSideV : p ∈ sideModelNeighborhood :=
        ⟨hySide, by linarith [hyBelow, hepsilon]⟩
      have hsideLocal :=
        interior_carrier_eq_sideWidthDomain_on_strip a
      have hpSidePair : p ∈ frontier (interior a.carrier) ∩
          sideModelNeighborhood :=
        ⟨hpInteriorFrontier, hpSideV⟩
      rw [← frontier_inter_open_inter isOpen_sideModelNeighborhood,
        hsideLocal, frontier_inter_open_inter isOpen_sideModelNeighborhood]
        at hpSidePair
      have hsideModel :=
        sideWidthDomain_regular_at a hh hpSidePair.1 hpSideV
      have hinterior :=
        regularBoundaryCertificate_of_local_eq
          isOpen_sideModelNeighborhood hpSideV hsideLocal
          hpInteriorFrontier hsideModel
      exact regularBoundaryCertificate_of_local_eq
        (isOpen_belowUpperTransition epsilon) hpBelow hbelow hp hinterior
  · by_cases hyAbove : 1 < p.2
    · have hpAbove : p ∈ aboveUpperTransition := hyAbove
      have habove := upperSurgeryDomain_eq_interior_aboveTransition
        a hepsilon hepsilon_upper
      have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
          aboveUpperTransition := ⟨hp, hpAbove⟩
      rw [← frontier_inter_open_inter isOpen_aboveUpperTransition,
        habove, frontier_inter_open_inter isOpen_aboveUpperTransition] at hpPair
      have hinterior :=
        regularBoundaryCertificate_of_local_eq_of_smooth
          isOpen_aboveUpperTransition hpAbove
          (interior_carrier_eq_upperCapDomain_above a)
          hpPair.1 (isSmoothDomain_upperCapDomain a)
      exact regularBoundaryCertificate_of_local_eq
        isOpen_aboveUpperTransition hpAbove habove hp hinterior
    · have hyCore : p.2 ∈ Icc (1 - epsilon) 1 :=
        ⟨le_of_not_gt hyBelow, le_of_not_gt hyAbove⟩
      have hpV : p ∈ upperModelNeighborhood epsilon := by
        exact ⟨by linarith [hyCore.1, hepsilon],
          by linarith [hyCore.2, hepsilon]⟩
      have hlocal :=
        upperSurgeryDomain_eq_upperBlend_on_modelNeighborhood a hepsilon
      have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
          upperModelNeighborhood epsilon := ⟨hp, hpV⟩
      rw [← frontier_inter_open_inter
        (isOpen_upperModelNeighborhood epsilon), hlocal,
        frontier_inter_open_inter (isOpen_upperModelNeighborhood epsilon)]
        at hpPair
      have hqContinuous : Continuous (upperBlendQ a epsilon) := by
        unfold upperBlendQ upperSideSquare upperSideRadicand upperCapSquare
          TypeThreeAssembly.upperCenter upperJunctionWeight
        fun_prop
      have heq : p.1 ^ 2 = upperBlendQ a epsilon p.2 := by
        apply frontier_lt_subset_eq (continuous_fst.pow 2)
          (hqContinuous.comp continuous_snd)
        simpa [upperBlendDomain] using hpPair.1
      let t : ℝ := (p.2 - (1 - epsilon)) / epsilon
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor
        · exact div_nonneg (sub_nonneg.mpr hyCore.1) hepsilon.le
        · rw [div_le_one hepsilon]
          linarith [hyCore.2]
      have hheight : upperJunctionHeight epsilon t = p.2 := by
        unfold upperJunctionHeight t
        field_simp [hepsilon.ne']
        ring
      have hqpos : 0 < upperBlendQ a epsilon p.2 := by
        have hnorm := upperNormalizedQ_pos a hepsilon hepsilon_upper ht
        unfold upperNormalizedQ at hnorm
        rwa [hheight] at hnorm
      have hpCollar : p.2 ∈
          Ioo (1 - 2 * upperSafeScale a)
            (1 + 2 * upperSafeScale a) := by
        constructor <;> nlinarith [hyCore.1, hyCore.2,
          hepsilon_upper, upperSafeScale_pos a]
      have hqAt : ContDiffAt ℝ ∞ (upperBlendQ a epsilon) p.2 :=
        (contDiffOn_upperBlendQ a epsilon).contDiffAt
          (isOpen_Ioo.mem_nhds hpCollar)
      have hqV : ContDiffOn ℝ ∞
          (fun z : PlanePoint => upperBlendQ a epsilon z.2)
          (upperModelNeighborhood epsilon) := by
        exact (contDiffOn_upperBlendQ a epsilon).comp contDiffOn_snd
          (fun z hz => by
            constructor <;> nlinarith [hz.1, hz.2, hepsilon_upper,
              upperSafeScale_pos a])
      have hmodel0 := squaredWidthDomain_regular_at_of_pos
        (isOpen_upperModelNeighborhood epsilon) hpV hqAt hqV heq hqpos
      have hmodel :
          ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
              (D : PlanePoint →L[ℝ] ℝ),
            IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
            HasFDerivAt g D p ∧ D ≠ 0 ∧
            upperBlendDomain a epsilon ∩ W =
              W ∩ {z | g z < 0} := by
        simpa [upperBlendDomain, squaredWidthDomain] using hmodel0
      exact regularBoundaryCertificate_of_local_eq
        (isOpen_upperModelNeighborhood epsilon) hpV hlocal hp hmodel



/-- The complete nondegenerate surgery is a smooth open domain.  The proof
uses the lower graph models exactly on their closed change supports and the
unchanged side, bottom, upper-blend, and cap models everywhere else. -/
theorem isSmoothDomain_combinedSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ combinedSafeScale a / 2) :
    IsSmoothDomain (combinedSurgeryDomain a epsilon) := by
  have hepsilon_lower : epsilon ≤ lowerSafeScale a / 2 := by
    have hle := combinedSafeScale_le_lower a
    nlinarith
  have hepsilon_upper : epsilon ≤ upperSafeScale a := by
    have hle := combinedSafeScale_le_upper a
    have hs0 := (combinedSafeScale_pos a hh).le
    nlinarith
  constructor
  · exact isOpen_combinedSurgeryDomain a epsilon
  · intro p hp
    by_cases hpRight : p ∈ signedLowerChangeSupport a 1 epsilon
    · have hpV : p ∈ signedLowerModelNeighborhood a 1 epsilon :=
        signedLowerChangeSupport_subset_modelNeighborhood
          a hepsilon hepsilon_lower hpRight
      have hlocal :=
        combinedSurgeryDomain_eq_rightLowerLocal_on_modelNeighborhood
          a hh hepsilon hepsilon_lower hepsilon_upper
      have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
          signedLowerModelNeighborhood a 1 epsilon := ⟨hp, hpV⟩
      rw [← frontier_inter_open_inter
        (isOpen_signedLowerModelNeighborhood a 1 epsilon), hlocal,
        frontier_inter_open_inter
          (isOpen_signedLowerModelNeighborhood a 1 epsilon)] at hpPair
      have hgraphContinuous : Continuous (fun z : PlanePoint =>
          lowerContactGraph a epsilon
            (signedLowerOutwardCoordinate a 1 z)) := by
        unfold lowerContactGraph lowerContactWeight lowerCircleRise
          signedLowerOutwardCoordinate
        fun_prop
      have heq : lowerContactGraph a epsilon
          (signedLowerOutwardCoordinate a 1 p) = p.2 := by
        apply frontier_lt_subset_eq hgraphContinuous continuous_snd
        simpa [signedLowerLocalDomain] using hpPair.1
      have hpGraph : p ∈ signedLowerGraphNeighborhood a 1 := by
        change signedLowerOutwardCoordinate a 1 p ∈
          Ioo (-a.radius) a.radius
        have hcoord := hpRight.1
        have hscale := lowerSafeScale_le_radius_quarter a
        constructor <;>
          nlinarith [hcoord.1, hcoord.2, hepsilon_lower, hscale,
            a.radius_pos]
      have hmodel :=
        signedLowerLocalDomain_regular_at a 1 epsilon hpGraph heq
      exact regularBoundaryCertificate_of_local_eq
        (isOpen_signedLowerModelNeighborhood a 1 epsilon)
        hpV hlocal hp hmodel
    · by_cases hpLeft : p ∈ signedLowerChangeSupport a (-1) epsilon
      · have hpV : p ∈ signedLowerModelNeighborhood a (-1) epsilon :=
          signedLowerChangeSupport_subset_modelNeighborhood
            a hepsilon hepsilon_lower hpLeft
        have hlocal :=
          combinedSurgeryDomain_eq_leftLowerLocal_on_modelNeighborhood
            a hh hepsilon hepsilon_lower hepsilon_upper
        have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
            signedLowerModelNeighborhood a (-1) epsilon := ⟨hp, hpV⟩
        rw [← frontier_inter_open_inter
          (isOpen_signedLowerModelNeighborhood a (-1) epsilon), hlocal,
          frontier_inter_open_inter
            (isOpen_signedLowerModelNeighborhood a (-1) epsilon)] at hpPair
        have hgraphContinuous : Continuous (fun z : PlanePoint =>
            lowerContactGraph a epsilon
              (signedLowerOutwardCoordinate a (-1) z)) := by
          unfold lowerContactGraph lowerContactWeight lowerCircleRise
            signedLowerOutwardCoordinate
          fun_prop
        have heq : lowerContactGraph a epsilon
            (signedLowerOutwardCoordinate a (-1) p) = p.2 := by
          apply frontier_lt_subset_eq hgraphContinuous continuous_snd
          simpa [signedLowerLocalDomain] using hpPair.1
        have hpGraph : p ∈ signedLowerGraphNeighborhood a (-1) := by
          change signedLowerOutwardCoordinate a (-1) p ∈
            Ioo (-a.radius) a.radius
          have hcoord := hpLeft.1
          have hscale := lowerSafeScale_le_radius_quarter a
          constructor <;>
            nlinarith [hcoord.1, hcoord.2, hepsilon_lower, hscale,
              a.radius_pos]
        have hmodel :=
          signedLowerLocalDomain_regular_at a (-1) epsilon hpGraph heq
        exact regularBoundaryCertificate_of_local_eq
          (isOpen_signedLowerModelNeighborhood a (-1) epsilon)
          hpV hlocal hp hmodel
      · have hpOutside : p ∈ (lowerChangeSupports a epsilon)ᶜ := by
          exact fun hpSupport => hpSupport.elim hpRight hpLeft
        have hlocal :=
          combinedSurgeryDomain_eq_upperSurgeryDomain_off_lowerSupports
            a hh hepsilon hepsilon_lower hepsilon_upper
        have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
            (lowerChangeSupports a epsilon)ᶜ := ⟨hp, hpOutside⟩
        have hopen : IsOpen ((lowerChangeSupports a epsilon)ᶜ) :=
          (isClosed_lowerChangeSupports a epsilon).isOpen_compl
        rw [← frontier_inter_open_inter hopen, hlocal,
          frontier_inter_open_inter hopen] at hpPair
        have hmodel :=
          upperSurgeryDomain_regular_at_away_lowerSupports
            a hh hepsilon hepsilon_lower hepsilon_upper hpPair.1
              hpRight hpLeft
        exact regularBoundaryCertificate_of_local_eq
          hopen hpOutside hlocal hp hmodel

/-- Scales used by the actual smooth nondegenerate recovery sequence.  The
factor `1/2` keeps every buffered lower graph inside `lowerSafeScale`. -/
def smoothCombinedRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) : ℝ :=
  combinedRecoveryScale a n / 2

lemma smoothCombinedRecoveryScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) (n : ℕ) :
    0 < smoothCombinedRecoveryScale a n :=
  div_pos (combinedRecoveryScale_pos a hh n) (by norm_num)

lemma smoothCombinedRecoveryScale_le
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) :
    smoothCombinedRecoveryScale a n ≤ combinedSafeScale a / 2 :=
  div_le_div_of_nonneg_right (combinedRecoveryScale_le a n) (by norm_num)

lemma tendsto_smoothCombinedRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Tendsto (smoothCombinedRecoveryScale a) atTop (𝓝 0) := by
  unfold smoothCombinedRecoveryScale
  simpa only [zero_div] using
    (tendsto_combinedRecoveryScale a).div_const 2

/-- Actual smooth recovery sequence for either nonsemicircular branch. -/
def nondegenerateRecoverySequence
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    SmoothSequence where
  carrier n := combinedSurgeryDomain a (smoothCombinedRecoveryScale a n)
  smooth n := isSmoothDomain_combinedSurgeryDomain a hh
    (smoothCombinedRecoveryScale_pos a hh n)
    (smoothCombinedRecoveryScale_le a n)

theorem nondegenerateRecoverySequence_converges_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    (nondegenerateRecoverySequence a hh).ConvergesTo a.carrier := by
  unfold SmoothSequence.ConvergesTo
  have hbound : Tendsto
      (fun n : ℕ => ENNReal.ofReal
        ((4 * upperHorizontalRadius a + 4) *
          smoothCombinedRecoveryScale a n))
      atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ => (4 * upperHorizontalRadius a + 4) *
          smoothCombinedRecoveryScale a n)
        atTop (𝓝 ((4 * upperHorizontalRadius a + 4) * 0)) :=
      tendsto_const_nhds.mul (tendsto_smoothCombinedRecoveryScale a)
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n =>
      characteristicDistance_combinedSurgeryDomain_carrier_le a
        (smoothCombinedRecoveryScale_pos a hh n)
        (by
          have hscale := smoothCombinedRecoveryScale_le a n
          have hs := combinedSafeScale_pos a hh
          have hhalf : combinedSafeScale a / 2 ≤ combinedSafeScale a := by
            nlinarith
          exact (hscale.trans hhalf).trans (combinedSafeScale_le_lower a))
        (by
          have hscale := smoothCombinedRecoveryScale_le a n
          have hs := combinedSafeScale_pos a hh
          have hhalf : combinedSafeScale a / 2 ≤ combinedSafeScale a := by
            nlinarith
          exact (hscale.trans hhalf).trans (combinedSafeScale_le_upper a)))


/-- Branch-complete recovery: the exact open disk at the semicircular
transition and the glued surgery on both nondegenerate branches. -/
def typeThreeRecoverySequence
    {lam : ℝ} (a : TypeThreeAssembly lam) : SmoothSequence :=
  if hh : a.h = 1 / 2 then
    semicircularDiskConstantSequence
  else
    nondegenerateRecoverySequence a hh

theorem typeThreeRecoverySequence_converges_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    (typeThreeRecoverySequence a).ConvergesTo a.carrier := by
  by_cases hh : a.h = 1 / 2
  · simp only [typeThreeRecoverySequence, dif_pos hh]
    exact semicircularDiskConstantSequence_converges_carrier a hh
  · simp only [typeThreeRecoverySequence, dif_neg hh]
    exact nondegenerateRecoverySequence_converges_carrier a hh

end CMVRelaxation.TypeThreeRecovery
