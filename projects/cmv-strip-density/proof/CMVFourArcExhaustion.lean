/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRightSideExhaustion

/-!
# Closed-curvature four-arc projection exhaustion

Axis reflections transport the shared candidate-level upper-cap and right-side
tangent patches to the lower cap and left side for `0 < h ≤ 1`. Strict region
localization makes all four finite families pairwise disjoint, so one
finite-summation application charges the actual complete-frontier payoff to
one global smooth cost.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section

namespace CMVRelaxation

/-- Reflection across the vertical source axis. -/
def verticalAxisReflection : EuclideanPlane ≃ᵢ EuclideanPlane :=
  tangentComplexEquiv.trans <|
    Complex.conjLIE.toIsometryEquiv.trans tangentComplexEquiv.symm

/-- Reflection across the horizontal source axis. -/
def horizontalAxisReflection : EuclideanPlane ≃ᵢ EuclideanPlane :=
  tangentComplexEquiv.trans <|
    (Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)).toIsometryEquiv.trans
      tangentComplexEquiv.symm

@[simp] theorem euclideanRigidMap_verticalAxisReflection (p : PlanePoint) :
    euclideanRigidMap verticalAxisReflection p = (-p.1, p.2) := by
  apply planeEuclideanHomeomorph.injective
  change tangentComplexEquiv.symm ((starRingEnd ℂ) ⟨p.2, p.1⟩) =
    WithLp.toLp 2 (-p.1, p.2)
  change WithLp.toLp 2 (-p.1, p.2) = WithLp.toLp 2 (-p.1, p.2)
  rfl

@[simp] theorem euclideanRigidMap_horizontalAxisReflection (p : PlanePoint) :
    euclideanRigidMap horizontalAxisReflection p = (p.1, -p.2) := by
  apply planeEuclideanHomeomorph.injective
  change tangentComplexEquiv.symm (-((starRingEnd ℂ) ⟨p.2, p.1⟩)) =
    WithLp.toLp 2 (p.1, -p.2)
  rw [tangentComplexEquiv_symm_apply]
  simp

@[simp] theorem euclideanRigidMap_trans
    (e f : EuclideanPlane ≃ᵢ EuclideanPlane) (p : PlanePoint) :
    euclideanRigidMap (e.trans f) p =
      euclideanRigidMap f (euclideanRigidMap e p) := by
  rfl

end CMVRelaxation


namespace CMVRelaxation

namespace RigidProjectionPatch

variable {lam : ℝ} {E : Set PlanePoint}

/-- Postcompose a patch frame with a rigid symmetry preserving the carrier and
strip density. -/
noncomputable def postcompose
    (P : RigidProjectionPatch lam E)
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : ∀ p, euclideanRigidMap e p ∈ E ↔ p ∈ E)
    (hdensity : ∀ p, StripDensity lam (euclideanRigidMap e p) =
      StripDensity lam p) :
    RigidProjectionPatch lam E where
  frame := P.frame.trans e
  a := P.a
  b := P.b
  y₀ := P.y₀
  rho := P.rho
  weight := P.weight
  rho_pos := P.rho_pos
  lower_collar := by
    rintro _ ⟨p, hp, rfl⟩
    rw [euclideanRigidMap_trans]
    exact (hE _).2 (P.lower_collar ⟨p, hp, rfl⟩)
  upper_collar := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hmem
    rw [euclideanRigidMap_trans] at hmem
    exact (Set.disjoint_left.mp P.upper_collar)
      ⟨p, hp, rfl⟩ ((hE _).1 hmem)
  density_lower := by
    rintro _ ⟨p, hp, rfl⟩
    rw [euclideanRigidMap_trans, hdensity]
    exact P.density_lower _ ⟨p, hp, rfl⟩

theorem window_postcompose
    (P : RigidProjectionPatch lam E)
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : ∀ p, euclideanRigidMap e p ∈ E ↔ p ∈ E)
    (hdensity : ∀ p, StripDensity lam (euclideanRigidMap e p) =
      StripDensity lam p) :
    (P.postcompose e hE hdensity).window =
      euclideanRigidMap e '' P.window := by
  ext q
  simp only [window, rigidProjectionBox, postcompose, Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨euclideanRigidMap P.frame p, ⟨p, hp, rfl⟩,
      (euclideanRigidMap_trans P.frame e p).symm⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, euclideanRigidMap_trans P.frame e p⟩

@[simp] theorem payoff_postcompose
    (P : RigidProjectionPatch lam E)
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : ∀ p, euclideanRigidMap e p ∈ E ↔ p ∈ E)
    (hdensity : ∀ p, StripDensity lam (euclideanRigidMap e p) =
      StripDensity lam p) :
    (P.postcompose e hE hdensity).payoff = P.payoff := by
  rfl

@[simp] theorem errorCoefficient_postcompose
    (P : RigidProjectionPatch lam E)
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : ∀ p, euclideanRigidMap e p ∈ E ↔ p ∈ E)
    (hdensity : ∀ p, StripDensity lam (euclideanRigidMap e p) =
      StripDensity lam p) :
    (P.postcompose e hE hdensity).errorCoefficient =
      P.errorCoefficient := by
  rfl

end RigidProjectionPatch

namespace CandidatePatchReflection

variable {lam : ℝ} (candidate : FourArcCandidate lam)

private theorem vertical_carrier (p : PlanePoint) :
    euclideanRigidMap verticalAxisReflection p ∈ candidate.assembly.carrier ↔
      p ∈ candidate.assembly.carrier := by
  simpa using candidate.mem_assembly_carrier_vertical_reflection p

private theorem horizontal_carrier (p : PlanePoint) :
    euclideanRigidMap horizontalAxisReflection p ∈ candidate.assembly.carrier ↔
      p ∈ candidate.assembly.carrier := by
  simpa using candidate.mem_assembly_carrier_horizontal_reflection p

private theorem vertical_density (p : PlanePoint) :
    StripDensity lam (euclideanRigidMap verticalAxisReflection p) =
      StripDensity lam p := by
  simp [StripDensity]

private theorem horizontal_density (p : PlanePoint) :
    StripDensity lam (euclideanRigidMap horizontalAxisReflection p) =
      StripDensity lam p := by
  simp [StripDensity]

noncomputable def vertical
    (P : RigidProjectionPatch lam candidate.assembly.carrier) :
    RigidProjectionPatch lam candidate.assembly.carrier :=
  P.postcompose verticalAxisReflection (vertical_carrier candidate)
    vertical_density

noncomputable def horizontal
    (P : RigidProjectionPatch lam candidate.assembly.carrier) :
    RigidProjectionPatch lam candidate.assembly.carrier :=
  P.postcompose horizontalAxisReflection (horizontal_carrier candidate)
    horizontal_density

theorem window_vertical
    (P : RigidProjectionPatch lam candidate.assembly.carrier) :
    (vertical candidate P).window =
      (fun p : PlanePoint => (-p.1, p.2)) '' P.window := by
  rw [vertical, RigidProjectionPatch.window_postcompose]
  simp only [euclideanRigidMap_verticalAxisReflection]

theorem window_horizontal
    (P : RigidProjectionPatch lam candidate.assembly.carrier) :
    (horizontal candidate P).window =
      (fun p : PlanePoint => (p.1, -p.2)) '' P.window := by
  rw [horizontal, RigidProjectionPatch.window_postcompose]
  simp only [euclideanRigidMap_horizontalAxisReflection]

end CandidatePatchReflection

namespace CandidateLowerCap

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Reflection of the upper-cap exhaustion onto the actual lower cap, valid on
the complete closed-curvature candidate range. -/
theorem exists_lowerCap_patch_family
    (hlam : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
        RigidProjectionPatch lam candidate.assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = lam) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | p.2 < -1}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (lam * candidate.assembly.lowerCap.arcLength) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta := by
  obtain ⟨N, P, hN, hweight, hloc, hpair, herr, hpay, _⟩ :=
    FourArcUpperCap.exists_upperCap_patch_family_and_bound
      candidate hlam heta
  let Q : Fin N → RigidProjectionPatch lam candidate.assembly.carrier :=
    fun i => CandidatePatchReflection.horizontal candidate (P i)
  have hreflect_injective :
      Function.Injective (fun p : PlanePoint => (p.1, -p.2)) := by
    intro p q h
    injection h with hfst hsnd
    exact Prod.ext hfst (neg_injective hsnd)
  refine ⟨N, Q, hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hweight i
  · intro i q hq
    rw [CandidatePatchReflection.window_horizontal] at hq
    rcases hq with ⟨p, hp, rfl⟩
    have hpabove := hloc i hp
    change 1 < p.2 at hpabove
    change -p.2 < -1
    linarith
  · intro i _ j _ hij
    dsimp only [Function.onFun, Q]
    rw [CandidatePatchReflection.window_horizontal,
      CandidatePatchReflection.window_horizontal]
    exact Set.disjoint_image_of_injective hreflect_injective
      (hpair (Set.mem_univ i) (Set.mem_univ j) hij)
  · simpa only [Q, CandidatePatchReflection.horizontal,
      RigidProjectionPatch.errorCoefficient_postcompose] using herr
  · have hcap :
        candidate.assembly.lowerCap.arcLength =
          candidate.assembly.upperCap.arcLength := by
      rfl
    rw [hcap]
    simpa only [Q, CandidatePatchReflection.horizontal,
      RigidProjectionPatch.payoff_postcompose] using hpay

end CandidateLowerCap

namespace CandidateLeftSide

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Reflection of the right-side exhaustion onto the actual left side, valid
on the complete closed-curvature candidate range. -/
theorem exists_leftSide_patch_family
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
        RigidProjectionPatch lam candidate.assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = 1) ∧
      (∀ i, (P i).window ⊆
        {p : PlanePoint | p.1 < -candidate.capChord / 2 ∧ |p.2| < 1}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (coreArcEnd candidate.stripCore -
            coreArcStart candidate.stripCore) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta := by
  obtain ⟨N, P, hN, hweight, hloc, hpair, herr, hpay, _⟩ :=
    FourArcRightSide.exists_rightSide_patch_family_and_bound candidate heta
  let Q : Fin N → RigidProjectionPatch lam candidate.assembly.carrier :=
    fun i => CandidatePatchReflection.vertical candidate (P i)
  have hreflect_injective :
      Function.Injective (fun p : PlanePoint => (-p.1, p.2)) := by
    intro p q h
    injection h with hfst hsnd
    exact Prod.ext (neg_injective hfst) hsnd
  refine ⟨N, Q, hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hweight i
  · intro i q hq
    rw [CandidatePatchReflection.window_vertical] at hq
    rcases hq with ⟨p, hp, rfl⟩
    have hposition := hloc i hp
    exact ⟨by linarith [hposition.1], hposition.2⟩
  · intro i _ j _ hij
    dsimp only [Function.onFun, Q]
    rw [CandidatePatchReflection.window_vertical,
      CandidatePatchReflection.window_vertical]
    exact Set.disjoint_image_of_injective hreflect_injective
      (hpair (Set.mem_univ i) (Set.mem_univ j) hij)
  · simpa only [Q, CandidatePatchReflection.vertical,
      RigidProjectionPatch.errorCoefficient_postcompose] using herr
  · simpa only [Q, CandidatePatchReflection.vertical,
      RigidProjectionPatch.payoff_postcompose] using hpay

end CandidateLeftSide

namespace CandidateFourArc

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Disjoint-sum index for upper, lower, right, and left patch families. -/
abbrev PatchIndex (Nu Nd Nr Nl : ℕ) :=
  Sum (Fin Nu) (Sum (Fin Nd) (Sum (Fin Nr) (Fin Nl)))

/-- One family containing all four literal candidate frontier pieces. -/
def combinedPatch {Nu Nd Nr Nl : ℕ}
    (Pu : Fin Nu → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pd : Fin Nd → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pr : Fin Nr → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pl : Fin Nl → RigidProjectionPatch lam candidate.assembly.carrier) :
    PatchIndex Nu Nd Nr Nl →
      RigidProjectionPatch lam candidate.assembly.carrier
  | Sum.inl i => Pu i
  | Sum.inr (Sum.inl i) => Pd i
  | Sum.inr (Sum.inr (Sum.inl i)) => Pr i
  | Sum.inr (Sum.inr (Sum.inr i)) => Pl i

private theorem capChordHalf_pos : 0 < candidate.capChord / 2 :=
  div_pos candidate.capChord_pos (by norm_num)

theorem combinedPatch_pairwise
    {Nu Nd Nr Nl : ℕ}
    (Pu : Fin Nu → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pd : Fin Nd → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pr : Fin Nr → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pl : Fin Nl → RigidProjectionPatch lam candidate.assembly.carrier)
    (hu : ∀ i, (Pu i).window ⊆ {p : PlanePoint | 1 < p.2})
    (hd : ∀ i, (Pd i).window ⊆ {p : PlanePoint | p.2 < -1})
    (hr : ∀ i, (Pr i).window ⊆
      {p : PlanePoint | candidate.capChord / 2 < p.1 ∧ |p.2| < 1})
    (hl : ∀ i, (Pl i).window ⊆
      {p : PlanePoint | p.1 < -candidate.capChord / 2 ∧ |p.2| < 1})
    (hpu : Set.Pairwise (Set.univ : Set (Fin Nu))
      (Function.onFun Disjoint fun i => (Pu i).window))
    (hpd : Set.Pairwise (Set.univ : Set (Fin Nd))
      (Function.onFun Disjoint fun i => (Pd i).window))
    (hpr : Set.Pairwise (Set.univ : Set (Fin Nr))
      (Function.onFun Disjoint fun i => (Pr i).window))
    (hpl : Set.Pairwise (Set.univ : Set (Fin Nl))
      (Function.onFun Disjoint fun i => (Pl i).window)) :
    Set.Pairwise (Set.univ : Set (PatchIndex Nu Nd Nr Nl))
      (Function.onFun Disjoint fun i =>
        (combinedPatch candidate Pu Pd Pr Pl i).window) := by
  have hUD : ∀ i j, Disjoint (Pu i).window (Pd j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpu' hpd'
    have hup := hu i hpu'
    have hdown := hd j hpd'
    change 1 < p.2 at hup
    change p.2 < -1 at hdown
    linarith
  have hUR : ∀ i j, Disjoint (Pu i).window (Pr j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpu' hpr'
    have hup := hu i hpu'
    have hright := hr j hpr'
    change 1 < p.2 at hup
    change candidate.capChord / 2 < p.1 ∧ |p.2| < 1 at hright
    linarith [le_abs_self p.2]
  have hUL : ∀ i j, Disjoint (Pu i).window (Pl j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpu' hpl'
    have hup := hu i hpu'
    have hleft := hl j hpl'
    change 1 < p.2 at hup
    change p.1 < -candidate.capChord / 2 ∧ |p.2| < 1 at hleft
    linarith [le_abs_self p.2]
  have hDR : ∀ i j, Disjoint (Pd i).window (Pr j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpd' hpr'
    have hdown := hd i hpd'
    have hright := hr j hpr'
    change p.2 < -1 at hdown
    change candidate.capChord / 2 < p.1 ∧ |p.2| < 1 at hright
    have hneg := neg_le_abs p.2
    linarith
  have hDL : ∀ i j, Disjoint (Pd i).window (Pl j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpd' hpl'
    have hdown := hd i hpd'
    have hleft := hl j hpl'
    change p.2 < -1 at hdown
    change p.1 < -candidate.capChord / 2 ∧ |p.2| < 1 at hleft
    have hneg := neg_le_abs p.2
    linarith
  have hRL : ∀ i j, Disjoint (Pr i).window (Pl j).window := by
    intro i j
    rw [Set.disjoint_left]
    intro p hpr' hpl'
    have hright := hr i hpr'
    have hleft := hl j hpl'
    change candidate.capChord / 2 < p.1 ∧ |p.2| < 1 at hright
    change p.1 < -candidate.capChord / 2 ∧ |p.2| < 1 at hleft
    linarith [capChordHalf_pos candidate]
  intro i _ j _ hij
  rcases i with iu | irest
  · rcases j with ju | jrest
    · exact hpu (Set.mem_univ iu) (Set.mem_univ ju) (by
        intro h
        subst ju
        exact hij rfl)
    · rcases jrest with jd | jrest
      · exact hUD iu jd
      · rcases jrest with jr | jl
        · exact hUR iu jr
        · exact hUL iu jl
  · rcases irest with id | irest
    · rcases j with ju | jrest
      · exact (hUD ju id).symm
      · rcases jrest with jd | jrest
        · exact hpd (Set.mem_univ id) (Set.mem_univ jd) (by
            intro h
            subst jd
            exact hij rfl)
        · rcases jrest with jr | jl
          · exact hDR id jr
          · exact hDL id jl
    · rcases irest with ir | il
      · rcases j with ju | jrest
        · exact (hUR ju ir).symm
        · rcases jrest with jd | jrest
          · exact (hDR jd ir).symm
          · rcases jrest with jr | jl
            · exact hpr (Set.mem_univ ir) (Set.mem_univ jr) (by
                intro h
                subst jr
                exact hij rfl)
            · exact hRL ir jl
      · rcases j with ju | jrest
        · exact (hUL ju il).symm
        · rcases jrest with jd | jrest
          · exact (hDL jd il).symm
          · rcases jrest with jr | jl
            · exact (hRL jr il).symm
            · exact hpl (Set.mem_univ il) (Set.mem_univ jl) (by
                intro h
                subst jl
                exact hij rfl)

theorem sum_combinedPatch_payoff
    {Nu Nd Nr Nl : ℕ}
    (Pu : Fin Nu → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pd : Fin Nd → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pr : Fin Nr → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pl : Fin Nl → RigidProjectionPatch lam candidate.assembly.carrier) :
    (∑ i : PatchIndex Nu Nd Nr Nl,
      (combinedPatch candidate Pu Pd Pr Pl i).payoff) =
      (∑ i, (Pu i).payoff) + (∑ i, (Pd i).payoff) +
        (∑ i, (Pr i).payoff) + (∑ i, (Pl i).payoff) := by
  simp [PatchIndex, combinedPatch, add_assoc]

theorem sum_combinedPatch_errorCoefficient
    {Nu Nd Nr Nl : ℕ}
    (Pu : Fin Nu → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pd : Fin Nd → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pr : Fin Nr → RigidProjectionPatch lam candidate.assembly.carrier)
    (Pl : Fin Nl → RigidProjectionPatch lam candidate.assembly.carrier) :
    (∑ i : PatchIndex Nu Nd Nr Nl,
      (combinedPatch candidate Pu Pd Pr Pl i).errorCoefficient) =
      (∑ i, (Pu i).errorCoefficient) +
        (∑ i, (Pd i).errorCoefficient) +
        (∑ i, (Pr i).errorCoefficient) +
        (∑ i, (Pl i).errorCoefficient) := by
  simp [PatchIndex, combinedPatch, add_assoc]

theorem frontierWeightedPerimeter_eq_four_components :
    _root_.WeightedPerimeter lam
        (FrontierMeasure candidate.assembly.carrier) =
      lam * candidate.assembly.upperCap.arcLength +
        lam * candidate.assembly.lowerCap.arcLength +
        (coreArcEnd candidate.stripCore -
          coreArcStart candidate.stripCore) +
        (coreArcEnd candidate.stripCore -
          coreArcStart candidate.stripCore) := by
  have hside :
      coreArcEnd candidate.stripCore -
          coreArcStart candidate.stripCore =
        2 * ell candidate.stripCore.sideAngle := by
    unfold coreArcEnd coreArcStart StripCore.radius ell
    rw [candidate.stripCore.sin_sideAngle]
    field_simp [candidate.stripCore.curvature_pos.ne']
    ring
  rw [← fourArc_frontier_weightedPerimeter_eq,
    FourArcAssembly.weightedPerimeter_formula]
  change candidate.stripCore.boundaryArcLength +
      lam * (candidate.assembly.upperCap.arcLength +
        candidate.assembly.lowerCap.arcLength) = _
  rw [StripCore.boundaryArcLength, hside]
  ring

theorem extendedFrontierCost_eq_four_components
    (hlam : 1 < lam) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) =
      ENNReal.ofReal
          (lam * candidate.assembly.upperCap.arcLength) +
        ENNReal.ofReal
          (lam * candidate.assembly.lowerCap.arcLength) +
        ENNReal.ofReal
          (coreArcEnd candidate.stripCore -
            coreArcStart candidate.stripCore) +
        ENNReal.ofReal
          (coreArcEnd candidate.stripCore -
            coreArcStart candidate.stripCore) := by
  rw [frontierWeightedPerimeter_eq_four_components candidate]
  have hlam_nonneg : 0 ≤ lam := hlam.le.trans' (by norm_num)
  have hcapUpper :
      0 ≤ lam * candidate.assembly.upperCap.arcLength :=
    mul_nonneg hlam_nonneg candidate.assembly.upperCap.arcLength_pos.le
  have hcapLower :
      0 ≤ lam * candidate.assembly.lowerCap.arcLength :=
    mul_nonneg hlam_nonneg candidate.assembly.lowerCap.arcLength_pos.le
  have hside :
      0 ≤ coreArcEnd candidate.stripCore -
        coreArcStart candidate.stripCore := by
    dsimp [coreArcEnd, coreArcStart]
    nlinarith [candidate.stripCore.radius_pos,
      candidate.stripCore.sideAngle_pos]
  rw [ENNReal.ofReal_add (add_nonneg
      (add_nonneg hcapUpper hcapLower) hside) hside,
    ENNReal.ofReal_add (add_nonneg hcapUpper hcapLower) hside,
    ENNReal.ofReal_add hcapUpper hcapLower]

/-- All four literal candidate arc families form one pairwise-disjoint patch
family. Its payoff approximates the actual complete-frontier weighted
perimeter, and one finite-summation application charges one global smooth
cost. -/
theorem exists_fourArc_patch_family_and_bound
    (hlam : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ Nu Nd Nr Nl : ℕ,
      ∃ Pu : Fin Nu →
        RigidProjectionPatch lam candidate.assembly.carrier,
      ∃ Pd : Fin Nd →
        RigidProjectionPatch lam candidate.assembly.carrier,
      ∃ Pr : Fin Nr →
        RigidProjectionPatch lam candidate.assembly.carrier,
      ∃ Pl : Fin Nl →
        RigidProjectionPatch lam candidate.assembly.carrier,
      0 < Nu ∧ 0 < Nd ∧ 0 < Nr ∧ 0 < Nl ∧
      (∀ i, (Pu i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      (∀ i, (Pd i).window ⊆ {p : PlanePoint | p.2 < -1}) ∧
      (∀ i, (Pr i).window ⊆
        {p : PlanePoint | candidate.capChord / 2 < p.1 ∧ |p.2| < 1}) ∧
      (∀ i, (Pl i).window ⊆
        {p : PlanePoint | p.1 < -candidate.capChord / 2 ∧ |p.2| < 1}) ∧
      Set.Pairwise (Set.univ : Set (PatchIndex Nu Nd Nr Nl))
        (Function.onFun Disjoint fun i =>
          (combinedPatch candidate Pu Pd Pr Pl i).window) ∧
      (∑ i : PatchIndex Nu Nd Nr Nl,
        (combinedPatch candidate Pu Pd Pr Pl i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (_root_.WeightedPerimeter lam
            (FrontierMeasure candidate.assembly.carrier)) ≤
        (∑ i : PatchIndex Nu Nd Nr Nl,
          (combinedPatch candidate Pu Pd Pr Pl i).payoff) +
          ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i : PatchIndex Nu Nd Nr Nl,
          (combinedPatch candidate Pu Pd Pr Pl i).payoff) ≤
        smoothCost lam U +
          (∑ i : PatchIndex Nu Nd Nr Nl,
            (combinedPatch candidate Pu Pd Pr Pl i).errorCoefficient) *
            characteristicDistance U candidate.assembly.carrier := by
  have hetaQuarter : 0 < eta / 4 := div_pos heta (by norm_num)
  obtain ⟨Nu, Pu, hNu, _, hu, hpu, _, hpayu, _⟩ :=
    FourArcUpperCap.exists_upperCap_patch_family_and_bound
      candidate hlam hetaQuarter
  obtain ⟨Nd, Pd, hNd, _, hd, hpd, _, hpayd⟩ :=
    CandidateLowerCap.exists_lowerCap_patch_family
      candidate hlam hetaQuarter
  obtain ⟨Nr, Pr, hNr, _, hr, hpr, _, hpayr, _⟩ :=
    FourArcRightSide.exists_rightSide_patch_family_and_bound
      candidate hetaQuarter
  obtain ⟨Nl, Pl, hNl, _, hl, hpl, _, hpayl⟩ :=
    CandidateLeftSide.exists_leftSide_patch_family candidate hetaQuarter
  have hpair := combinedPatch_pairwise candidate Pu Pd Pr Pl
    hu hd hr hl hpu hpd hpr hpl
  refine ⟨Nu, Nd, Nr, Nl, Pu, Pd, Pr, Pl,
    hNu, hNd, hNr, hNl, hu, hd, hr, hl, hpair, ?_, ?_, ?_⟩
  · apply ENNReal.sum_ne_top.2
    intro i _
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2
        (combinedPatch candidate Pu Pd Pr Pl i).rho_pos).ne'
  · rw [extendedFrontierCost_eq_four_components candidate hlam,
      sum_combinedPatch_payoff]
    let e : ℝ≥0∞ := ENNReal.ofReal (eta / 4)
    have hquarter : 0 ≤ eta / 4 := hetaQuarter.le
    have hfourError : e + e + e + e = ENNReal.ofReal eta := by
      dsimp [e]
      rw [← ENNReal.ofReal_add hquarter hquarter,
        ← ENNReal.ofReal_add (add_nonneg hquarter hquarter) hquarter,
        ← ENNReal.ofReal_add
          (add_nonneg (add_nonneg hquarter hquarter) hquarter) hquarter]
      congr 1
      ring
    calc
      ENNReal.ofReal
            (lam * candidate.assembly.upperCap.arcLength) +
          ENNReal.ofReal
            (lam * candidate.assembly.lowerCap.arcLength) +
          ENNReal.ofReal
            (coreArcEnd candidate.stripCore -
              coreArcStart candidate.stripCore) +
          ENNReal.ofReal
            (coreArcEnd candidate.stripCore -
              coreArcStart candidate.stripCore) ≤
          ((∑ i, (Pu i).payoff) + e) +
            ((∑ i, (Pd i).payoff) + e) +
            ((∑ i, (Pr i).payoff) + e) +
            ((∑ i, (Pl i).payoff) + e) :=
        add_le_add (add_le_add (add_le_add hpayu hpayd) hpayr) hpayl
      _ = ((∑ i, (Pu i).payoff) + (∑ i, (Pd i).payoff) +
            (∑ i, (Pr i).payoff) + (∑ i, (Pl i).payoff)) +
          (e + e + e + e) := by
        ac_rfl
      _ = ((∑ i, (Pu i).payoff) + (∑ i, (Pd i).payoff) +
            (∑ i, (Pr i).payoff) + (∑ i, (Pl i).payoff)) +
          ENNReal.ofReal eta := by
        rw [hfourError]
  · intro U hU
    have hpair' :
        Set.Pairwise
          (↑(Finset.univ : Finset (PatchIndex Nu Nd Nr Nl)))
          (Function.onFun Disjoint fun i =>
            (combinedPatch candidate Pu Pd Pr Pl i).window) := by
      simpa using hpair
    simpa using
      (RigidProjectionPatch.finset_sum_payoff_le_smoothCost_add_error
        (Finset.univ : Finset (PatchIndex Nu Nd Nr Nl))
        (combinedPatch candidate Pu Pd Pr Pl) hpair'
        candidate.assembly.measurableSet_carrier hU)
end CandidateFourArc
end CMVRelaxation

