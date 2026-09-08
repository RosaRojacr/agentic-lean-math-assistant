/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneGapBounds
import NearOneThirdFrozenMajorantTenthBounds

/-!
# Prescribed-density augmentation of the first near-one cell

This module adds the scale as a fourth box coordinate.  The fourth residual
prescribes the exact density `1 + r^3`; its two scale faces have uniform strict
opposite signs throughout the endpoint box.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

/-- The first three coordinates of a four-dimensional scale-coordinate point. -/
def prescribedDensityCoordinates (p : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![p 0, p 1, p 2]

/-- The fourth coordinate of a four-dimensional scale-coordinate point. -/
def prescribedDensityScale (p : Fin 4 → ℝ) : ℝ := p 3

/-- The cancellation-free residual for the prescribed density `1 + r^3`. -/
def prescribedDensityRow (r s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  s ^ 3 * densityCubeQuotient s (endpointPhysicalPoint s q 0) - r ^ 3

/-- Lower faces of the scale-coordinate endpoint prism. -/
def prescribedDensityBoxLower : Fin 4 → ℝ := ![52, 27, -3822, 0]

/-- Upper faces of the scale-coordinate endpoint prism. -/
def prescribedDensityBoxUpper (r : ℝ) : Fin 4 → ℝ :=
  ![54, 28, -3821, r / 2]

/-- The first three coordinates and scale bounds extracted from prism membership. -/
theorem prescribedDensityBox_membership {r : ℝ} {p : Fin 4 → ℝ}
    (hp : p ∈ Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r)) :
    InEndpointBox (prescribedDensityCoordinates p) ∧
      prescribedDensityScale p ∈ Icc 0 (r / 2) := by
  constructor
  · intro i
    fin_cases i
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        prescribedDensityBoxLower, prescribedDensityBoxUpper] using
        ⟨hp.1 (0 : Fin 4), hp.2 (0 : Fin 4)⟩
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        prescribedDensityBoxLower, prescribedDensityBoxUpper] using
        ⟨hp.1 (1 : Fin 4), hp.2 (1 : Fin 4)⟩
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        prescribedDensityBoxLower, prescribedDensityBoxUpper] using
        ⟨hp.1 (2 : Fin 4), hp.2 (2 : Fin 4)⟩
  · simpa [prescribedDensityScale, prescribedDensityBoxLower,
      prescribedDensityBoxUpper] using
      ⟨hp.1 (3 : Fin 4), hp.2 (3 : Fin 4)⟩

/-- The prescribed-density row is strictly negative on the zero-scale face. -/
theorem prescribedDensityRow_zero_face {r : ℝ} (hr : 0 < r)
    (q : Fin 3 → ℝ) : prescribedDensityRow r 0 q < 0 := by
  simp only [prescribedDensityRow, zero_pow (by norm_num : 3 ≠ 0), zero_mul,
    zero_sub]
  exact neg_neg_of_pos (pow_pos hr 3)

/-- The prescribed-density row is strictly positive on the `r / 2` scale face,
uniformly over the complete endpoint box. -/
theorem prescribedDensityRow_half_face {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 50) (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : 0 < prescribedDensityRow r (r / 2) q := by
  have hs0 : 0 < r / 2 := by positivity
  have hs : r / 2 < (1 / 100 : ℝ) := by linarith
  have hquot := endpointBox_densityCubeQuotient_bounds hs0 hs q hq
  have hr3 : 0 < r ^ 3 := pow_pos hr0 3
  have hscaled := mul_lt_mul_of_pos_left hquot.1
    (show 0 < r ^ 3 / 8 by positivity)
  rw [prescribedDensityRow]
  have hcube : (r / 2) ^ 3 = r ^ 3 / 8 := by ring
  rw [hcube]
  nlinarith

/-- The complete four-row scale-coordinate map used for prescribed-density
Poincare--Miranda. -/
def prescribedDensityAugmentedMap (r : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let s := prescribedDensityScale p
  let q := prescribedDensityCoordinates p
  ![rescaledOrientedNearOneMap s q 0,
    rescaledOrientedNearOneMap s q 1,
    rescaledOrientedNearOneMap s q 2,
    prescribedDensityRow r s q]

/-- The fourth augmented coordinate has strict opposite signs on both scale
faces of every sufficiently small prescribed-density prism. -/
theorem prescribedDensityAugmentedMap_scale_faces {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 50) (p : Fin 4 → ℝ)
    (hp : p ∈ Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r)) :
    (p 3 = prescribedDensityBoxLower 3 →
      prescribedDensityAugmentedMap r p 3 < 0) ∧
    (p 3 = prescribedDensityBoxUpper r 3 →
      0 < prescribedDensityAugmentedMap r p 3) := by
  have hmem := prescribedDensityBox_membership hp
  constructor
  · intro hface
    have hs : prescribedDensityScale p = 0 := by
      simpa [prescribedDensityScale, prescribedDensityBoxLower] using hface
    simpa [prescribedDensityAugmentedMap, hs] using
      prescribedDensityRow_zero_face hr0 (prescribedDensityCoordinates p)
  · intro hface
    have hs : prescribedDensityScale p = r / 2 := by
      simpa [prescribedDensityScale, prescribedDensityBoxUpper] using hface
    simpa [prescribedDensityAugmentedMap, hs] using
      prescribedDensityRow_half_face hr0 hr (prescribedDensityCoordinates p) hmem.1


set_option maxHeartbeats 0 in
-- The joint third-row expansion exceeds the default deterministic elaboration budget.
/-- The complete rescaled map is jointly continuous in the scale and all three
rescaled coordinates at every positive point of the endpoint box below
`1 / 100`. -/
theorem continuousAt_rescaledOrientedNearOneMap_joint_positive
    {s : ℝ} (hs0 : 0 < s) (hs : s < 1 / 100)
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2) (s, q) := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  rcases endpointBox_principalChart hs0 hs q hq with
    ⟨hySq, hdenFour, _haddFour, hdenThree, _haddThree⟩
  have hZ : ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => endpointPhysicalPoint p.1 p.2 0)
      (s, q) := by
    unfold endpointPhysicalPoint tangentCenteredPoint
    fun_prop
  have hA : ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => endpointPhysicalPoint p.1 p.2 1)
      (s, q) := by
    unfold endpointPhysicalPoint tangentCenteredPoint
    fun_prop
  have hB : ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => endpointPhysicalPoint p.1 p.2 2)
      (s, q) := by
    unfold endpointPhysicalPoint tangentCenteredPoint
    fun_prop
  rw [continuousAt_pi]
  intro i
  fin_cases i
  · change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 0) (s, q)
    rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
        rescaledOrientedNearOneMap p.1 p.2 0) =
        fun p => poleFreeFirstRescaledRow p.1 (p.2 0) by
      funext p
      exact rescaledOrientedNearOneMap_first_eq_poleFree p.1 p.2]
    have hy :
        1 - yCoord s (rescaledFirstPhysicalCoordinate s (q 0)) ^ 2 ≠ 0 := by
      rw [← tangentCenteredPoint_rescaled_zeroCoord s q]
      change 1 - yCoord s (endpointPhysicalPoint s q 0) ^ 2 ≠ 0
      nlinarith
    have hd :
        1 + s * yCoord s (rescaledFirstPhysicalCoordinate s (q 0)) ≠ 0 := by
      simpa [endpointPhysicalPoint] using hdenFour
    have hz : ContinuousAt
        (fun p : ℝ × (Fin 3 → ℝ) =>
          rescaledFirstPhysicalCoordinate p.1 (p.2 0)) (s, q) := by
      unfold rescaledFirstPhysicalCoordinate
      fun_prop
    have hangle : ContinuousAt
        (fun p : ℝ × (Fin 3 → ℝ) =>
          typeFourAngleBar p.1
            (rescaledFirstPhysicalCoordinate p.1 (p.2 0))) (s, q) := by
      unfold typeFourAngleBar densityCubeQuotient density
        typeFourAngleIncrement halfCos yCoord aCoord
        rescaledFirstPhysicalCoordinate
      fun_prop (disch := first | exact hy | exact hd | positivity)
    unfold poleFreeFirstRescaledRow firstRescaledAlgebraicFactor
      yCoord aCoord rescaledFirstPhysicalCoordinate
    fun_prop (disch := first | exact hangle | exact hy | exact hd | positivity)
  · change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 1) (s, q)
    rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
        rescaledOrientedNearOneMap p.1 p.2 1) =
        fun p => poleFreeSecondRescaledRow p.1 p.2 by
      funext p
      exact rescaledOrientedNearOneMap_second_eq_poleFree p.1 p.2]
    exact continuous_poleFreeSecondRescaledRow_joint.continuousAt
  · change ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 2) (s, q)
    rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
        rescaledOrientedNearOneMap p.1 p.2 2) =
        fun p => -poleFreeThirdRescaledRow p.1 p.2 by
      funext p
      exact rescaledOrientedNearOneMap_third_eq_neg_poleFree p.1 p.2]
    let Z : ℝ × (Fin 3 → ℝ) → ℝ := fun p => endpointPhysicalPoint p.1 p.2 0
    let Af : ℝ × (Fin 3 → ℝ) → ℝ := fun p => endpointPhysicalPoint p.1 p.2 1
    let Bf : ℝ × (Fin 3 → ℝ) → ℝ := fun p => endpointPhysicalPoint p.1 p.2 2
    have hZ' : ContinuousAt Z (s, q) := hZ
    have hA' : ContinuousAt Af (s, q) := hA
    have hB' : ContinuousAt Bf (s, q) := hB
    have hy : 1 - yCoord s (Z (s, q)) ^ 2 ≠ 0 := by
      dsimp only [Z]
      nlinarith
    have hyprod :
        (1 + s ^ 2) * (1 - yCoord s (Z (s, q)) ^ 2) ≠ 0 :=
      mul_ne_zero (by positivity) hy
    have hhalfY : halfCos (yCoord s (Z (s, q))) ≠ 0 := by
      unfold halfCos
      exact div_ne_zero hy (by positivity)
    let N : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
      (H3 (Z p) (Af p) (Bf p) π).eval p.1 -
        2 * (H2 (Z p) (Af p) (Bf p)).eval p.1 +
        4 * (H1 (Z p) π).eval p.1 +
        (2 / 3 : ℝ) * π * p.1 *
          ((H2 (Z p) (Af p) (Bf p)).eval p.1 -
            (H1 (Z p) π).eval p.1)
    have hN : ContinuousAt N (s, q) := by
      dsimp only [N]
      simp [H3, H2, H1, areaNumerator, areaL, areaZ, areaX, W, U, K,
        cosineNumerator, foldNumerator, qPrime, B, E, R, A]
      fun_prop
    have hpolyQuot : ContinuousAt (fun p => N p / p.1 ^ 2) (s, q) :=
      hN.div₀ (continuousAt_fst.pow 2) (pow_ne_zero 2 hsne)
    have hpoly : ContinuousAt
        (fun p => H3hatPolynomial p.1 (Z p) (Af p) (Bf p) π) (s, q) := by
      apply hpolyQuot.congr_of_eventuallyEq
      filter_upwards [continuousAt_fst.eventually_ne hsne] with p hp
      apply (eq_div_iff (pow_ne_zero 2 hp)).2
      rw [mul_comm]
      dsimp only [N]
      convert H3hatPolynomial_identity p.1 (Z p) (Af p) (Bf p) π using 1
      all_goals ring
    have hK : ContinuousAt
        (fun p => (NearOneNormalizedFlow.K (Af p)).eval p.1) (s, q) := by
      simp [NearOneNormalizedFlow.K, NearOneNormalizedFlow.R]
      fun_prop (disch := positivity)
    have hremFour : ContinuousAt
        (fun p => atanQuotientSqRemainder
          (p.1 ^ 2 * Z p / (1 + p.1 * yCoord p.1 (Z p)))) (s, q) :=
      continuous_atanQuotientSqRemainder.continuousAt.comp (by
        unfold yCoord aCoord
        fun_prop (disch := exact hdenFour))
    have hremThree : ContinuousAt
        (fun p => atanQuotientSqRemainder
          (p.1 ^ 2 * eCoord p.1 (Z p) (Af p) (Bf p) /
            (1 + wCoord p.1 (Af p) *
              vCoord p.1 (Z p) (Af p) (Bf p)))) (s, q) :=
      continuous_atanQuotientSqRemainder.continuousAt.comp (by
        unfold wCoord vCoord rCoord eCoord
        fun_prop (disch := exact hdenThree))
    have hatanW : ContinuousAt
        (fun p => atanQuotient (wCoord p.1 (Af p))) (s, q) :=
      continuous_atanQuotient.continuousAt.comp (by
        unfold wCoord rCoord
        fun_prop)
    have hregular : ContinuousAt
        (fun p => regularizedThirdRow p.1 (Z p) (Af p) (Bf p) π) (s, q) := by
      unfold regularizedThirdRow areaAngleCorrectionBar
        foldAngleCorrectionBar typeFourAngleBar typeThreeAngleBar2
        typeFourAngleBar2 typeThreeAngleIncrementBar2
        typeFourAngleIncrementBar2 typeFourAngleIncrement densityCubeQuotient
        density halfCos foldDenominator typeFourSineProductBar areaDenominator
        areaPiWeight yCoord wCoord vCoord aCoord rCoord eCoord
      fun_prop (disch := first | assumption | positivity)
    have hquot : ContinuousAt
        (fun p => regularizedThirdRow p.1 (Z p) (Af p) (Bf p) π / p.1 ^ 2)
        (s, q) :=
      hregular.div₀ (continuousAt_fst.pow 2) (pow_ne_zero 2 hsne)
    apply ContinuousAt.neg
    apply hquot.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually_ne hsne] with p hp
    simp only [poleFreeThirdRescaledRow, hp, ↓reduceIte, Z, Af, Bf,
      endpointPhysicalPoint]

/-- The complete prescribed-density augmented map is continuous on its prism. -/
theorem continuousOn_prescribedDensityAugmentedMap {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 50) :
    ContinuousOn (prescribedDensityAugmentedMap r)
      (Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r)) := by
  intro p hp
  have hmem := prescribedDensityBox_membership hp
  have hr_nonneg : 0 ≤ r := hr0.le
  let s := prescribedDensityScale p
  let q := prescribedDensityCoordinates p
  have hs0 : 0 ≤ s := hmem.2.1
  have hs : s < 1 / 100 := by
    have hsle : s ≤ r / 2 := hmem.2.2
    norm_num at hr hsle ⊢
    linarith [hr_nonneg]
  have hscont : ContinuousAt prescribedDensityScale p := by
    exact (continuous_apply 3).continuousAt
  have hqcont : ContinuousAt prescribedDensityCoordinates p := by
    unfold prescribedDensityCoordinates
    fun_prop
  have hsq : ContinuousAt (fun x : Fin 4 → ℝ =>
      (prescribedDensityScale x, prescribedDensityCoordinates x)) p :=
    hscont.prodMk hqcont
  have hfirst : ContinuousAt (fun x : Fin 4 → ℝ =>
      rescaledOrientedNearOneMap (prescribedDensityScale x)
        (prescribedDensityCoordinates x)) p := by
    by_cases hszero : s = 0
    · have hcusp : ContinuousAt (fun z : ℝ × (Fin 3 → ℝ) =>
          rescaledOrientedNearOneMap z.1 z.2) (0, q) := by
        rw [continuousAt_pi]
        intro i
        fin_cases i
        · exact continuousAt_rescaledOrientedNearOneMap_first_joint_zero q
        · change ContinuousAt (fun z : ℝ × (Fin 3 → ℝ) =>
              rescaledOrientedNearOneMap z.1 z.2 (1 : Fin 3)) (0, q)
          rw [show (fun z : ℝ × (Fin 3 → ℝ) =>
              rescaledOrientedNearOneMap z.1 z.2 (1 : Fin 3)) =
              fun z => poleFreeSecondRescaledRow z.1 z.2 by
            funext z
            exact rescaledOrientedNearOneMap_second_eq_poleFree z.1 z.2]
          exact continuous_poleFreeSecondRescaledRow_joint.continuousAt
        · exact continuousAt_rescaledOrientedNearOneMap_third_joint q
      have hcomp := hcusp.comp_of_eq hsq (by simp [s, q, hszero])
      simpa only [Function.comp_def] using hcomp
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hszero)
      have hpositive :=
        continuousAt_rescaledOrientedNearOneMap_joint_positive hspos hs q hmem.1
      have hcomp := hpositive.comp_of_eq hsq (by simp [s, q])
      simpa only [Function.comp_def] using hcomp
  have hrow : ContinuousAt (fun x : Fin 4 → ℝ =>
      prescribedDensityRow r (prescribedDensityScale x)
        (prescribedDensityCoordinates x)) p := by
    have hz : ContinuousAt (fun x : Fin 4 → ℝ =>
        endpointPhysicalPoint (prescribedDensityScale x)
          (prescribedDensityCoordinates x) 0) p := by
      unfold endpointPhysicalPoint prescribedDensityScale prescribedDensityCoordinates
      simp only [tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
        exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      fun_prop (disch := positivity)
    have hden : (1 + s ^ 2) *
        (1 - yCoord s (endpointPhysicalPoint s q 0) ^ 2) ≠ 0 := by
      by_cases hspos : 0 < s
      · have hquot := endpointBox_densityCubeQuotient_bounds hspos hs q hmem.1
        intro hzero
        have hzeroquot : densityCubeQuotient s (endpointPhysicalPoint s q 0) = 0 := by
          simp [densityCubeQuotient, hzero]
        rw [hzeroquot] at hquot
        norm_num at hquot
      · have hs_eq : s = 0 := le_antisymm (not_lt.mp hspos) hs0
        simp [hs_eq, yCoord, aCoord]
    have hquot : ContinuousAt (fun x : Fin 4 → ℝ =>
        densityCubeQuotient (prescribedDensityScale x)
          (endpointPhysicalPoint (prescribedDensityScale x)
            (prescribedDensityCoordinates x) 0)) p := by
      have hden' : (1 + prescribedDensityScale p ^ 2) *
          (1 - (prescribedDensityScale p *
            (1 + prescribedDensityScale p * endpointPhysicalPoint
              (prescribedDensityScale p) (prescribedDensityCoordinates p) 0)) ^ 2) ≠ 0 := by
        simpa [s, q, yCoord, aCoord] using hden
      unfold densityCubeQuotient yCoord aCoord
      fun_prop (disch := first | exact hden' | assumption)
    unfold prescribedDensityRow
    exact ((hscont.pow 3).mul hquot).sub continuousAt_const
  rw [continuousWithinAt_pi]
  intro i
  fin_cases i
  · exact ((continuous_apply 0).continuousAt.comp hfirst).continuousWithinAt
  · exact ((continuous_apply 1).continuousAt.comp hfirst).continuousWithinAt
  · exact ((continuous_apply 2).continuousAt.comp hfirst).continuousWithinAt
  · simpa [prescribedDensityAugmentedMap] using hrow.continuousWithinAt

/-- The first three augmented rows inherit their strict endpoint-box face signs
uniformly throughout every sufficiently small scale-coordinate prism. -/
theorem prescribedDensityAugmentedMap_first_three_faces :
    ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
      ∀ p, p ∈ Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r) →
        ∀ i : Fin 3,
          (p i.castSucc = prescribedDensityBoxLower i.castSucc →
            prescribedDensityAugmentedMap r p i.castSucc < 0) ∧
          (p i.castSucc = prescribedDensityBoxUpper r i.castSucc →
            0 < prescribedDensityAugmentedMap r p i.castSucc) := by
  rcases Metric.mem_nhds_iff.mp eventually_all_face_cell with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro r hr0 hr p hp i
  have hmem := prescribedDensityBox_membership hp
  have hs0 : 0 ≤ prescribedDensityScale p := hmem.2.1
  have hslt : prescribedDensityScale p < ε := by
    have hsle : prescribedDensityScale p ≤ r / 2 := hmem.2.2
    nlinarith
  have hsball : prescribedDensityScale p ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_nonneg hs0] using hslt
  have hfaces : HasEndpointBoxFaceSigns (prescribedDensityScale p) := hball hsball
  have hi := hfaces (prescribedDensityCoordinates p) hmem.1 i
  fin_cases i <;>
    simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      prescribedDensityBoxLower, prescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hi

/-- All eight strict opposite-face signs of the prescribed-density prism hold
uniformly for every sufficiently small positive target parameter. -/
theorem prescribedDensityAugmentedMap_all_faces :
    ∃ r0 > 0, r0 ≤ 1 / 50 ∧
      ∀ r, 0 < r → r < r0 →
        ∀ p, p ∈ Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r) →
          ∀ i : Fin 4,
            (p i = prescribedDensityBoxLower i →
              prescribedDensityAugmentedMap r p i < 0) ∧
            (p i = prescribedDensityBoxUpper r i →
              0 < prescribedDensityAugmentedMap r p i) := by
  rcases prescribedDensityAugmentedMap_first_three_faces with
    ⟨r1, hr1, hfirst⟩
  refine ⟨min r1 (1 / 50), lt_min hr1 (by norm_num),
    min_le_right _ _, ?_⟩
  intro r hr0 hr p hp i
  have hr1' : r < r1 := lt_of_lt_of_le hr (min_le_left _ _)
  have hr50 : r < 1 / 50 := lt_of_lt_of_le hr (min_le_right _ _)
  have hfirst' := hfirst r hr0 hr1' p hp
  have hscale := prescribedDensityAugmentedMap_scale_faces hr0 hr50 p hp
  fin_cases i
  · simpa using hfirst' (0 : Fin 3)
  · simpa using hfirst' (1 : Fin 3)
  · simpa using hfirst' (2 : Fin 3)
  · simpa using hscale

/-- Poincare--Miranda produces a prescribed-density root from face signs on
one concrete augmented prism.  This is the reusable kernel-checked soundness
interface for explicit face certificates. -/
theorem prescribedDensity_nearOneRoot_of_augmented_faces {r : ℝ}
    (hrpos : 0 < r) (hr50 : r < 1 / 50)
    (hfaces :
      ∀ p, p ∈ Icc prescribedDensityBoxLower (prescribedDensityBoxUpper r) →
        ∀ i : Fin 4,
          (p i = prescribedDensityBoxLower i →
            prescribedDensityAugmentedMap r p i < 0) ∧
          (p i = prescribedDensityBoxUpper r i →
            0 < prescribedDensityAugmentedMap r p i)) :
    ∃ s q, 0 < s ∧ s < r / 2 ∧ s < 1 / 100 ∧ InEndpointBox q ∧
      rescaledOrientedNearOneMap s q = 0 ∧
      density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
  have hbox : ∀ i,
      prescribedDensityBoxLower i < prescribedDensityBoxUpper r i := by
    intro i
    fin_cases i <;>
      simp [prescribedDensityBoxLower, prescribedDensityBoxUpper] <;> linarith
  have hcontinuous := continuousOn_prescribedDensityAugmentedMap hrpos hr50
  obtain ⟨p, hp, hzero⟩ := BoxPoincareMiranda.poincareMiranda hbox
    (prescribedDensityAugmentedMap r) hcontinuous
    (fun p hp i hi => (hfaces p hp i).1 hi |>.le)
    (fun p hp i hi => (hfaces p hp i).2 hi |>.le)
  let s := prescribedDensityScale p
  let q := prescribedDensityCoordinates p
  have hmem : InEndpointBox q ∧ s ∈ Icc 0 (r / 2) := by
    simpa [s, q] using prescribedDensityBox_membership hp
  have hrow : prescribedDensityRow r s q = 0 := by
    have h := congrFun hzero (3 : Fin 4)
    simpa [prescribedDensityAugmentedMap, s, q] using h
  have hsne : s ≠ 0 := by
    intro hs
    have hneg := prescribedDensityRow_zero_face hrpos q
    have : prescribedDensityRow r s q < 0 := by simpa [hs] using hneg
    rw [hrow] at this
    exact (lt_irrefl (0 : ℝ)) this
  have hspos : 0 < s := lt_of_le_of_ne hmem.2.1 (Ne.symm hsne)
  have hsHalf : s < r / 2 := by
    apply lt_of_le_of_ne hmem.2.2
    intro h
    have hpos := prescribedDensityRow_half_face hrpos hr50 q hmem.1
    have : 0 < prescribedDensityRow r s q := by simpa [h] using hpos
    rw [hrow] at this
    exact (lt_irrefl (0 : ℝ)) this
  have hslt : s < 1 / 100 := by
    nlinarith [hmem.2.2]
  have hmap : rescaledOrientedNearOneMap s q = 0 := by
    funext i
    fin_cases i
    · have h := congrFun hzero (0 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
    · have h := congrFun hzero (1 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
    · have h := congrFun hzero (2 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
  have hySq := (endpointBox_principalChart hspos hslt q hmem.1).1
  have hy : 1 - yCoord s (endpointPhysicalPoint s q 0) ^ 2 ≠ 0 := by
    nlinarith
  have hdensity := density_sub_one_eq_cube_mul
    s (endpointPhysicalPoint s q 0) hy
  have hdensityTarget :
      density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
    rw [prescribedDensityRow] at hrow
    linarith
  exact ⟨s, q, hspos, hsHalf, hslt, hmem.1, hmap, hdensityTarget⟩

/-- Every sufficiently small positive prescribed density increment `r^3` is
attained by a simultaneous zero of the three-row rescaled endpoint map. -/
theorem prescribedDensity_nearOneRoot :
    ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
      ∃ s q, 0 < s ∧ s < r / 2 ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
  rcases prescribedDensityAugmentedMap_all_faces with
    ⟨r0, hr0, hr50bound, hfaces⟩
  refine ⟨r0, hr0, ?_⟩
  intro r hrpos hrr0
  exact prescribedDensity_nearOneRoot_of_augmented_faces hrpos
    (lt_of_lt_of_le hrr0 hr50bound) (hfaces r hrpos hrr0)

/-- Any explicit uniform radius for the six three-row face signs immediately
yields prescribed-density roots up to twice that radius.  In particular, a
literal rational `R` plugs into this theorem without another compactness
argument. -/
theorem prescribedDensity_nearOneRoot_of_face_radius {R : ℝ}
    (hR100 : R ≤ 1 / 100)
    (hfaces : ∀ s, 0 ≤ s → s < R → HasEndpointBoxFaceSigns s) :
    ∀ r, 0 < r → r < 2 * R →
      ∃ s q, 0 < s ∧ s < r / 2 ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
  intro r hrpos hrr
  have hr50 : r < 1 / 50 := by nlinarith
  apply prescribedDensity_nearOneRoot_of_augmented_faces hrpos hr50
  intro p hp i
  have hmem := prescribedDensityBox_membership hp
  have hs0 : 0 ≤ prescribedDensityScale p := hmem.2.1
  have hsR : prescribedDensityScale p < R := by
    nlinarith [hmem.2.2]
  have hfirst := hfaces (prescribedDensityScale p) hs0 hsR
    (prescribedDensityCoordinates p) hmem.1
  have hscale := prescribedDensityAugmentedMap_scale_faces hrpos hr50 p hp
  fin_cases i
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      prescribedDensityBoxLower, prescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (0 : Fin 3)
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      prescribedDensityBoxLower, prescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (1 : Fin 3)
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      prescribedDensityBoxLower, prescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (2 : Fin 3)
  · simpa using hscale

/-- An explicit six-face radius gives an exact density seam:
every `λ < 1 + (2R)³` is attained by the prescribed-density prism. -/
theorem prescribedDensity_lambda_nearOneRoot_of_face_radius {R : ℝ}
    (hR0 : 0 < R) (hR100 : R ≤ 1 / 100)
    (hfaces : ∀ s, 0 ≤ s → s < R → HasEndpointBoxFaceSigns s) :
    ∀ («λ» : ℝ), 1 < «λ» → «λ» < 1 + (2 * R) ^ 3 →
      ∃ s q, 0 < s ∧ 8 * s ^ 3 < «λ» - 1 ∧ s < 1 / 100 ∧
        InEndpointBox q ∧ rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» := by
  intro lam hLam hLamRadius
  have htarget0 : 0 ≤ lam - 1 := by linarith
  have htargetR : lam - 1 ≤ (2 * R) ^ 3 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3) (Icc 0 (2 * R)) :=
    continuous_pow 3 |>.continuousOn
  have htarget : lam - 1 ∈ Icc ((0 : ℝ) ^ 3) ((2 * R) ^ 3) := by
    simpa using And.intro htarget0 htargetR
  rcases intermediate_value_Icc (by positivity : (0 : ℝ) ≤ 2 * R)
      hcont htarget with ⟨r, hr, hrpow⟩
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro hre
    subst r
    norm_num at hrpow
    linarith
  have hrR : r < 2 * R := by
    apply lt_of_le_of_ne hr.2
    intro hre
    subst r
    linarith
  rcases prescribedDensity_nearOneRoot_of_face_radius hR100 hfaces
      r hrpos hrR with
    ⟨s, q, hs0, hsr, hs100, hq, hroot, hdensity⟩
  have htwos : 2 * s < r := by linarith
  have hcube : (2 * s) ^ 3 < r ^ 3 :=
    pow_lt_pow_left₀ htwos (by positivity) (by norm_num)
  have hscale : 8 * s ^ 3 < lam - 1 := by
    norm_num [mul_pow] at hcube
    linarith
  have hrlam : 1 + r ^ 3 = lam := by linarith
  rw [hrlam] at hdensity
  exact ⟨s, q, hs0, hscale, hs100, hq, hroot, hdensity⟩

/-- Below the certified reduced-gap radius, six face signs are the only
remaining certificate premise for prescribed-density strict improvement. -/
theorem prescribedDensity_lambda_strictImprovement_of_face_radius {R : ℝ}
    (hR0 : 0 < R) (hR : R ≤ 1 / 126334)
    (hfaces : ∀ s, 0 ≤ s → s < R → HasEndpointBoxFaceSigns s) :
    ∀ («λ» : ℝ), 1 < «λ» → «λ» < 1 + (2 * R) ^ 3 →
      ∃ s q, 0 < s ∧ s < R ∧ 8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamR
  obtain ⟨s, q, hs0, hscale, hs100, hq, hroot, hdensity⟩ :=
    prescribedDensity_lambda_nearOneRoot_of_face_radius hR0
      (hR.trans (by norm_num)) hfaces lam hlam hlamR
  have hsR : s < R := by
    by_contra h
    have hcube := pow_le_pow_left₀ hR0.le (le_of_not_gt h) 3
    nlinarith
  have hgap : poleFreeReducedGap s q < 0 :=
    (explicit_poleFreeReducedGap_neg q hs0.le (hsR.le.trans hR) hq).trans
      (by norm_num)
  have hstrict :=
    stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
      hs0 hs100 hq hroot hgap
  dsimp only at hstrict
  rw [hdensity] at hstrict
  exact ⟨s, q, hs0, hsR, hscale, hq, hroot, hdensity, hstrict⟩

/-- Bridge from the rational frozen third-row estimate to the complete explicit
six-face cell contract, including the exact density seam. -/
theorem prescribedDensity_lambda_explicit_first_cell_of_frozen_estimate
    (hfrozen : ExplicitThirdFrozenEstimate) :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» < 1 + (2 * (1 / 200000 : ℝ)) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 200000 ∧ 8 * s ^ 3 < «λ» - 1 ∧
        InEndpointBox q ∧ rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  apply prescribedDensity_lambda_strictImprovement_of_face_radius
    (R := (1 / 200000 : ℝ)) (by norm_num) (by norm_num)
  intro s hs0 hs
  exact explicit_all_face_cell_of_frozen_estimate hfrozen s hs0
    (hs.le.trans (by norm_num))

/-- Unconditional strict improvement on the explicit prescribed-density
cell `1 < λ < 1 + (2 / 200000) ^ 3`. -/
theorem prescribedDensity_lambda_explicit_first_cell :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» < 1 + (2 * (1 / 200000 : ℝ)) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 200000 ∧ 8 * s ^ 3 < «λ» - 1 ∧
        InEndpointBox q ∧ rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) :=
  prescribedDensity_lambda_explicit_first_cell_of_frozen_estimate
    explicitThirdFrozenEstimate

private def fixedPrescribedDensityBoxLower (R : ℝ) : Fin 4 → ℝ :=
  ![52, 27, -3822, R / 2]

private def fixedPrescribedDensityBoxUpper (R : ℝ) : Fin 4 → ℝ :=
  ![54, 28, -3821, R]

private theorem fixedPrescribedDensityBox_membership {R : ℝ} {p : Fin 4 → ℝ}
    (hp : p ∈ Icc (fixedPrescribedDensityBoxLower R)
      (fixedPrescribedDensityBoxUpper R)) :
    InEndpointBox (prescribedDensityCoordinates p) ∧
      prescribedDensityScale p ∈ Icc (R / 2) R := by
  constructor
  · intro i
    fin_cases i
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper] using
        ⟨hp.1 (0 : Fin 4), hp.2 (0 : Fin 4)⟩
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper] using
        ⟨hp.1 (1 : Fin 4), hp.2 (1 : Fin 4)⟩
    · simpa [prescribedDensityCoordinates, endpointBoxLower, endpointBoxUpper,
        fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper] using
        ⟨hp.1 (2 : Fin 4), hp.2 (2 : Fin 4)⟩
  · have hlo := hp.1 (3 : Fin 4)
    have hhi := hp.2 (3 : Fin 4)
    change R / 2 ≤ p 3 at hlo
    change p 3 ≤ R at hhi
    exact ⟨hlo, hhi⟩

private theorem fixedCell_radius_le_half_r {R r : ℝ} (hrpos : 0 < r)
    (hlower : (2 * R) ^ 3 ≤ r ^ 3) :
    R ≤ r / 2 := by
  have htwo : 2 * R ≤ r := by
    apply le_of_not_gt
    intro hlt
    have hpow : r ^ 3 < (2 * R) ^ 3 :=
      pow_lt_pow_left₀ hlt hrpos.le (by norm_num)
    exact (not_lt_of_ge hlower) hpow
  linarith

private theorem continuousOn_fixedPrescribedDensityAugmentedMap {R r : ℝ}
    (hRpos : 0 < R) (hrpos : 0 < r) (hr50 : r < 1 / 50)
    (hlower : (2 * R) ^ 3 ≤ r ^ 3) :
    ContinuousOn (prescribedDensityAugmentedMap r)
      (Icc (fixedPrescribedDensityBoxLower R)
        (fixedPrescribedDensityBoxUpper R)) := by
  apply (continuousOn_prescribedDensityAugmentedMap hrpos hr50).mono
  intro p hp
  have hRr := fixedCell_radius_le_half_r hrpos hlower
  constructor
  · intro i
    fin_cases i
    · simpa [fixedPrescribedDensityBoxLower, prescribedDensityBoxLower] using
        hp.1 (0 : Fin 4)
    · simpa [fixedPrescribedDensityBoxLower, prescribedDensityBoxLower] using
        hp.1 (1 : Fin 4)
    · simpa [fixedPrescribedDensityBoxLower, prescribedDensityBoxLower] using
        hp.1 (2 : Fin 4)
    · exact (by
        have hp3 := hp.1 (3 : Fin 4)
        simpa [fixedPrescribedDensityBoxLower, prescribedDensityBoxLower] using
          (le_trans (by positivity : (0 : ℝ) ≤ R / 2) hp3))
  · intro i
    fin_cases i
    · simpa [fixedPrescribedDensityBoxUpper, prescribedDensityBoxUpper] using
        hp.2 (0 : Fin 4)
    · simpa [fixedPrescribedDensityBoxUpper, prescribedDensityBoxUpper] using
        hp.2 (1 : Fin 4)
    · simpa [fixedPrescribedDensityBoxUpper, prescribedDensityBoxUpper] using
        hp.2 (2 : Fin 4)
    · exact (by
        have hp3 := hp.2 (3 : Fin 4)
        simpa [fixedPrescribedDensityBoxUpper, prescribedDensityBoxUpper] using
          (le_trans hp3 hRr))

private theorem fixedCell_augmented_faces {R r : ℝ}
    (hRpos : 0 < R) (hRupper : R ≤ 1 / 126334)
    (hlower : (2 * R) ^ 3 ≤ r ^ 3)
    (hupper : r ^ 3 ≤ 251 / 20 * R ^ 3) :
    ∀ p, p ∈ Icc (fixedPrescribedDensityBoxLower R)
        (fixedPrescribedDensityBoxUpper R) →
      ∀ i : Fin 4,
        (p i = fixedPrescribedDensityBoxLower R i →
          prescribedDensityAugmentedMap r p i < 0) ∧
        (p i = fixedPrescribedDensityBoxUpper R i →
          0 < prescribedDensityAugmentedMap r p i) := by
  intro p hp i
  have hmem := fixedPrescribedDensityBox_membership hp
  have hsnonneg : 0 ≤ prescribedDensityScale p :=
    (by exact (by positivity : (0 : ℝ) ≤ R / 2) |>.trans hmem.2.1)
  have hsWidened : prescribedDensityScale p ≤ 1 / 126334 :=
    hmem.2.2.trans hRupper
  have hfirst := explicit_all_face_cell_of_frozen_estimate explicitThirdFrozenEstimate
    (prescribedDensityScale p) hsnonneg hsWidened
    (prescribedDensityCoordinates p) hmem.1
  fin_cases i
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (0 : Fin 3)
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (1 : Fin 3)
  · simpa [prescribedDensityCoordinates, prescribedDensityAugmentedMap,
      fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper,
      endpointBoxLower, endpointBoxUpper] using hfirst (2 : Fin 3)
  · constructor
    · intro hface
      have hs : prescribedDensityScale p = R / 2 := by
        simpa [prescribedDensityScale, fixedPrescribedDensityBoxLower] using hface
      have hs100 : R / 2 < (1 / 100 : ℝ) := by
        calc
          R / 2 ≤ (1 / 126334 : ℝ) / 2 :=
            div_le_div_of_nonneg_right hRupper (by norm_num)
          _ < 1 / 100 := by norm_num
      have hquot := endpointBox_densityCubeQuotient_bounds
        (s := R / 2) (by positivity) hs100
        (prescribedDensityCoordinates p) hmem.1
      have hR3 : 0 < R ^ 3 := pow_pos hRpos 3
      have hscaled := mul_lt_mul_of_pos_left hquot.2
        (show 0 < R ^ 3 / 8 by positivity)
      change prescribedDensityRow r (prescribedDensityScale p)
        (prescribedDensityCoordinates p) < 0
      rw [hs, prescribedDensityRow]
      have hcube : (R / 2) ^ 3 = R ^ 3 / 8 := by ring
      rw [hcube]
      have hlower' : 8 * R ^ 3 ≤ r ^ 3 := by
        calc
          8 * R ^ 3 = (2 * R) ^ 3 := by ring
          _ ≤ r ^ 3 := hlower
      calc
        R ^ 3 / 8 *
              densityCubeQuotient (R / 2)
                (endpointPhysicalPoint (R / 2)
                  (prescribedDensityCoordinates p) 0) - r ^ 3
            < R ^ 3 / 8 * 14 - r ^ 3 :=
          sub_lt_sub_right hscaled _
        _ < 0 := by
          apply sub_neg.mpr
          exact lt_of_lt_of_le
            (by
              calc
                R ^ 3 / 8 * 14 = (7 / 4 : ℝ) * R ^ 3 := by ring
                _ < 8 * R ^ 3 :=
                  mul_lt_mul_of_pos_right (by norm_num) hR3)
            hlower'
    · intro hface
      have hs : prescribedDensityScale p = R := by
        simpa [prescribedDensityScale, fixedPrescribedDensityBoxUpper] using hface
      have hR100 : R < (1 / 100 : ℝ) :=
        hRupper.trans_lt (by norm_num)
      have hquot := endpointBox_densityCubeQuotient_bounds
        (s := R) hRpos hR100 (prescribedDensityCoordinates p) hmem.1
      have hscaled := mul_lt_mul_of_pos_left hquot.1 (pow_pos hRpos 3)
      change 0 < prescribedDensityRow r (prescribedDensityScale p)
        (prescribedDensityCoordinates p)
      rw [hs, prescribedDensityRow]
      apply sub_pos.mpr
      calc
        r ^ 3 ≤ 251 / 20 * R ^ 3 := hupper
        _ = R ^ 3 * (251 / 20) := by ring
        _ < R ^ 3 * densityCubeQuotient R
            (endpointPhysicalPoint R (prescribedDensityCoordinates p) 0) := hscaled

private theorem fixedPrescribedDensityCell {R r : ℝ}
    (hRpos : 0 < R) (hRupper : R ≤ 1 / 126334)
    (hrpos : 0 < r) (hr50 : r < 1 / 50)
    (hlower : (2 * R) ^ 3 ≤ r ^ 3)
    (hupper : r ^ 3 ≤ 251 / 20 * R ^ 3) :
    ∃ s q, R / 2 < s ∧ s < R ∧ s < 1 / 100 ∧ InEndpointBox q ∧
      rescaledOrientedNearOneMap s q = 0 ∧
      density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
  have hbox : ∀ i,
      fixedPrescribedDensityBoxLower R i <
        fixedPrescribedDensityBoxUpper R i := by
    intro i
    fin_cases i <;>
      simp [fixedPrescribedDensityBoxLower, fixedPrescribedDensityBoxUpper] <;>
      linarith
  have hcontinuous :=
    continuousOn_fixedPrescribedDensityAugmentedMap hRpos hrpos hr50 hlower
  have hfaces := fixedCell_augmented_faces hRpos hRupper hlower hupper
  obtain ⟨p, hp, hzero⟩ := BoxPoincareMiranda.poincareMiranda hbox
    (prescribedDensityAugmentedMap r) hcontinuous
    (fun p hp i hi => (hfaces p hp i).1 hi |>.le)
    (fun p hp i hi => (hfaces p hp i).2 hi |>.le)
  let s := prescribedDensityScale p
  let q := prescribedDensityCoordinates p
  have hmem : InEndpointBox q ∧ s ∈ Icc (R / 2) R := by
    simpa [s, q] using fixedPrescribedDensityBox_membership hp
  have hrow : prescribedDensityRow r s q = 0 := by
    have h := congrFun hzero (3 : Fin 4)
    simpa [prescribedDensityAugmentedMap, s, q] using h
  have hsLower : R / 2 < s := by
    apply lt_of_le_of_ne hmem.2.1
    intro h
    have hneg := (hfaces p hp (3 : Fin 4)).1
    have hpface : p 3 = fixedPrescribedDensityBoxLower R 3 := by
      simpa [s, prescribedDensityScale, fixedPrescribedDensityBoxLower] using h.symm
    have : prescribedDensityAugmentedMap r p 3 < 0 := hneg hpface
    have : prescribedDensityRow r s q < 0 := by
      simpa [prescribedDensityAugmentedMap, s, q] using this
    rw [hrow] at this
    exact (lt_irrefl (0 : ℝ)) this
  have hsUpper : s < R := by
    apply lt_of_le_of_ne hmem.2.2
    intro h
    have hpos := (hfaces p hp (3 : Fin 4)).2
    have hpface : p 3 = fixedPrescribedDensityBoxUpper R 3 := by
      simpa [s, prescribedDensityScale, fixedPrescribedDensityBoxUpper] using h
    have : 0 < prescribedDensityAugmentedMap r p 3 := hpos hpface
    have : 0 < prescribedDensityRow r s q := by
      simpa [prescribedDensityAugmentedMap, s, q] using this
    rw [hrow] at this
    exact (lt_irrefl (0 : ℝ)) this
  have hspos : 0 < s := lt_trans (by positivity) hsLower
  have hs100 : s < 1 / 100 :=
    hsUpper.trans (hRupper.trans_lt (by norm_num))
  have hmap : rescaledOrientedNearOneMap s q = 0 := by
    funext i
    fin_cases i
    · have h := congrFun hzero (0 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
    · have h := congrFun hzero (1 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
    · have h := congrFun hzero (2 : Fin 4)
      simpa [prescribedDensityAugmentedMap, s, q] using h
  have hySq := (endpointBox_principalChart hspos hs100 q hmem.1).1
  have hy : 1 - yCoord s (endpointPhysicalPoint s q 0) ^ 2 ≠ 0 := by
    nlinarith
  have hdensity := density_sub_one_eq_cube_mul
    s (endpointPhysicalPoint s q 0) hy
  have hdensityTarget :
      density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 := by
    rw [prescribedDensityRow] at hrow
    linarith
  exact ⟨s, q, hsLower, hsUpper, hs100, hmem.1, hmap, hdensityTarget⟩

private theorem fixedPrescribedDensityCell_strictImprovement {R r : ℝ}
    (hRpos : 0 < R) (hRupper : R ≤ 1 / 126334)
    (hrpos : 0 < r) (hr50 : r < 1 / 50)
    (hlower : (2 * R) ^ 3 ≤ r ^ 3)
    (hupper : r ^ 3 ≤ 251 / 20 * R ^ 3) :
    ∃ s q, R / 2 < s ∧ s < R ∧ InEndpointBox q ∧
      rescaledOrientedNearOneMap s q = 0 ∧
      density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 ∧
      (let x := endpointPhysicalPoint s q
       ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (1 + r ^ 3),
         pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
         pair.h₄ = halfCos s ∧
         1 < 1 + r ^ 3 ∧ 1 + r ^ 3 < (51 / 50 : ℝ) ∧
         LeanSuffixAnalytic.typeThreeFold (1 + r ^ 3) pair.h₃ < 0 ∧
         LeanSuffixAnalytic.reducedFoldGap (1 + r ^ 3) pair.h₃ pair.h₄ < 0 ∧
         LeanSuffixAnalytic.typeThreePerimeter (1 + r ^ 3) pair.h₃ <
           LeanSuffixAnalytic.typeFourPerimeter (1 + r ^ 3) pair.h₄) := by
  obtain ⟨s, q, hsLower, hsUpper, hs100, hq, hroot, hdensity⟩ :=
    fixedPrescribedDensityCell hRpos hRupper hrpos hr50 hlower hupper
  have hspos : 0 < s := lt_trans (by positivity) hsLower
  have hsWidened : s ≤ 1 / 126334 :=
    hsUpper.le.trans hRupper
  have hgap : poleFreeReducedGap s q < 0 :=
    (explicit_poleFreeReducedGap_neg q hspos.le hsWidened hq).trans
      (by norm_num)
  have hstrict :=
    stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
      hspos hs100 hq hroot hgap
  dsimp only at hstrict
  rw [hdensity] at hstrict
  exact ⟨s, q, hsLower, hsUpper, hq, hroot, hdensity, hstrict⟩

private theorem prescribedDensity_lambda_explicit_fixed_cell {R : ℝ}
    (hRpos : 0 < R) (hRupper : R ≤ 1 / 126334) :
    ∀ («λ» : ℝ),
      1 + (2 * R) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * R ^ 3 →
      ∃ s q, R / 2 < s ∧ s < R ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have htarget : lam - 1 ∈ Icc ((2 * R) ^ 3) ((3 * R) ^ 3) := by
    constructor
    · linarith
    · calc
        lam - 1 ≤ 251 / 20 * R ^ 3 := by linarith
        _ ≤ (3 * R) ^ 3 := by
          nlinarith [pow_pos hRpos 3]
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3)
      (Icc (2 * R) (3 * R)) :=
    continuous_pow 3 |>.continuousOn
  rcases intermediate_value_Icc
      (show 2 * R ≤ 3 * R by linarith)
      hcont htarget with ⟨r, hr, hrpow⟩
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr.1
  have hr50 : r < 1 / 50 := by
    calc
      r ≤ 3 * R := hr.2
      _ ≤ 3 * (1 / 126334 : ℝ) :=
        mul_le_mul_of_nonneg_left hRupper (by norm_num)
      _ < 1 / 50 := by norm_num
  have hlower : (2 * R) ^ 3 ≤ r ^ 3 :=
    htarget.1.trans_eq hrpow.symm
  have hupper : r ^ 3 ≤ 251 / 20 * R ^ 3 :=
    hrpow.trans_le (by linarith)
  obtain ⟨s, q, hsLower, hsUpper, hq, hroot, hdensity, hstrict⟩ :=
    fixedPrescribedDensityCell_strictImprovement
      hRpos hRupper hrpos hr50 hlower hupper
  have htwos : 2 * s < r := by
    calc
      2 * s < 2 * R := mul_lt_mul_of_pos_left hsUpper (by norm_num)
      _ ≤ r := hr.1
  have hspos : 0 < s := lt_trans (by positivity) hsLower
  have hcube : (2 * s) ^ 3 < r ^ 3 :=
    pow_lt_pow_left₀ htwos (by positivity) (by norm_num)
  have hscale : 8 * s ^ 3 < lam - 1 := by
    norm_num [mul_pow] at hcube
    linarith
  have hrlam : 1 + r ^ 3 = lam := by linarith
  rw [hrlam] at hdensity hstrict
  exact ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

private abbrev secondCellRadius : ℝ := 1 / 200000

/-- The adjacent prescribed-density prism covers the first seam and extends
strict improvement through `λ = 1 + (251 / 20) / 200000³`. -/
theorem prescribedDensity_lambda_explicit_second_cell :
    ∀ («λ» : ℝ),
      1 + (2 * (1 / 200000 : ℝ)) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 200000 : ℝ) ^ 3 →
      ∃ s q, 1 / 400000 < s ∧ s < 1 / 200000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := secondCellRadius) (by norm_num [secondCellRadius])
    (by norm_num [secondCellRadius]) lam
    (by simpa [secondCellRadius] using hlamLower)
    (by simpa [secondCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 400000 < s := by
    calc
      1 / 400000 = secondCellRadius / 2 := by norm_num [secondCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 200000 := by
    simpa [secondCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirdCellRadius : ℝ := 1 / 180000

/-- The next fixed prescribed-density prism starts at the exact preceding seam
and extends strict improvement through `λ = 1 + (251 / 20) / 180000³`. -/
theorem prescribedDensity_lambda_explicit_third_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 200000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 180000 : ℝ) ^ 3 →
      ∃ s q, 1 / 360000 < s ∧ s < 1 / 180000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirdCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirdCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 200000 : ℝ) ^ 3 := by
        norm_num [thirdCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirdCellRadius) (by norm_num [thirdCellRadius])
    (by norm_num [thirdCellRadius]) lam hcanonicalLower
    (by simpa [thirdCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 360000 < s := by
    calc
      1 / 360000 = thirdCellRadius / 2 := by norm_num [thirdCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 180000 := by
    simpa [thirdCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev fourthCellRadius : ℝ := 1 / 179668

/-- The fourth fixed prescribed-density prism starts at the exact preceding
seam and extends strict improvement through
`λ = 1 + (251 / 20) / 179668³`. -/
theorem prescribedDensity_lambda_explicit_fourth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 180000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 179668 : ℝ) ^ 3 →
      ∃ s q, 1 / 359336 < s ∧ s < 1 / 179668 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * fourthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * fourthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 180000 : ℝ) ^ 3 := by
        norm_num [fourthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := fourthCellRadius) (by norm_num [fourthCellRadius])
    (by norm_num [fourthCellRadius]) lam hcanonicalLower
    (by simpa [fourthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 359336 < s := by
    calc
      1 / 359336 = fourthCellRadius / 2 := by norm_num [fourthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 179668 := by
    simpa [fourthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev fifthCellRadius : ℝ := 1 / 170000

/-- The fifth fixed prescribed-density prism starts at the exact preceding
seam and extends strict improvement through
`λ = 1 + (251 / 20) / 170000³`. -/
theorem prescribedDensity_lambda_explicit_fifth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 179668 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 170000 : ℝ) ^ 3 →
      ∃ s q, 1 / 340000 < s ∧ s < 1 / 170000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * fifthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * fifthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 179668 : ℝ) ^ 3 := by
        norm_num [fifthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := fifthCellRadius) (by norm_num [fifthCellRadius])
    (by norm_num [fifthCellRadius]) lam hcanonicalLower
    (by simpa [fifthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 340000 < s := by
    calc
      1 / 340000 = fifthCellRadius / 2 := by norm_num [fifthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 170000 := by
    simpa [fifthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev sixthCellRadius : ℝ := 1 / 168000

/-- The sixth fixed prescribed-density prism starts at the exact preceding
seam and extends strict improvement through
`λ = 1 + (251 / 20) / 168000³`. -/
theorem prescribedDensity_lambda_explicit_sixth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 170000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 168000 : ℝ) ^ 3 →
      ∃ s q, 1 / 336000 < s ∧ s < 1 / 168000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * sixthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * sixthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 170000 : ℝ) ^ 3 := by
        norm_num [sixthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := sixthCellRadius) (by norm_num [sixthCellRadius])
    (by norm_num [sixthCellRadius]) lam hcanonicalLower
    (by simpa [sixthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 336000 < s := by
    calc
      1 / 336000 = sixthCellRadius / 2 := by norm_num [sixthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 168000 := by
    simpa [sixthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev seventhCellRadius : ℝ := 1 / 167500

/-- The seventh fixed prescribed-density prism starts at the exact preceding
seam and extends strict improvement through
`λ = 1 + (251 / 20) / 167500³`. -/
theorem prescribedDensity_lambda_explicit_seventh_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 168000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 167500 : ℝ) ^ 3 →
      ∃ s q, 1 / 335000 < s ∧ s < 1 / 167500 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * seventhCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * seventhCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 168000 : ℝ) ^ 3 := by
        norm_num [seventhCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := seventhCellRadius) (by norm_num [seventhCellRadius])
    (by norm_num [seventhCellRadius]) lam hcanonicalLower
    (by simpa [seventhCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 335000 < s := by
    calc
      1 / 335000 = seventhCellRadius / 2 := by norm_num [seventhCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 167500 := by
    simpa [seventhCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev eighthCellRadius : ℝ := 1 / 167401

/-- The eighth fixed prescribed-density prism starts at the exact preceding
seam and extends strict improvement through
`λ = 1 + (251 / 20) / 167401³`. -/
theorem prescribedDensity_lambda_explicit_eighth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 167500 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 167401 : ℝ) ^ 3 →
      ∃ s q, 1 / 334802 < s ∧ s < 1 / 167401 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * eighthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * eighthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 167500 : ℝ) ^ 3 := by
        norm_num [eighthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := eighthCellRadius) (by norm_num [eighthCellRadius])
    (by norm_num [eighthCellRadius]) lam hcanonicalLower
    (by simpa [eighthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 334802 < s := by
    calc
      1 / 334802 = eighthCellRadius / 2 := by norm_num [eighthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 167401 := by
    simpa [eighthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev ninthCellRadius : ℝ := 1 / 164000

/-- The ninth prescribed-density cell (the eighth fixed prism) starts at the
exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 164000³`. -/
theorem prescribedDensity_lambda_explicit_ninth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 167401 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 164000 : ℝ) ^ 3 →
      ∃ s q, 1 / 328000 < s ∧ s < 1 / 164000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * ninthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * ninthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 167401 : ℝ) ^ 3 := by
        norm_num [ninthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := ninthCellRadius) (by norm_num [ninthCellRadius])
    (by norm_num [ninthCellRadius]) lam hcanonicalLower
    (by simpa [ninthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 328000 < s := by
    calc
      1 / 328000 = ninthCellRadius / 2 := by norm_num [ninthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 164000 := by
    simpa [ninthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev tenthCellRadius : ℝ := 1 / 163935

/-- The tenth prescribed-density cell (the ninth fixed prism) starts at the
exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 163935³`. -/
theorem prescribedDensity_lambda_explicit_tenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 164000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 163935 : ℝ) ^ 3 →
      ∃ s q, 1 / 327870 < s ∧ s < 1 / 163935 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * tenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * tenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 164000 : ℝ) ^ 3 := by
        norm_num [tenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := tenthCellRadius) (by norm_num [tenthCellRadius])
    (by norm_num [tenthCellRadius]) lam hcanonicalLower
    (by simpa [tenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 327870 < s := by
    calc
      1 / 327870 = tenthCellRadius / 2 := by norm_num [tenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 163935 := by
    simpa [tenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev eleventhCellRadius : ℝ := 1 / 161000

/-- The eleventh prescribed-density cell (the tenth fixed prism) starts at the
exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 161000³`. -/
theorem prescribedDensity_lambda_explicit_eleventh_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 163935 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 161000 : ℝ) ^ 3 →
      ∃ s q, 1 / 322000 < s ∧ s < 1 / 161000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * eleventhCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * eleventhCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 163935 : ℝ) ^ 3 := by
        norm_num [eleventhCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := eleventhCellRadius) (by norm_num [eleventhCellRadius])
    (by norm_num [eleventhCellRadius]) lam hcanonicalLower
    (by simpa [eleventhCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 322000 < s := by
    calc
      1 / 322000 = eleventhCellRadius / 2 := by norm_num [eleventhCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 161000 := by
    simpa [eleventhCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twelfthCellRadius : ℝ := 1 / 160900

/-- The twelfth prescribed-density cell (the eleventh fixed prism) starts at
the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160900³`. -/
theorem prescribedDensity_lambda_explicit_twelfth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 161000 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160900 : ℝ) ^ 3 →
      ∃ s q, 1 / 321800 < s ∧ s < 1 / 160900 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twelfthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twelfthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 161000 : ℝ) ^ 3 := by
        norm_num [twelfthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twelfthCellRadius) (by norm_num [twelfthCellRadius])
    (by norm_num [twelfthCellRadius]) lam hcanonicalLower
    (by simpa [twelfthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321800 < s := by
    calc
      1 / 321800 = twelfthCellRadius / 2 := by norm_num [twelfthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160900 := by
    simpa [twelfthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirteenthCellRadius : ℝ := 1 / 160829

/-- The thirteenth prescribed-density cell (the twelfth fixed prism) starts at
the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160829³`. -/
theorem prescribedDensity_lambda_explicit_thirteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160900 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160829 : ℝ) ^ 3 →
      ∃ s q, 1 / 321658 < s ∧ s < 1 / 160829 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160900 : ℝ) ^ 3 := by
        norm_num [thirteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirteenthCellRadius) (by norm_num [thirteenthCellRadius])
    (by norm_num [thirteenthCellRadius]) lam hcanonicalLower
    (by simpa [thirteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321658 < s := by
    calc
      1 / 321658 = thirteenthCellRadius / 2 := by norm_num [thirteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160829 := by
    simpa [thirteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev fourteenthCellRadius : ℝ := 1 / 160817

/-- The fourteenth prescribed-density cell (the thirteenth fixed prism) starts
at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160817³`. -/
theorem prescribedDensity_lambda_explicit_fourteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160829 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160817 : ℝ) ^ 3 →
      ∃ s q, 1 / 321634 < s ∧ s < 1 / 160817 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * fourteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * fourteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160829 : ℝ) ^ 3 := by
        norm_num [fourteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := fourteenthCellRadius) (by norm_num [fourteenthCellRadius])
    (by norm_num [fourteenthCellRadius]) lam hcanonicalLower
    (by simpa [fourteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321634 < s := by
    calc
      1 / 321634 = fourteenthCellRadius / 2 := by norm_num [fourteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160817 := by
    simpa [fourteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev fifteenthCellRadius : ℝ := 1 / 160778

/-- The fifteenth prescribed-density cell (the fourteenth fixed prism) starts
at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160778³`. -/
theorem prescribedDensity_lambda_explicit_fifteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160817 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160778 : ℝ) ^ 3 →
      ∃ s q, 1 / 321556 < s ∧ s < 1 / 160778 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * fifteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * fifteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160817 : ℝ) ^ 3 := by
        norm_num [fifteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := fifteenthCellRadius) (by norm_num [fifteenthCellRadius])
    (by norm_num [fifteenthCellRadius]) lam hcanonicalLower
    (by simpa [fifteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321556 < s := by
    calc
      1 / 321556 = fifteenthCellRadius / 2 := by norm_num [fifteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160778 := by
    simpa [fifteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev sixteenthCellRadius : ℝ := 1 / 160777

/-- The sixteenth prescribed-density cell (the fifteenth fixed prism) starts at
the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160777³`. -/
theorem prescribedDensity_lambda_explicit_sixteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160778 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160777 : ℝ) ^ 3 →
      ∃ s q, 1 / 321554 < s ∧ s < 1 / 160777 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * sixteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * sixteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160778 : ℝ) ^ 3 := by
        norm_num [sixteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := sixteenthCellRadius) (by norm_num [sixteenthCellRadius])
    (by norm_num [sixteenthCellRadius]) lam hcanonicalLower
    (by simpa [sixteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321554 < s := by
    calc
      1 / 321554 = sixteenthCellRadius / 2 := by norm_num [sixteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160777 := by
    simpa [sixteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev seventeenthCellRadius : ℝ := 1 / 160772

/-- The seventeenth prescribed-density cell (the sixteenth fixed prism) starts
at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160772³`. -/
theorem prescribedDensity_lambda_explicit_seventeenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160777 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160772 : ℝ) ^ 3 →
      ∃ s q, 1 / 321544 < s ∧ s < 1 / 160772 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * seventeenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * seventeenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160777 : ℝ) ^ 3 := by
        norm_num [seventeenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := seventeenthCellRadius) (by norm_num [seventeenthCellRadius])
    (by norm_num [seventeenthCellRadius]) lam hcanonicalLower
    (by simpa [seventeenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321544 < s := by
    calc
      1 / 321544 = seventeenthCellRadius / 2 := by
        norm_num [seventeenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160772 := by
    simpa [seventeenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev eighteenthCellRadius : ℝ := 1 / 160771

/-- The eighteenth prescribed-density cell (the seventeenth fixed prism)
starts at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160771³`. -/
theorem prescribedDensity_lambda_explicit_eighteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160772 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160771 : ℝ) ^ 3 →
      ∃ s q, 1 / 321542 < s ∧ s < 1 / 160771 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * eighteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * eighteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160772 : ℝ) ^ 3 := by
        norm_num [eighteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := eighteenthCellRadius) (by norm_num [eighteenthCellRadius])
    (by norm_num [eighteenthCellRadius]) lam hcanonicalLower
    (by simpa [eighteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321542 < s := by
    calc
      1 / 321542 = eighteenthCellRadius / 2 := by
        norm_num [eighteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160771 := by
    simpa [eighteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev nineteenthCellRadius : ℝ := 1 / 160770

/-- The nineteenth prescribed-density cell (the eighteenth fixed prism)
starts at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160770³`. -/
theorem prescribedDensity_lambda_explicit_nineteenth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160771 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160770 : ℝ) ^ 3 →
      ∃ s q, 1 / 321540 < s ∧ s < 1 / 160770 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * nineteenthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * nineteenthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160771 : ℝ) ^ 3 := by
        norm_num [nineteenthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := nineteenthCellRadius) (by norm_num [nineteenthCellRadius])
    (by norm_num [nineteenthCellRadius]) lam hcanonicalLower
    (by simpa [nineteenthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321540 < s := by
    calc
      1 / 321540 = nineteenthCellRadius / 2 := by
        norm_num [nineteenthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160770 := by
    simpa [nineteenthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentiethCellRadius : ℝ := 1 / 160769

/-- The twentieth prescribed-density cell (the nineteenth fixed prism) starts
at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160769³`. -/
theorem prescribedDensity_lambda_explicit_twentieth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160770 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160769 : ℝ) ^ 3 →
      ∃ s q, 1 / 321538 < s ∧ s < 1 / 160769 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentiethCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentiethCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160770 : ℝ) ^ 3 := by
        norm_num [twentiethCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentiethCellRadius) (by norm_num [twentiethCellRadius])
    (by norm_num [twentiethCellRadius]) lam hcanonicalLower
    (by simpa [twentiethCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321538 < s := by
    calc
      1 / 321538 = twentiethCellRadius / 2 := by
        norm_num [twentiethCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160769 := by
    simpa [twentiethCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyFirstCellRadius : ℝ := 1 / 160545

/-- The twenty-first prescribed-density cell (the twentieth fixed prism) starts
at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 160545³`. -/
theorem prescribedDensity_lambda_explicit_twenty_first_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160769 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160545 : ℝ) ^ 3 →
      ∃ s q, 1 / 321090 < s ∧ s < 1 / 160545 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyFirstCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyFirstCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160769 : ℝ) ^ 3 := by
        norm_num [twentyFirstCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyFirstCellRadius) (by norm_num [twentyFirstCellRadius])
    (by norm_num [twentyFirstCellRadius]) lam hcanonicalLower
    (by simpa [twentyFirstCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 321090 < s := by
    calc
      1 / 321090 = twentyFirstCellRadius / 2 := by
        norm_num [twentyFirstCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 160545 := by
    simpa [twentyFirstCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentySecondCellRadius : ℝ := 1 / 138170

/-- The twenty-second prescribed-density cell (the twenty-first fixed prism)
starts at the exact preceding seam and extends strict improvement through
`λ = 1 + (251 / 20) / 138170³`. -/
theorem prescribedDensity_lambda_explicit_twenty_second_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 160545 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 138170 : ℝ) ^ 3 →
      ∃ s q, 1 / 276340 < s ∧ s < 1 / 138170 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentySecondCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentySecondCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 160545 : ℝ) ^ 3 := by
        norm_num [twentySecondCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentySecondCellRadius) (by norm_num [twentySecondCellRadius])
    (by norm_num [twentySecondCellRadius]) lam hcanonicalLower
    (by simpa [twentySecondCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 276340 < s := by
    calc
      1 / 276340 = twentySecondCellRadius / 2 := by
        norm_num [twentySecondCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 138170 := by
    simpa [twentySecondCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyThirdCellRadius : ℝ := 1 / 130730

/-- The twenty-third prescribed-density cell (the twenty-second fixed prism)
starts at the exact preceding seam and reaches the full common face radius:
`λ = 1 + (251 / 20) / 130730³`. -/
theorem prescribedDensity_lambda_explicit_twenty_third_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 138170 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 130730 : ℝ) ^ 3 →
      ∃ s q, 1 / 261460 < s ∧ s < 1 / 130730 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyThirdCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyThirdCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 138170 : ℝ) ^ 3 := by
        norm_num [twentyThirdCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyThirdCellRadius) (by norm_num [twentyThirdCellRadius])
    (by norm_num [twentyThirdCellRadius]) lam hcanonicalLower
    (by simpa [twentyThirdCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 261460 < s := by
    calc
      1 / 261460 = twentyThirdCellRadius / 2 := by
        norm_num [twentyThirdCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 130730 := by
    simpa [twentyThirdCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyFourthCellRadius : ℝ := 1 / 128797

/-- The twenty-fourth prescribed-density cell (the twenty-third fixed prism)
starts at the exact preceding seam and reaches the enlarged common face radius:
`λ = 1 + (251 / 20) / 128797³`. -/
theorem prescribedDensity_lambda_explicit_twenty_fourth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 130730 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128797 : ℝ) ^ 3 →
      ∃ s q, 1 / 257594 < s ∧ s < 1 / 128797 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyFourthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyFourthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 130730 : ℝ) ^ 3 := by
        norm_num [twentyFourthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyFourthCellRadius) (by norm_num [twentyFourthCellRadius])
    (by norm_num [twentyFourthCellRadius]) lam hcanonicalLower
    (by simpa [twentyFourthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 257594 < s := by
    calc
      1 / 257594 = twentyFourthCellRadius / 2 := by
        norm_num [twentyFourthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128797 := by
    simpa [twentyFourthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyFifthCellRadius : ℝ := 1 / 128788

/-- The twenty-fifth prescribed-density cell (the twenty-fourth fixed prism)
starts at the exact preceding seam and reaches the sharpened common face radius:
`λ = 1 + (251 / 20) / 128788³`. -/
theorem prescribedDensity_lambda_explicit_twenty_fifth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128797 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128788 : ℝ) ^ 3 →
      ∃ s q, 1 / 257576 < s ∧ s < 1 / 128788 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyFifthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyFifthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128797 : ℝ) ^ 3 := by
        norm_num [twentyFifthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyFifthCellRadius) (by norm_num [twentyFifthCellRadius])
    (by norm_num [twentyFifthCellRadius]) lam hcanonicalLower
    (by simpa [twentyFifthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 257576 < s := by
    calc
      1 / 257576 = twentyFifthCellRadius / 2 := by
        norm_num [twentyFifthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128788 := by
    simpa [twentyFifthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentySixthCellRadius : ℝ := 1 / 128489

/-- The twenty-sixth prescribed-density cell (the twenty-fifth fixed prism)
starts at the exact preceding seam and reaches the next exact seam:
`λ = 1 + (251 / 20) / 128489³`. -/
theorem prescribedDensity_lambda_explicit_twenty_sixth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128788 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128489 : ℝ) ^ 3 →
      ∃ s q, 1 / 256978 < s ∧ s < 1 / 128489 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentySixthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentySixthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128788 : ℝ) ^ 3 := by
        norm_num [twentySixthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentySixthCellRadius) (by norm_num [twentySixthCellRadius])
    (by norm_num [twentySixthCellRadius]) lam hcanonicalLower
    (by simpa [twentySixthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256978 < s := by
    calc
      1 / 256978 = twentySixthCellRadius / 2 := by
        norm_num [twentySixthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128489 := by
    simpa [twentySixthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentySeventhCellRadius : ℝ := 1 / 128399

/-- The twenty-seventh prescribed-density cell (the twenty-sixth fixed prism)
starts at the exact preceding seam and reaches the sharpened common face radius:
`λ = 1 + (251 / 20) / 128399³`. -/
theorem prescribedDensity_lambda_explicit_twenty_seventh_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128489 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128399 : ℝ) ^ 3 →
      ∃ s q, 1 / 256798 < s ∧ s < 1 / 128399 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentySeventhCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentySeventhCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128489 : ℝ) ^ 3 := by
        norm_num [twentySeventhCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentySeventhCellRadius) (by norm_num [twentySeventhCellRadius])
    (by norm_num [twentySeventhCellRadius]) lam hcanonicalLower
    (by simpa [twentySeventhCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256798 < s := by
    calc
      1 / 256798 = twentySeventhCellRadius / 2 := by
        norm_num [twentySeventhCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128399 := by
    simpa [twentySeventhCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyEighthCellRadius : ℝ := 1 / 128394

/-- The twenty-eighth prescribed-density cell (the twenty-seventh fixed prism)
starts at the exact preceding seam and reaches the sharpened common face radius:
`λ = 1 + (251 / 20) / 128394³`. -/
theorem prescribedDensity_lambda_explicit_twenty_eighth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128399 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128394 : ℝ) ^ 3 →
      ∃ s q, 1 / 256788 < s ∧ s < 1 / 128394 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyEighthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyEighthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128399 : ℝ) ^ 3 := by
        norm_num [twentyEighthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyEighthCellRadius) (by norm_num [twentyEighthCellRadius])
    (by norm_num [twentyEighthCellRadius]) lam hcanonicalLower
    (by simpa [twentyEighthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256788 < s := by
    calc
      1 / 256788 = twentyEighthCellRadius / 2 := by
        norm_num [twentyEighthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128394 := by
    simpa [twentyEighthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev twentyNinthCellRadius : ℝ := 1 / 128389

/-- The twenty-ninth prescribed-density cell (the twenty-eighth fixed prism)
starts at the exact preceding seam and reaches the sharpened common face radius:
`λ = 1 + (251 / 20) / 128389³`. -/
theorem prescribedDensity_lambda_explicit_twenty_ninth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128394 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128389 : ℝ) ^ 3 →
      ∃ s q, 1 / 256778 < s ∧ s < 1 / 128389 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * twentyNinthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * twentyNinthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128394 : ℝ) ^ 3 := by
        norm_num [twentyNinthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := twentyNinthCellRadius) (by norm_num [twentyNinthCellRadius])
    (by norm_num [twentyNinthCellRadius]) lam hcanonicalLower
    (by simpa [twentyNinthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256778 < s := by
    calc
      1 / 256778 = twentyNinthCellRadius / 2 := by
        norm_num [twentyNinthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128389 := by
    simpa [twentyNinthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirtiethCellRadius : ℝ := 1 / 128385

/-- The thirtieth prescribed-density cell (the twenty-ninth fixed prism)
starts at the exact preceding seam and reaches the rho-sharpened common face
radius: `λ = 1 + (251 / 20) / 128385³`. -/
theorem prescribedDensity_lambda_explicit_thirtieth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128389 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128385 : ℝ) ^ 3 →
      ∃ s q, 1 / 256770 < s ∧ s < 1 / 128385 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirtiethCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirtiethCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128389 : ℝ) ^ 3 := by
        norm_num [thirtiethCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirtiethCellRadius) (by norm_num [thirtiethCellRadius])
    (by norm_num [thirtiethCellRadius]) lam hcanonicalLower
    (by simpa [thirtiethCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256770 < s := by
    calc
      1 / 256770 = thirtiethCellRadius / 2 := by
        norm_num [thirtiethCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128385 := by
    simpa [thirtiethCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirtyFirstCellRadius : ℝ := 1 / 128384

/-- The thirty-first prescribed-density cell (the thirtieth fixed prism)
starts at the exact preceding seam and reaches the common face radius
`λ = 1 + (251 / 20) / 128384³`. -/
theorem prescribedDensity_lambda_explicit_thirty_first_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128385 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128384 : ℝ) ^ 3 →
      ∃ s q, 1 / 256768 < s ∧ s < 1 / 128384 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirtyFirstCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirtyFirstCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128385 : ℝ) ^ 3 := by
        norm_num [thirtyFirstCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirtyFirstCellRadius) (by norm_num [thirtyFirstCellRadius])
    (by norm_num [thirtyFirstCellRadius]) lam hcanonicalLower
    (by simpa [thirtyFirstCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 256768 < s := by
    calc
      1 / 256768 = thirtyFirstCellRadius / 2 := by
        norm_num [thirtyFirstCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 128384 := by
    simpa [thirtyFirstCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirtySecondCellRadius : ℝ := 1 / 127280

/-- The thirty-second prescribed-density cell (the thirty-first fixed prism)
starts at the exact preceding seam and reaches the previous common face radius:
`λ = 1 + (251 / 20) / 127280³`. -/
theorem prescribedDensity_lambda_explicit_thirty_second_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 128384 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 127280 : ℝ) ^ 3 →
      ∃ s q, 1 / 254560 < s ∧ s < 1 / 127280 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirtySecondCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirtySecondCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 128384 : ℝ) ^ 3 := by
        norm_num [thirtySecondCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirtySecondCellRadius) (by norm_num [thirtySecondCellRadius])
    (by norm_num [thirtySecondCellRadius]) lam hcanonicalLower
    (by simpa [thirtySecondCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 254560 < s := by
    calc
      1 / 254560 = thirtySecondCellRadius / 2 := by
        norm_num [thirtySecondCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 127280 := by
    simpa [thirtySecondCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirtyThirdCellRadius : ℝ := 1 / 126341

/-- The thirty-third prescribed-density cell (the thirty-second fixed prism)
starts at the exact `1 / 127280` seam and reaches the widened common face
radius: `λ = 1 + (251 / 20) / 126341³`. -/
theorem prescribedDensity_lambda_explicit_thirty_third_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 127280 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 126341 : ℝ) ^ 3 →
      ∃ s q, 1 / 252682 < s ∧ s < 1 / 126341 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirtyThirdCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirtyThirdCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 127280 : ℝ) ^ 3 := by
        norm_num [thirtyThirdCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirtyThirdCellRadius) (by norm_num [thirtyThirdCellRadius])
    (by norm_num [thirtyThirdCellRadius]) lam hcanonicalLower
    (by simpa [thirtyThirdCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 252682 < s := by
    calc
      1 / 252682 = thirtyThirdCellRadius / 2 := by
        norm_num [thirtyThirdCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 126341 := by
    simpa [thirtyThirdCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

private abbrev thirtyFourthCellRadius : ℝ := 1 / 126334

/-- The thirty-fourth prescribed-density cell (the thirty-third fixed prism)
starts at the exact `1 / 126341` seam and reaches the widened common face
radius: `λ = 1 + (251 / 20) / 126334³`. -/
theorem prescribedDensity_lambda_explicit_thirty_fourth_cell :
    ∀ («λ» : ℝ),
      1 + (251 / 20 : ℝ) * (1 / 126341 : ℝ) ^ 3 ≤ «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 126334 : ℝ) ^ 3 →
      ∃ s q, 1 / 252668 < s ∧ s < 1 / 126334 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlamLower hlamUpper
  have hcanonicalLower :
      1 + (2 * thirtyFourthCellRadius) ^ 3 ≤ lam := by
    calc
      1 + (2 * thirtyFourthCellRadius) ^ 3 ≤
          1 + (251 / 20 : ℝ) * (1 / 126341 : ℝ) ^ 3 := by
        norm_num [thirtyFourthCellRadius]
      _ ≤ lam := hlamLower
  have hresult := prescribedDensity_lambda_explicit_fixed_cell
    (R := thirtyFourthCellRadius) (by norm_num [thirtyFourthCellRadius])
    (by norm_num [thirtyFourthCellRadius]) lam hcanonicalLower
    (by simpa [thirtyFourthCellRadius] using hlamUpper)
  obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ := hresult
  have hsLower' : 1 / 252668 < s := by
    calc
      1 / 252668 = thirtyFourthCellRadius / 2 := by
        norm_num [thirtyFourthCellRadius]
      _ < s := hsLower
  have hsUpper' : s < 1 / 126334 := by
    simpa [thirtyFourthCellRadius] using hsUpper
  exact ⟨s, q, hsLower', hsUpper', hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition through the seventh prescribed-density cell. -/
private theorem prescribedDensity_lambda_explicit_through_seventh :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 167500 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 167500 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hsixth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 168000 : ℝ) ^ 3
  · by_cases hfifth :
        lam ≤ 1 + (251 / 20 : ℝ) * (1 / 170000 : ℝ) ^ 3
    · by_cases hold :
          lam ≤ 1 + (251 / 20 : ℝ) * (1 / 179668 : ℝ) ^ 3
      · by_cases hthird :
            lam ≤ 1 + (251 / 20 : ℝ) * (1 / 180000 : ℝ) ^ 3
        · by_cases hprevious :
              lam ≤ 1 + (251 / 20 : ℝ) * (1 / 200000 : ℝ) ^ 3
          · by_cases hseam : lam < 1 + (2 * (1 / 200000 : ℝ)) ^ 3
            · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
                prescribedDensity_lambda_explicit_first_cell lam hlam hseam
              have hsUpper' : s < 1 / 167500 :=
                hsUpper.trans (by norm_num)
              exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
            · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
                prescribedDensity_lambda_explicit_second_cell lam
                  (le_of_not_gt hseam) hprevious
              have hspos : 0 < s := lt_trans (by norm_num) hsLower
              have hsUpper' : s < 1 / 167500 :=
                hsUpper.trans (by norm_num)
              exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
          · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
              prescribedDensity_lambda_explicit_third_cell lam
                (lt_of_not_ge hprevious).le hthird
            have hspos : 0 < s := lt_trans (by norm_num) hsLower
            have hsUpper' : s < 1 / 167500 :=
              hsUpper.trans (by norm_num)
            exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
        · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
            prescribedDensity_lambda_explicit_fourth_cell lam
              (lt_of_not_ge hthird).le hold
          have hspos : 0 < s := lt_trans (by norm_num) hsLower
          have hsUpper' : s < 1 / 167500 :=
            hsUpper.trans (by norm_num)
          exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
      · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
          prescribedDensity_lambda_explicit_fifth_cell lam
            (lt_of_not_ge hold).le hfifth
        have hspos : 0 < s := lt_trans (by norm_num) hsLower
        have hsUpper' : s < 1 / 167500 :=
          hsUpper.trans (by norm_num)
        exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
    · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_sixth_cell lam
          (lt_of_not_ge hfifth).le hsixth
      have hspos : 0 < s := lt_trans (by norm_num) hsLower
      have hsUpper' : s < 1 / 167500 :=
        hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_seventh_cell lam
        (lt_of_not_ge hsixth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
seven adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_eighth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 167401 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 167401 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hseventh :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 167500 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_seventh lam hlam hseventh
    have hsUpper' : s < 1 / 167401 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_eighth_cell lam
        (lt_of_not_ge hseventh).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all eight
adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_ninth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 164000 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 164000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases heighth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 167401 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_eighth lam hlam heighth
    have hsUpper' : s < 1 / 164000 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_ninth_cell lam
        (lt_of_not_ge heighth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all nine
adjacent fixed prisms through the tenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_tenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 163935 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 163935 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hninth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 164000 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_ninth lam hlam hninth
    have hsUpper' : s < 1 / 163935 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_tenth_cell lam
        (lt_of_not_ge hninth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all ten
adjacent fixed prisms through the eleventh cell. -/
private theorem prescribedDensity_lambda_explicit_through_eleventh :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 161000 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 161000 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 163935 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_tenth lam hlam htenth
    have hsUpper' : s < 1 / 161000 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_eleventh_cell lam
        (lt_of_not_ge htenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all eleven
adjacent fixed prisms through the twelfth cell. -/
private theorem prescribedDensity_lambda_explicit_through_twelfth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160900 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160900 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases heleventh :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 161000 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_eleventh lam hlam heleventh
    have hsUpper' : s < 1 / 160900 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twelfth_cell lam
        (lt_of_not_ge heleventh).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all twelve
adjacent fixed prisms through the thirteenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_thirteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160829 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160829 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwelfth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160900 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twelfth lam hlam htwelfth
    have hsUpper' : s < 1 / 160829 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_thirteenth_cell lam
        (lt_of_not_ge htwelfth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
thirteen adjacent fixed prisms through the fourteenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_fourteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160817 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160817 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hthirteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160829 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_thirteenth
        lam hlam hthirteenth
    have hsUpper' : s < 1 / 160817 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_fourteenth_cell lam
        (lt_of_not_ge hthirteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
fourteen adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_fifteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160778 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160778 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hfourteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160817 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_fourteenth
        lam hlam hfourteenth
    have hsUpper' : s < 1 / 160778 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_fifteenth_cell lam
        (lt_of_not_ge hfourteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
fifteen adjacent fixed prisms through the sixteenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_sixteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160777 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160777 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hfifteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160778 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_fifteenth
        lam hlam hfifteenth
    have hsUpper' : s < 1 / 160777 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_sixteenth_cell lam
        (lt_of_not_ge hfifteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
sixteen adjacent fixed prisms through the seventeenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_seventeenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160772 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160772 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hsixteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160777 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_sixteenth
        lam hlam hsixteenth
    have hsUpper' : s < 1 / 160772 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_seventeenth_cell lam
        (lt_of_not_ge hsixteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
seventeen adjacent fixed prisms through the eighteenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_eighteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160771 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160771 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hseventeenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160772 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_seventeenth
        lam hlam hseventeenth
    have hsUpper' : s < 1 / 160771 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_eighteenth_cell lam
        (lt_of_not_ge hseventeenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
eighteen adjacent fixed prisms through the nineteenth cell. -/
private theorem prescribedDensity_lambda_explicit_through_nineteenth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160770 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160770 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases heighteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160771 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_eighteenth
        lam hlam heighteenth
    have hsUpper' : s < 1 / 160770 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_nineteenth_cell lam
        (lt_of_not_ge heighteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
nineteen adjacent fixed prisms through the twentieth cell. -/
private theorem prescribedDensity_lambda_explicit_through_twentieth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160769 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160769 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hnineteenth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160770 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_nineteenth
        lam hlam hnineteenth
    have hsUpper' : s < 1 / 160769 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twentieth_cell lam
        (lt_of_not_ge hnineteenth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
twenty adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_first :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 160545 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 160545 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentieth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160769 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twentieth
        lam hlam htwentieth
    have hsUpper' : s < 1 / 160545 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_first_cell lam
        (lt_of_not_ge htwentieth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
twenty-one adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_second :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 138170 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 138170 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentyFirst :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 160545 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twenty_first
        lam hlam htwentyFirst
    have hsUpper' : s < 1 / 138170 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_second_cell lam
        (lt_of_not_ge htwentyFirst).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
twenty-two adjacent fixed prisms through the twenty-third cell. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_third :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 130730 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 130730 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentySecond :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 138170 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twenty_second
        lam hlam htwentySecond
    have hsUpper' : s < 1 / 130730 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_third_cell lam
        (lt_of_not_ge htwentySecond).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
twenty-three adjacent fixed prisms through the twenty-fourth cell. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_fourth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128797 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 128797 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentyThird :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 130730 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twenty_third
        lam hlam htwentyThird
    have hsUpper' : s < 1 / 128797 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_fourth_cell lam
        (lt_of_not_ge htwentyThird).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
twenty-five adjacent fixed prisms through the twenty-sixth cell. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_sixth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128489 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 128489 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentyFifth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128788 : ℝ) ^ 3
  · by_cases htwentyFourth :
        lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128797 : ℝ) ^ 3
    · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_through_twenty_fourth
          lam hlam htwentyFourth
      have hsUpper' : s < 1 / 128489 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
    · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_twenty_fifth_cell lam
          (lt_of_not_ge htwentyFourth).le htwentyFifth
      have hspos : 0 < s := lt_trans (by norm_num) hsLower
      have hsUpper' : s < 1 / 128489 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_sixth_cell lam
        (lt_of_not_ge htwentyFifth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
twenty-six adjacent fixed prisms through the twenty-seventh cell. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_seventh :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128399 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 128399 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentySixth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128489 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_twenty_sixth
        lam hlam htwentySixth
    have hsUpper' : s < 1 / 128399 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_seventh_cell lam
        (lt_of_not_ge htwentySixth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
twenty-eight adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_twenty_ninth :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128389 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 128389 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases htwentyEighth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128394 : ℝ) ^ 3
  · by_cases htwentySeventh :
        lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128399 : ℝ) ^ 3
    · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_through_twenty_seventh
          lam hlam htwentySeventh
      have hsUpper' : s < 1 / 128389 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
    · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_twenty_eighth_cell lam
          (lt_of_not_ge htwentySeventh).le htwentyEighth
      have hspos : 0 < s := lt_trans (by norm_num) hsLower
      have hsUpper' : s < 1 / 128389 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_twenty_ninth_cell lam
        (lt_of_not_ge htwentyEighth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
thirty adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_thirty_first :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 128384 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 128384 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hthirtieth :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128385 : ℝ) ^ 3
  · by_cases htwentyNinth :
        lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128389 : ℝ) ^ 3
    · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_through_twenty_ninth
          lam hlam htwentyNinth
      have hsUpper' : s < 1 / 128384 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
    · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
        prescribedDensity_lambda_explicit_thirtieth_cell lam
          (lt_of_not_ge htwentyNinth).le hthirtieth
      have hspos : 0 < s := lt_trans (by norm_num) hsLower
      have hsUpper' : s < 1 / 128384 := hsUpper.trans (by norm_num)
      exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_thirty_first_cell lam
        (lt_of_not_ge hthirtieth).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
thirty-one adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_thirty_second :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 127280 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 127280 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hthirtyFirst :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 128384 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_thirty_first lam hlam hthirtyFirst
    have hsUpper' : s < 1 / 127280 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_thirty_second_cell lam
        (lt_of_not_ge hthirtyFirst).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and the first
thirty-two adjacent fixed prisms. -/
private theorem prescribedDensity_lambda_explicit_through_thirty_third :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 126341 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 126341 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hthirtySecond :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 127280 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_thirty_second
        lam hlam hthirtySecond
    have hsUpper' : s < 1 / 126341 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_thirty_third_cell lam
        (lt_of_not_ge hthirtySecond).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Gap-free composition of the initial prescribed-density cell and all
thirty-three adjacent fixed prisms. -/
theorem prescribedDensity_lambda_explicit_combined :
    ∀ («λ» : ℝ), 1 < «λ» →
      «λ» ≤ 1 + (251 / 20 : ℝ) * (1 / 126334 : ℝ) ^ 3 →
      ∃ s q, 0 < s ∧ s < 1 / 126334 ∧
        8 * s ^ 3 < «λ» - 1 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  intro lam hlam hlamUpper
  by_cases hthirtyThird :
      lam ≤ 1 + (251 / 20 : ℝ) * (1 / 126341 : ℝ) ^ 3
  · obtain ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_through_thirty_third
        lam hlam hthirtyThird
    have hsUpper' : s < 1 / 126334 := hsUpper.trans (by norm_num)
    exact ⟨s, q, hspos, hsUpper', hscale, hq, hroot, hdensity, hstrict⟩
  · obtain ⟨s, q, hsLower, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩ :=
      prescribedDensity_lambda_explicit_thirty_fourth_cell lam
        (lt_of_not_ge hthirtyThird).le hlamUpper
    have hspos : 0 < s := lt_trans (by norm_num) hsLower
    exact ⟨s, q, hspos, hsUpper, hscale, hq, hroot, hdensity, hstrict⟩

/-- Every sufficiently small positive prescribed density increment is realized
by a stationary equal-area pair on the negative type-(iii) fold branch with
strict perimeter improvement. -/
theorem prescribedDensity_stationaryEqualAreaPair_strictImprovement :
    ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
      ∃ s q, 0 < s ∧ s < r / 2 ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = 1 + r ^ 3 ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (1 + r ^ 3),
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < 1 + r ^ 3 ∧ 1 + r ^ 3 < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold (1 + r ^ 3) pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap
               (1 + r ^ 3) pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter (1 + r ^ 3) pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter (1 + r ^ 3) pair.h₄) := by
  rcases prescribedDensity_nearOneRoot with ⟨r₁, hr₁, hroot⟩
  refine ⟨min r₁ (2 / 200000), lt_min hr₁ (by norm_num), ?_⟩
  intro r hr0 hrradius
  have hrr₁ : r < r₁ := lt_of_lt_of_le hrradius (min_le_left _ _)
  have hrbound : r < 2 / 200000 :=
    lt_of_lt_of_le hrradius (min_le_right _ _)
  rcases hroot r hr0 hrr₁ with
    ⟨s, q, hs0, hsr, hs100, hq, hrescaled, hdensity⟩
  have hsbound : s ≤ 1 / 200000 := by linarith
  have hgapq : poleFreeReducedGap s q < 0 :=
    (explicit_poleFreeReducedGap_neg q hs0.le (hsbound.trans (by norm_num)) hq).trans
      (by norm_num)
  have hstrict :=
    stationaryEqualAreaPair_strictImprovement_of_rescaled_root_gap
      hs0 hs100 hq hrescaled hgapq
  dsimp only at hstrict
  rw [hdensity] at hstrict
  exact ⟨s, q, hs0, hsr, hs100, hq, hrescaled, hdensity, hstrict⟩

/-- Every density in a sufficiently small open interval above one is realized
by the prescribed-density first cell, with all strict-improvement conclusions
expressed directly in terms of that density. -/
theorem prescribedDensity_lambda_stationaryEqualAreaPair_strictImprovement :
    ∃ δ > 0, ∀ («λ» : ℝ), 1 < «λ» → «λ» < 1 + δ →
      ∃ s q, 0 < s ∧ 8 * s ^ 3 < «λ» - 1 ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 ∧
        density s (endpointPhysicalPoint s q 0) = «λ» ∧
        (let x := endpointPhysicalPoint s q
         ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair «λ»,
           pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
           pair.h₄ = halfCos s ∧
           1 < «λ» ∧ «λ» < (51 / 50 : ℝ) ∧
           LeanSuffixAnalytic.typeThreeFold «λ» pair.h₃ < 0 ∧
           LeanSuffixAnalytic.reducedFoldGap «λ» pair.h₃ pair.h₄ < 0 ∧
           LeanSuffixAnalytic.typeThreePerimeter «λ» pair.h₃ <
             LeanSuffixAnalytic.typeFourPerimeter «λ» pair.h₄) := by
  rcases prescribedDensity_stationaryEqualAreaPair_strictImprovement with
    ⟨r₀, hr₀, hmain⟩
  refine ⟨r₀ ^ 3, by positivity, ?_⟩
  intro lam hLam hLamDelta
  have htarget0 : 0 ≤ lam - 1 := by linarith
  have htargetr₀ : lam - 1 ≤ r₀ ^ 3 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3) (Icc 0 r₀) :=
    continuous_pow 3 |>.continuousOn
  have htarget : lam - 1 ∈ Icc ((0 : ℝ) ^ 3) (r₀ ^ 3) := by
    simpa using And.intro htarget0 htargetr₀
  rcases intermediate_value_Icc hr₀.le hcont htarget with ⟨r, hr, hrpow⟩
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro hre
    subst r
    norm_num at hrpow
    linarith
  have hrr₀ : r < r₀ := by
    apply lt_of_le_of_ne hr.2
    intro hre
    subst r
    linarith
  rcases hmain r hrpos hrr₀ with
    ⟨s, q, hs0, hsr, hs100, hq, hroot, hdensity, hstrict⟩
  have htwos : 2 * s < r := by linarith
  have hcube : (2 * s) ^ 3 < r ^ 3 :=
    pow_lt_pow_left₀ htwos (by positivity) (by norm_num)
  have hscale : 8 * s ^ 3 < lam - 1 := by
    norm_num [mul_pow] at hcube
    linarith
  have hrlam : 1 + r ^ 3 = lam := by linarith
  rw [hrlam] at hdensity hstrict
  exact ⟨s, q, hs0, hscale, hs100, hq, hroot, hdensity, hstrict⟩

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
