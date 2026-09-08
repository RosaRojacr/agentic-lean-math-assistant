/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import TypeThreeAssembly
import CMVSourceBridge

/-!
# CMV Figure 3 literal chord obstruction

Cañete--Miranda--Vittone, Lemma 3.8 Step 1 (printed page 16, equation
(23)), excludes Figure 3 by observing that the exterior cap chord cannot fit
between the two tangencies of the type-(iii) core.  This file proves that
obstruction for the literal coordinate carriers.  The type-(iii) upper arc is
left branch-complete: major, semicircular, and minor branches are all allowed.

This is only the model-side non-fit gate.  Deriving the type-(iii) core and the
chord containment from independent source boundary incidence remains separate.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

/-- The literal point-valued horizontal section of a planar carrier. -/
def horizontalSection (carrier : Set PlanePoint) (y : ℝ) : Set PlanePoint :=
  carrier ∩ {p | p.2 = y}

namespace TypeThreeAssembly

variable {lam : ℝ} (a : _root_.TypeThreeAssembly lam)

/-- The actual type-(iii) carrier section on the lower strip interface is
exactly its possibly degenerate bottom segment. -/
theorem horizontalSection_neg_one :
    horizontalSection a.carrier (-1) = a.bottomSegmentCarrier := by
  ext p
  change (p ∈ a.carrier ∧ p.2 = (-1 : ℝ)) ↔
    (p.2 = (-1 : ℝ) ∧ |p.1| ≤ a.sideHalfWidth)
  constructor
  · rintro ⟨hp, hy⟩
    rcases hp with hcore | hcap
    · rcases hcore with (hrect | hleft) | hright
      · change
          ((-a.sideHalfWidth ≤ p.1 ∧ p.1 ≤ a.sideHalfWidth) ∧
            (-1 ≤ p.2 ∧ p.2 ≤ 1)) at hrect
        exact ⟨hy, abs_le.mpr hrect.1⟩
      · change
          ((p.1 - a.leftCenter.1) ^ 2 +
              (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
            p.1 ≤ a.leftCenter.1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 at hleft
        have hx : p.1 = -a.sideHalfWidth := by
          have hdisk := hleft.1
          simp only [_root_.TypeThreeAssembly.leftCenter,
            sub_neg_eq_add] at hdisk
          rw [hy] at hdisk
          ring_nf at hdisk
          nlinarith [sq_nonneg (p.1 + a.sideHalfWidth)]
        refine ⟨hy, ?_⟩
        rw [hx, abs_neg, abs_of_nonneg a.sideHalfWidth_nonneg]
      · change
          ((p.1 - a.rightCenter.1) ^ 2 +
              (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
            a.rightCenter.1 ≤ p.1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 at hright
        have hx : p.1 = a.sideHalfWidth := by
          have hdisk := hright.1
          simp only [_root_.TypeThreeAssembly.rightCenter] at hdisk
          rw [hy] at hdisk
          ring_nf at hdisk
          nlinarith [sq_nonneg (p.1 - a.sideHalfWidth)]
        refine ⟨hy, ?_⟩
        rw [hx, abs_of_nonneg a.sideHalfWidth_nonneg]
    · have hyCap : (1 : ℝ) ≤ p.2 := by
        simpa [_root_.TypeThreeAssembly.outerCap,
          OneSidedCircularCap.carrier] using hcap.2
      exfalso
      linarith
  · rintro ⟨hy, habs⟩
    have hx : -a.sideHalfWidth ≤ p.1 ∧ p.1 ≤ a.sideHalfWidth :=
      abs_le.mp habs
    have hyBounds : (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 := by
      constructor <;> linarith
    refine ⟨?_, hy⟩
    exact Or.inl (Or.inl (Or.inl ⟨hx, hyBounds⟩))

/-- Horizontal placement commutes with taking the actual lower-interface
section. -/
theorem horizontalSection_horizontalTranslation (t : ℝ) :
    horizontalSection (horizontalTranslation t '' a.carrier) (-1) =
      horizontalTranslation t '' a.bottomSegmentCarrier := by
  ext p
  change
    (p ∈ horizontalTranslation t '' a.carrier ∧ p.2 = (-1 : ℝ)) ↔
      p ∈ horizontalTranslation t '' a.bottomSegmentCarrier
  constructor
  · rintro ⟨⟨q, hq, hqp⟩, hpY⟩
    have hqY : q.2 = (-1 : ℝ) := by
      have hsecond := congrArg Prod.snd hqp
      simpa only [horizontalTranslation_apply] using hsecond.trans hpY
    refine ⟨q, ?_, hqp⟩
    rw [← horizontalSection_neg_one a]
    exact ⟨hq, hqY⟩
  · rintro ⟨q, hq, hqp⟩
    refine ⟨⟨q, ?_, hqp⟩, ?_⟩
    · have hsection : q ∈ horizontalSection a.carrier (-1) := by
        rw [horizontalSection_neg_one a]
        exact hq
      exact hsection.1
    · have hsecond := congrArg Prod.snd hqp
      simp only [horizontalTranslation_apply] at hsecond
      rw [← hsecond]
      exact hq.1

/-- At the branch transition `R = 2`, the translated actual lower-interface
section is a singleton. -/
theorem horizontalSection_horizontalTranslation_semicircular
    (hh : a.h = 1 / 2) (t : ℝ) :
    horizontalSection (horizontalTranslation t '' a.carrier) (-1) =
      {(t, -1)} := by
  have hw : a.sideHalfWidth = 0 :=
    a.sideHalfWidth_eq_zero_iff.mpr hh
  have hbottom : a.bottomSegmentCarrier = {(0, -1)} := by
    ext p
    simp only [_root_.TypeThreeAssembly.bottomSegmentCarrier, mem_inter_iff,
      mem_ofPred_eq, hw, abs_nonpos_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hy, hx⟩
      exact Prod.ext hx hy
    · intro hp
      rw [hp]
      exact ⟨rfl, rfl⟩
  rw [horizontalSection_horizontalTranslation a t, hbottom, image_singleton]
  simp

/-- Equation (23)'s strict scalar content, derived from the actual principal
angles and from the cap's own radius and contact law. -/
theorem bottomChord_lt_contactChord
    (c : OneSidedCircularCap)
    (hradius : c.radius = a.radius)
    (hcontact : lam * cos c.theta = 1) :
    a.bottomChord < c.chord := by
  have hlamPos : 0 < lam := lt_trans (by norm_num) a.density_jump
  have hlamSq : 1 < lam ^ 2 := by nlinarith [a.density_jump]
  have hcosOuter : lam * cos a.outerAngle = cos a.innerAngle :=
    a.snell_incidence
  have htrigOuter := Real.sin_sq_add_cos_sq a.outerAngle
  have htrigInner := Real.sin_sq_add_cos_sq a.innerAngle
  have htrigCap := Real.sin_sq_add_cos_sq c.theta
  have hcosOuterSq := congrArg (fun z : ℝ => z ^ 2) hcosOuter
  have hcontactSq := congrArg (fun z : ℝ => z ^ 2) hcontact
  have hscaledOuter :
      lam ^ 2 * sin a.outerAngle ^ 2 =
        lam ^ 2 - cos a.innerAngle ^ 2 := by
    nlinarith
  have hscaledCap :
      lam ^ 2 * sin c.theta ^ 2 = lam ^ 2 - 1 := by
    nlinarith
  have hgain :
      0 < (lam ^ 2 - 1) * sin a.innerAngle ^ 2 +
        2 * lam ^ 2 * sin a.innerAngle * sin c.theta := by
    have hfirst : 0 < (lam ^ 2 - 1) * sin a.innerAngle ^ 2 :=
      mul_pos (sub_pos.mpr hlamSq) (sq_pos_of_pos a.innerSin_pos)
    have hsecond :
        0 < 2 * lam ^ 2 * sin a.innerAngle * sin c.theta :=
      mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hlamPos))
          a.innerSin_pos)
        c.sin_theta_pos
    linarith
  have hscaledSq :
      lam ^ 2 * sin a.outerAngle ^ 2 <
        lam ^ 2 * (sin a.innerAngle + sin c.theta) ^ 2 := by
    nlinarith
  have hsq :
      sin a.outerAngle ^ 2 <
        (sin a.innerAngle + sin c.theta) ^ 2 := by
    by_contra hnot
    have hle :
        (sin a.innerAngle + sin c.theta) ^ 2 ≤
          sin a.outerAngle ^ 2 := le_of_not_gt hnot
    have hscaledLe := mul_le_mul_of_nonneg_left hle (sq_nonneg lam)
    exact (not_lt_of_ge hscaledLe) hscaledSq
  have hsine :
      sin a.outerAngle < sin a.innerAngle + sin c.theta :=
    (sq_lt_sq₀ a.outerSin_pos.le
      (add_nonneg a.innerSin_pos.le c.sin_theta_pos.le)).mp hsq
  have hhalf : a.sideHalfWidth < c.chord / 2 := by
    rw [_root_.TypeThreeAssembly.sideHalfWidth, ← c.radius_mul_sin,
      hradius]
    exact mul_lt_mul_of_pos_left (by linarith) a.radius_pos
  rw [_root_.TypeThreeAssembly.bottomChord]
  linarith

/-- A contact-law exterior chord cannot be contained in any horizontal
translate of the actual lower-interface section of a type-(iii) carrier.
Arbitrary placement of both carriers is retained through `midpointX` and `t`.
-/
theorem chordCarrier_not_subset_translated_horizontalSection
    (c : OneSidedCircularCap)
    (_hside : c.side = .lower)
    (_hbase : c.baseY = -1)
    (hradius : c.radius = a.radius)
    (hcontact : lam * cos c.theta = 1)
    (t : ℝ) :
    ¬ c.chordCarrier ⊆
      horizontalSection (horizontalTranslation t '' a.carrier) (-1) := by
  intro hfit
  have hleft : c.leftEndpoint ∈ c.chordCarrier := by
    constructor
    · rfl
    · rw [OneSidedCircularCap.leftEndpoint]
      have hcHalf : 0 ≤ c.chord / 2 :=
        div_nonneg c.chord_pos.le (by norm_num)
      rw [show c.midpointX - c.chord / 2 - c.midpointX =
          -(c.chord / 2) by ring,
        abs_neg, abs_of_nonneg hcHalf]
  have hright : c.rightEndpoint ∈ c.chordCarrier := by
    constructor
    · rfl
    · rw [OneSidedCircularCap.rightEndpoint]
      have hcHalf : 0 ≤ c.chord / 2 :=
        div_nonneg c.chord_pos.le (by norm_num)
      rw [show c.midpointX + c.chord / 2 - c.midpointX =
          c.chord / 2 by ring,
        abs_of_nonneg hcHalf]
  have hsection := horizontalSection_horizontalTranslation a t
  have hleftImage :
      c.leftEndpoint ∈ horizontalTranslation t '' a.bottomSegmentCarrier := by
    rw [← hsection]
    exact hfit hleft
  have hrightImage :
      c.rightEndpoint ∈ horizontalTranslation t '' a.bottomSegmentCarrier := by
    rw [← hsection]
    exact hfit hright
  rcases hleftImage with ⟨qLeft, hqLeft, hqLeftEq⟩
  rcases hrightImage with ⟨qRight, hqRight, hqRightEq⟩
  change qLeft.2 = (-1 : ℝ) ∧ |qLeft.1| ≤ a.sideHalfWidth at hqLeft
  change qRight.2 = (-1 : ℝ) ∧ |qRight.1| ≤ a.sideHalfWidth at hqRight
  have hxLeft := congrArg Prod.fst hqLeftEq
  have hxRight := congrArg Prod.fst hqRightEq
  simp only [horizontalTranslation_apply, OneSidedCircularCap.leftEndpoint,
    OneSidedCircularCap.rightEndpoint] at hxLeft hxRight
  have hleftBound := (abs_le.mp hqLeft.2).1
  have hrightBound := (abs_le.mp hqRight.2).2
  have hchordLe : c.chord ≤ a.bottomChord := by
    rw [_root_.TypeThreeAssembly.bottomChord]
    nlinarith
  exact (not_lt_of_ge hchordLe)
    (bottomChord_lt_contactChord a c hradius hcontact)

/-- The literal non-fit theorem explicitly specialized to the degenerate
`h = 1/2`, `R = 2` bottom interval, with arbitrary horizontal placement. -/
theorem semicircular_chordCarrier_not_subset_translated_horizontalSection
    (hh : a.h = 1 / 2)
    (c : OneSidedCircularCap)
    (hside : c.side = .lower)
    (hbase : c.baseY = -1)
    (hradius : c.radius = a.radius)
    (hcontact : lam * cos c.theta = 1)
    (t : ℝ) :
    ¬ c.chordCarrier ⊆
      horizontalSection (horizontalTranslation t '' a.carrier) (-1) := by
  rw [horizontalSection_horizontalTranslation_semicircular a hh t]
  intro hfit
  apply chordCarrier_not_subset_translated_horizontalSection
    a c hside hbase hradius hcontact t
  rw [horizontalSection_horizontalTranslation_semicircular a hh t]
  exact hfit

end TypeThreeAssembly

end CMVFigureThree
