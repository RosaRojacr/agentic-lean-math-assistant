/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourTargetGeometry
import Mathlib.Analysis.Convex.PathConnected

/-!
# Complement topology of the literal CMV Figure-4 carrier

The proofs use the literal closed carrier.  Horizontal paths are justified by
its complete centered-section geometry, not by source sections or an assumed
orientation.  Exterior paths first escape along a horizontal ray and then join
above a bounded box.
-/

open Set Real

noncomputable section

namespace CMVFigureFourComplementTopology

open CMVSourceClassification
open CMVSourceClassification.RawFourArcCoordinates

/-- Every horizontal section is empty or a closed interval about one fixed
vertical axis. -/
def HasCenteredClosedSections (K : Set PlanePoint) (center : ℝ) : Prop :=
  ∀ y, IsEmptyOrCenteredClosedInterval center (horizontalSection K y)

/-- Moving horizontally toward the section center preserves membership. -/
theorem mem_of_mem_same_height_of_abs_sub_le
    {K : Set PlanePoint} {center : ℝ}
    (hsections : HasCenteredClosedSections K center)
    {p q : PlanePoint} (hp : p ∈ K) (hy : q.2 = p.2)
    (habs : |q.1 - center| ≤ |p.1 - center|) : q ∈ K := by
  change p.1 ∈ horizontalSection K p.2 at hp
  change q.1 ∈ horizontalSection K q.2
  rcases hsections p.2 with hempty | ⟨radius, hradius, hsection⟩
  · rw [hempty] at hp
    exact hp.elim
  · rw [hy, hsection]
    rw [hsection] at hp
    have hpabs : |p.1 - center| ≤ radius := by
      rw [abs_le]
      constructor <;> linarith [hp.1, hp.2]
    have hqabs : |q.1 - center| ≤ radius := habs.trans hpabs
    rw [abs_le] at hqabs
    constructor <;> linarith [hqabs.1, hqabs.2]

/-- The horizontal projection of an interior point to the section axis is
again interior.  The proof constructs a genuine open box around the projected
point from an open ball around the original point. -/
theorem verticalSpine_mem_interior
    {K : Set PlanePoint} {center : ℝ}
    (hsections : HasCenteredClosedSections K center)
    {p : PlanePoint} (hp : p ∈ interior K) :
    (center, p.2) ∈ interior K := by
  by_cases haxis : p.1 = center
  · rw [show (center, p.2) = p from Prod.ext haxis.symm rfl]
    exact hp
  have hd : 0 < |p.1 - center| := abs_pos.mpr (sub_ne_zero.mpr haxis)
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  let delta := min epsilon |p.1 - center| / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaEpsilon : delta < epsilon := by
    dsimp [delta]
    have := min_le_left epsilon |p.1 - center|
    linarith
  have hdeltaD : delta < |p.1 - center| := by
    dsimp [delta]
    have := min_le_right epsilon |p.1 - center|
    linarith
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ hdelta) ?_
  intro q hq
  have hqdist :
      max |q.1 - center| |q.2 - p.2| < delta := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_comm,
      abs_sub_comm] using hq
  let z : PlanePoint := (p.1, q.2)
  have hzball : z ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, Prod.dist_eq]
    dsimp [z]
    rw [dist_self, max_eq_right (dist_nonneg : 0 ≤ dist q.2 p.2),
      Real.dist_eq]
    exact ((le_max_right _ _).trans_lt hqdist).trans hdeltaEpsilon
  have hzK : z ∈ K := interior_subset (hball hzball)
  apply mem_of_mem_same_height_of_abs_sub_le hsections
    (p := z) (q := q) hzK rfl
  dsimp [z]
  exact (le_max_left _ _).trans
    (le_of_lt (hqdist.trans hdeltaD))

/-- Horizontal contraction about the section center preserves interior points. -/
theorem horizontal_contraction_mem_interior
    {K : Set PlanePoint} {center t : ℝ}
    (hsections : HasCenteredClosedSections K center)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {p : PlanePoint} (hp : p ∈ interior K) :
    (center + t * (p.1 - center), p.2) ∈ interior K := by
  rcases ht0.eq_or_lt with rfl | ht
  · simpa using verticalSpine_mem_interior hsections hp
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  let q : PlanePoint := (center + t * (p.1 - center), p.2)
  have htepsilon : 0 < t * epsilon := mul_pos ht hepsilon
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds q htepsilon) ?_
  intro z hz
  have hzdist :
      max |z.1 - q.1| |z.2 - q.2| < t * epsilon := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_comm,
      abs_sub_comm] using hz
  let w : PlanePoint :=
    (center + (z.1 - center) / t, z.2)
  have hwx : |w.1 - p.1| < epsilon := by
    have hx : |z.1 - q.1| < t * epsilon :=
      (le_max_left _ _).trans_lt hzdist
    have heq : w.1 - p.1 = (z.1 - q.1) / t := by
      dsimp [w, q]
      field_simp [ne_of_gt ht]
      ring
    rw [heq, abs_div, abs_of_pos ht]
    exact (div_lt_iff₀ ht).2 (by simpa [mul_comm] using hx)
  have hwy : |w.2 - p.2| < epsilon := by
    have hy : |z.2 - q.2| < t * epsilon :=
      (le_max_right _ _).trans_lt hzdist
    have hmul : t * epsilon ≤ epsilon := by
      calc
        t * epsilon ≤ 1 * epsilon :=
          mul_le_mul_of_nonneg_right ht1 hepsilon.le
        _ = epsilon := one_mul epsilon
    dsimp [w, q]
    exact hy.trans_le hmul
  have hwball : w ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq]
    exact max_lt hwx hwy
  have hwK : w ∈ K := interior_subset (hball hwball)
  apply mem_of_mem_same_height_of_abs_sub_le hsections
    (p := w) (q := z) hwK rfl
  have hxscale : z.1 - center = t * (w.1 - center) := by
    dsimp [w]
    field_simp [ne_of_gt ht]
    ring
  rw [hxscale, abs_mul, abs_of_pos ht]
  exact mul_le_of_le_one_left (abs_nonneg _) ht1

/-- The literal straight path from an interior point to its vertical spine
stays in the interior. -/
theorem interior_horizontal_spine_joinedIn
    {K : Set PlanePoint} {center : ℝ}
    (hsections : HasCenteredClosedSections K center)
    {p : PlanePoint} (hp : p ∈ interior K) :
    JoinedIn (interior K) p (center, p.2) := by
  apply JoinedIn.of_segment_subset
  rw [segment_subset_iff]
  intro a b ha hb hab
  have ha1 : a ≤ 1 := by linarith
  convert horizontal_contraction_mem_interior hsections ha ha1 hp using 1
  apply Prod.ext
  · dsimp
    rw [show b = 1 - a by linarith]
    ring
  · dsimp
    rw [show b = 1 - a by linarith]
    ring

/-- A bounded centered-section set has a path-connected exterior.  Every point
first follows a horizontal escape segment, then a vertical segment outside a
norm bound, and finally the common segment above that bound. -/
theorem isPathConnected_compl_of_bounded_centeredSections
    {K : Set PlanePoint} {center : ℝ}
    (hbounded : Bornology.IsBounded K)
    (hsections : HasCenteredClosedSections K center) :
    IsPathConnected Kᶜ := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbounded
  let rightX := max center M + 1
  let leftX := min center (-M) - 1
  let topY := M + 1
  have hrightCenter : center < rightX := by
    dsimp [rightX]
    linarith [le_max_left center M]
  have hrightM : M < rightX := by
    dsimp [rightX]
    linarith [le_max_right center M]
  have hleftCenter : leftX < center := by
    dsimp [leftX]
    linarith [min_le_left center (-M)]
  have hleftM : leftX < -M := by
    dsimp [leftX]
    linarith [min_le_right center (-M)]
  have htopM : M < topY := by dsimp [topY]; linarith
  have hcoord {z : PlanePoint} (hz : z ∈ K) :
      |z.1| ≤ M ∧ |z.2| ≤ M := by
    have hzNorm := hM z hz
    exact ⟨(norm_fst_le z).trans hzNorm,
      (norm_snd_le z).trans hzNorm⟩
  have hrightOutside (y : ℝ) : (rightX, y) ∈ Kᶜ := by
    intro hmem
    have hx := (hcoord hmem).1
    dsimp only at hx
    have : rightX ≤ |rightX| := le_abs_self rightX
    linarith
  have hleftOutside (y : ℝ) : (leftX, y) ∈ Kᶜ := by
    intro hmem
    have hx := (hcoord hmem).1
    dsimp only at hx
    have : -leftX ≤ |leftX| := neg_le_abs leftX
    linarith
  have htopOutside (x : ℝ) : (x, topY) ∈ Kᶜ := by
    intro hmem
    have hy := (hcoord hmem).2
    dsimp only at hy
    have : topY ≤ |topY| := le_abs_self topY
    linarith
  have rightEscape {p : PlanePoint} (hp : p ∈ Kᶜ)
      (hpc : center ≤ p.1) :
      JoinedIn Kᶜ p (rightX, p.2) := by
    apply JoinedIn.of_segment_subset
    rw [segment_subset_iff]
    intro a b ha hb hab hmem
    let q : PlanePoint := a • p + b • (rightX, p.2)
    have hqy : q.2 = p.2 := by
      dsimp [q]
      rw [show b = 1 - a by linarith]
      ring
    have hqSection : q.1 ∈ horizontalSection K p.2 := by
      change (q.1, p.2) ∈ K
      rw [← hqy]
      simpa only [Prod.eta] using hmem
    rcases hsections p.2 with hempty | ⟨radius, hradius, hsection⟩
    · rw [hempty] at hqSection
      exact hqSection.elim
    · have hpNot : p.1 ∉ Icc (center - radius) (center + radius) := by
        intro hpIcc
        apply hp
        change p.1 ∈ horizontalSection K p.2
        rwa [hsection]
      have hpRight : center + radius < p.1 := by
        rw [Set.mem_Icc, not_and_or] at hpNot
        rcases hpNot with hpNot | hpNot
        · exfalso
          exact hpNot (by linarith)
        · exact lt_of_not_ge hpNot
      have hendpoint : (center + radius, p.2) ∈ K := by
        change center + radius ∈ horizontalSection K p.2
        rw [hsection]
        exact ⟨by linarith, le_rfl⟩
      have hendBound := (hcoord hendpoint).1
      have hrightEndpoint : center + radius < rightX := by
        have : center + radius ≤ |center + radius| := le_abs_self _
        linarith
      have haTerm : 0 ≤ a * (p.1 - (center + radius)) :=
        mul_nonneg ha (sub_nonneg.mpr hpRight.le)
      have hbTerm : 0 ≤ b * (rightX - (center + radius)) :=
        mul_nonneg hb (sub_nonneg.mpr hrightEndpoint.le)
      have hsumTerm :
          0 < a * (p.1 - (center + radius)) +
            b * (rightX - (center + radius)) := by
        rcases ha.eq_or_lt with rfl | haPos
        · have hbOne : b = 1 := by linarith
          simpa [hbOne] using sub_pos.mpr hrightEndpoint
        · exact add_pos_of_pos_of_nonneg
            (mul_pos haPos (sub_pos.mpr hpRight)) hbTerm
      have hqRight : center + radius < q.1 := by
        dsimp [q]
        nlinarith
      rw [hsection] at hqSection
      linarith [hqSection.2]
  have leftEscape {p : PlanePoint} (hp : p ∈ Kᶜ)
      (hpc : p.1 < center) :
      JoinedIn Kᶜ p (leftX, p.2) := by
    apply JoinedIn.of_segment_subset
    rw [segment_subset_iff]
    intro a b ha hb hab hmem
    let q : PlanePoint := a • p + b • (leftX, p.2)
    have hqy : q.2 = p.2 := by
      dsimp [q]
      rw [show b = 1 - a by linarith]
      ring
    have hqSection : q.1 ∈ horizontalSection K p.2 := by
      change (q.1, p.2) ∈ K
      rw [← hqy]
      simpa only [Prod.eta] using hmem
    rcases hsections p.2 with hempty | ⟨radius, hradius, hsection⟩
    · rw [hempty] at hqSection
      exact hqSection.elim
    · have hpNot : p.1 ∉ Icc (center - radius) (center + radius) := by
        intro hpIcc
        apply hp
        change p.1 ∈ horizontalSection K p.2
        rwa [hsection]
      have hpLeft : p.1 < center - radius := by
        rw [Set.mem_Icc, not_and_or] at hpNot
        rcases hpNot with hpNot | hpNot
        · exact lt_of_not_ge hpNot
        · exfalso
          exact hpNot (by linarith)
      have hendpoint : (center - radius, p.2) ∈ K := by
        change center - radius ∈ horizontalSection K p.2
        rw [hsection]
        exact ⟨le_rfl, by linarith⟩
      have hendBound := (hcoord hendpoint).1
      have hleftEndpoint : leftX < center - radius := by
        have : -(center - radius) ≤ |center - radius| := neg_le_abs _
        linarith
      have haTerm : 0 ≤ a * ((center - radius) - p.1) :=
        mul_nonneg ha (sub_nonneg.mpr hpLeft.le)
      have hbTerm : 0 ≤ b * ((center - radius) - leftX) :=
        mul_nonneg hb (sub_nonneg.mpr hleftEndpoint.le)
      have hsumTerm :
          0 < a * ((center - radius) - p.1) +
            b * ((center - radius) - leftX) := by
        rcases ha.eq_or_lt with rfl | haPos
        · have hbOne : b = 1 := by linarith
          simpa [hbOne] using sub_pos.mpr hleftEndpoint
        · exact add_pos_of_pos_of_nonneg
            (mul_pos haPos (sub_pos.mpr hpLeft)) hbTerm
      have hqLeft : q.1 < center - radius := by
        dsimp [q]
        nlinarith
      rw [hsection] at hqSection
      linarith [hqSection.1]
  have rightVertical (y : ℝ) :
      JoinedIn Kᶜ (rightX, y) (rightX, topY) := by
    apply JoinedIn.of_segment_subset
    rw [segment_subset_iff]
    intro a b ha hb hab
    convert hrightOutside (a * y + b * topY) using 1
    apply Prod.ext <;> dsimp
    · rw [show b = 1 - a by linarith]
      ring
  have leftVertical (y : ℝ) :
      JoinedIn Kᶜ (leftX, y) (leftX, topY) := by
    apply JoinedIn.of_segment_subset
    rw [segment_subset_iff]
    intro a b ha hb hab
    convert hleftOutside (a * y + b * topY) using 1
    apply Prod.ext <;> dsimp
    · rw [show b = 1 - a by linarith]
      ring
  have topHorizontal :
      JoinedIn Kᶜ (leftX, topY) (rightX, topY) := by
    apply JoinedIn.of_segment_subset
    rw [segment_subset_iff]
    intro a b ha hb hab
    convert htopOutside (a * leftX + b * rightX) using 1
    apply Prod.ext <;> dsimp
    rw [show b = 1 - a by linarith]
    ring
  refine ⟨(rightX, topY), hrightOutside topY, ?_⟩
  intro p hp
  by_cases hpc : center ≤ p.1
  · exact (rightVertical p.2).symm.trans (rightEscape hp hpc).symm
  · exact topHorizontal.symm.trans
      ((leftVertical p.2).symm.trans (leftEscape hp (lt_of_not_ge hpc)).symm)

end CMVFigureFourComplementTopology
