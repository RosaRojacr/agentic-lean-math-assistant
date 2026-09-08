/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureThreeNormalization

/-!
# CMV Figure 3 added-cap containment

The two literal interface segments force the added exterior chord to lie between
the strip-side tangencies.  Vertical normalization transports that same cap,
its chord, radius, and contact angle to the lower-interface coordinates consumed
by the checked type-(iii) non-fit theorem.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

namespace VerticalOrientation

/-- The actual added exterior cap after leaving the upper-primary orientation
fixed or reflecting the lower-primary orientation across the horizontal axis. -/
def normalizeAddedCap (o : VerticalOrientation)
    (c : OneSidedCircularCap) : OneSidedCircularCap where
  chord := c.chord
  theta := c.theta
  midpointX := c.midpointX
  baseY := o.sign * c.baseY
  side := .lower
  chord_pos := c.chord_pos
  theta_pos := c.theta_pos
  theta_lt_pi := c.theta_lt_pi

@[simp] theorem normalizeAddedCap_radius (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).radius = c.radius := rfl

@[simp] theorem normalizeAddedCap_chord (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).chord = c.chord := rfl

@[simp] theorem normalizeAddedCap_theta (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).theta = c.theta := rfl

@[simp] theorem normalizeAddedCap_midpointX (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).midpointX = c.midpointX := rfl

@[simp] theorem normalizeAddedCap_baseY (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).baseY = o.sign * c.baseY := rfl

@[simp] theorem normalizeAddedCap_side (o : VerticalOrientation)
    (c : OneSidedCircularCap) :
    (o.normalizeAddedCap c).side = .lower := rfl

/-- Orientation normalization carries every point of the actual added arc to
the corresponding point of the normalized lower cap. -/
theorem normalizePoint_added_arcPoint
    (o : VerticalOrientation) (c : OneSidedCircularCap)
    (hside : c.side = o.addedCapSide) (t : ℝ) :
    o.normalizePoint (c.arcPoint t) = (o.normalizeAddedCap c).arcPoint t := by
  cases o with
  | upperPrimary =>
      have hc : c.side = .lower := by
        simpa [addedCapSide] using hside
      simp [normalizePoint, normalizeAddedCap, sign,
        OneSidedCircularCap.arcPoint, OneSidedCircularCap.radius, hc]
  | lowerPrimary =>
      have hc : c.side = .upper := by
        simpa [addedCapSide] using hside
      simp [normalizePoint, normalizeAddedCap, sign,
        OneSidedCircularCap.arcPoint, OneSidedCircularCap.radius, hc]
      ring

/-- Orientation normalization transports the complete literal chord of the
same added cap, including both endpoints and every placement. -/
theorem normalizePoint_image_chordCarrier
    (o : VerticalOrientation) (c : OneSidedCircularCap) :
    o.normalizePoint '' c.chordCarrier =
      (o.normalizeAddedCap c).chordCarrier := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.2 = c.baseY ∧
      |q.1 - c.midpointX| ≤ c.chord / 2 at hq
    change o.sign * q.2 = o.sign * c.baseY ∧
      |q.1 - c.midpointX| ≤ c.chord / 2
    exact ⟨congrArg (o.sign * ·) hq.1, hq.2⟩
  · intro hp
    change p.2 = o.sign * c.baseY ∧
      |p.1 - c.midpointX| ≤ c.chord / 2 at hp
    refine ⟨(p.1, o.sign * p.2), ?_, ?_⟩
    · change o.sign * p.2 = c.baseY ∧
        |p.1 - c.midpointX| ≤ c.chord / 2
      constructor
      · cases o <;> simp [sign] at hp ⊢ <;> linarith
      · exact hp.2
    · apply Prod.ext
      · rfl
      · cases o <;> simp [normalizePoint, sign]

end VerticalOrientation

namespace SourceIncidence

variable {lam : ℝ} (s : SourceIncidence lam)

/-- The two possibly degenerate interface segments force every point of the
actual added-cap chord to lie between the two actual strip tangencies. -/
theorem added_chordCarrier_subset_tangentInterval :
    s.addedExterior.chordCarrier ⊆ s.tangentInterval := by
  intro p hp
  change p.2 = s.addedExterior.baseY ∧
    |p.1 - s.addedExterior.midpointX| ≤ s.addedExterior.chord / 2 at hp
  change p.2 = s.orientation.tangentInterfaceY ∧
    s.tangentLeft.1 ≤ p.1 ∧ p.1 ≤ s.tangentRight.1
  have hhalf : 0 ≤ s.addedExterior.chord / 2 :=
    (div_nonneg s.addedExterior.chord_pos.le (by norm_num))
  have hbounds := abs_le.mp hp.2
  have hleftPoint : s.addedExterior.leftEndpoint.1 ≤ p.1 := by
    rw [OneSidedCircularCap.leftEndpoint]
    linarith
  have hrightPoint : p.1 ≤ s.addedExterior.rightEndpoint.1 := by
    rw [OneSidedCircularCap.rightEndpoint]
    linarith
  have hleftSegment := s.leftInterfaceSegment.left_le_right
  have hrightSegment := s.rightInterfaceSegment.left_le_right
  rw [s.left_segment_starts_at_tangency,
    s.left_segment_ends_at_added_cap] at hleftSegment
  rw [s.right_segment_starts_at_added_cap,
    s.right_segment_ends_at_tangency] at hrightSegment
  exact ⟨hp.1.trans s.added_base, hleftSegment.trans hleftPoint,
    hrightPoint.trans hrightSegment⟩

/-- The normalized added cap is literally lower-facing at the normalized lower
interface. -/
theorem normalizedAddedCap_baseY :
    (s.orientation.normalizeAddedCap s.addedExterior).baseY = -1 := by
  rw [VerticalOrientation.normalizeAddedCap_baseY, s.added_base]
  exact s.orientation.normalizePoint_tangentInterfaceY

/-- The actual added cap keeps the source radius after orientation
normalization. -/
theorem normalizedAddedCap_radius (hR : 1 < s.sourceRadius) :
    (s.orientation.normalizeAddedCap s.addedExterior).radius =
      (s.strictAssembly hR).radius := by
  rw [VerticalOrientation.normalizeAddedCap_radius, s.added_radius,
    s.strictAssembly_radius hR]

/-- The source contact law is unchanged by orientation normalization. -/
theorem normalizedAddedCap_contactLaw :
    lam * cos (s.orientation.normalizeAddedCap s.addedExterior).theta = 1 := by
  simpa using s.added_contact_law

/-- The segment-derived containment, actual-cap transport, and source-derived
normalization compose into the literal lower-section containment consumed by
the model-side non-fit theorem. -/
theorem normalized_added_chordCarrier_subset_horizontalSection
    (hR : 1 < s.sourceRadius) :
    (s.orientation.normalizeAddedCap s.addedExterior).chordCarrier ⊆
      horizontalSection
        (horizontalTranslation s.symmetryAxisX ''
          (s.strictAssembly hR).carrier) (-1) := by
  rw [← s.orientation.normalizePoint_image_chordCarrier]
  rw [← s.normalizePoint_image_tangentInterval_eq_horizontalSection hR]
  exact image_mono s.added_chordCarrier_subset_tangentInterval

/-- No strict-radius Figure-3 incidence package exists: its literal added chord
is both forced into and kernel-proved not to fit in the same actual translated
lower section. -/
theorem strictRadius_false (hR : 1 < s.sourceRadius) : False := by
  exact (TypeThreeAssembly.chordCarrier_not_subset_translated_horizontalSection
    (s.strictAssembly hR)
    (s.orientation.normalizeAddedCap s.addedExterior)
    rfl s.normalizedAddedCap_baseY (s.normalizedAddedCap_radius hR)
    s.normalizedAddedCap_contactLaw s.symmetryAxisX)
    (s.normalized_added_chordCarrier_subset_horizontalSection hR)

/-- The independent Figure-3 incidence forces the explicit radius-one residual. -/
theorem sourceRadius_eq_one : s.sourceRadius = 1 := by
  exact le_antisymm (le_of_not_gt fun hR => s.strictRadius_false hR)
    s.radius_ge_one

end SourceIncidence

end CMVFigureThree
