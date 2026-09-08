import CMVProjectionDefect

/-!
# Common phase outside square-frontier projections

Inside a closed coordinate box, remove the product of the two coordinate
projections of the localized topological frontier.  If each coordinate interval
contains a point outside its projection, the remaining points all have one
common phase: they are all in the set or all in its complement.
-/

open Set
open scoped Topology

noncomputable section

namespace CMVRelaxation

/-- Vertical coordinates whose complete horizontal box segment meets the
frontier of `U`.  This is an unweighted Euclidean coordinate projection. -/
def horizontalCrossingFibers (U : Set PlanePoint) (a b y₀ rho : ℝ) : Set ℝ :=
  Prod.snd '' (frontier U ∩ projectionBox a b y₀ rho)

lemma isCompact_horizontalCrossingFibers
    (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    IsCompact (horizontalCrossingFibers U a b y₀ rho) := by
  exact ((isCompact_projectionBox a b y₀ rho).inter_left
    isClosed_frontier).image continuous_snd

lemma measurableSet_horizontalCrossingFibers
    (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    MeasurableSet (horizontalCrossingFibers U a b y₀ rho) :=
  (isCompact_horizontalCrossingFibers U a b y₀ rho).measurableSet

/-- If one horizontal box fiber misses the frontier, its complete segment is
wholly inside or wholly outside the set.  No openness hypothesis is needed. -/
lemma horizontalSegment_subset_or_subset_compl
    {U : Set PlanePoint} {a b y₀ rho y : ℝ}
    (hy : y ∈ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) \
      horizontalCrossingFibers U a b y₀ rho) :
    (fun x : ℝ => (x, y)) '' Icc a b ⊆ U ∨
      (fun x : ℝ => (x, y)) '' Icc a b ⊆ Uᶜ := by
  let f : ℝ → PlanePoint := fun x => (x, y)
  have hfrontier : Icc a b ⊆ f ⁻¹' (frontier U)ᶜ := by
    intro x hx
    change (x, y) ∉ frontier U
    intro hboundary
    exact hy.2 ⟨(x, y), ⟨hboundary, ⟨hx, hy.1⟩⟩, rfl⟩
  have hcover : Icc a b ⊆
      f ⁻¹' interior U ∪ f ⁻¹' interior Uᶜ := by
    simpa only [preimage_union, compl_frontier_eq_union_interior] using hfrontier
  have hopenU : IsOpen (f ⁻¹' interior U) :=
    isOpen_interior.preimage (continuous_id.prodMk continuous_const)
  have hopenC : IsOpen (f ⁻¹' interior Uᶜ) :=
    isOpen_interior.preimage (continuous_id.prodMk continuous_const)
  have hdisjoint : Disjoint (f ⁻¹' interior U) (f ⁻¹' interior Uᶜ) := by
    apply Set.disjoint_left.2
    intro x hxU hxC
    exact (show f x ∉ U from interior_subset hxC) (interior_subset hxU)
  rcases isPreconnected_Icc.subset_or_subset hopenU hopenC hdisjoint
      hcover with hin | hout
  · left
    rintro p ⟨x, hx, rfl⟩
    exact interior_subset (hin hx)
  · right
    rintro p ⟨x, hx, rfl⟩
    exact interior_subset (hout hx)

/-- Product of the two localized coordinate projections of the frontier. -/
def crossingProjectionProduct (U : Set PlanePoint) (a b y₀ rho : ℝ) :
    Set PlanePoint :=
  crossingFibers U a b y₀ rho ×ˢ
    horizontalCrossingFibers U a b y₀ rho

/-- The vertical and horizontal reference fibers force one common phase on the
box outside the product of the two frontier projections.  The reference points
are derived from the two strict non-cover hypotheses. -/
theorem projectionBox_diff_crossingProjectionProduct_commonPhase
    {U : Set PlanePoint} {a b y₀ rho : ℝ}
    (hxGood : ¬ Icc a b ⊆ crossingFibers U a b y₀ rho)
    (hyGood : ¬ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆
      horizontalCrossingFibers U a b y₀ rho) :
    projectionBox a b y₀ rho \
        crossingProjectionProduct U a b y₀ rho ⊆ U ∨
      projectionBox a b y₀ rho \
        crossingProjectionProduct U a b y₀ rho ⊆ Uᶜ := by
  obtain ⟨xRef, hxRef, hxRefGood⟩ := Set.not_subset.mp hxGood
  obtain ⟨yRef, hyRef, hyRefGood⟩ := Set.not_subset.mp hyGood
  have hvRef := verticalSegment_subset_or_subset_compl
    (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (x := xRef)
    ⟨hxRef, hxRefGood⟩
  have hhRef := horizontalSegment_subset_or_subset_compl
    (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (y := yRef)
    ⟨hyRef, hyRefGood⟩
  have href :
      (((fun y : ℝ => (xRef, y)) ''
            Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ U) ∧
        ((fun x : ℝ => (x, yRef)) '' Icc a b ⊆ U)) ∨
      (((fun y : ℝ => (xRef, y)) ''
            Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆ Uᶜ) ∧
        ((fun x : ℝ => (x, yRef)) '' Icc a b ⊆ Uᶜ)) := by
    rcases hvRef with hvIn | hvOut
    · rcases hhRef with hhIn | hhOut
      · exact Or.inl ⟨hvIn, hhIn⟩
      · exact False.elim
          ((hhOut ⟨xRef, hxRef, rfl⟩) (hvIn ⟨yRef, hyRef, rfl⟩))
    · rcases hhRef with hhIn | hhOut
      · exact False.elim
          ((hvOut ⟨yRef, hyRef, rfl⟩) (hhIn ⟨xRef, hxRef, rfl⟩))
      · exact Or.inr ⟨hvOut, hhOut⟩
  rcases href with ⟨hvRefIn, hhRefIn⟩ | ⟨hvRefOut, hhRefOut⟩
  · left
    rintro ⟨x, y⟩ hp
    have hbox : x ∈ Icc a b ∧
        y ∈ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) := hp.1
    have hprojection :
        x ∉ crossingFibers U a b y₀ rho ∨
          y ∉ horizontalCrossingFibers U a b y₀ rho := by
      simpa only [crossingProjectionProduct, Set.mem_prod, not_and_or] using hp.2
    rcases hprojection with hx | hy
    · rcases verticalSegment_subset_or_subset_compl
          (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (x := x)
          ⟨hbox.1, hx⟩ with hvIn | hvOut
      · exact hvIn ⟨y, hbox.2, rfl⟩
      · exact False.elim
          ((hvOut ⟨yRef, hyRef, rfl⟩) (hhRefIn ⟨x, hbox.1, rfl⟩))
    · rcases horizontalSegment_subset_or_subset_compl
          (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (y := y)
          ⟨hbox.2, hy⟩ with hhIn | hhOut
      · exact hhIn ⟨x, hbox.1, rfl⟩
      · exact False.elim
          ((hhOut ⟨xRef, hxRef, rfl⟩) (hvRefIn ⟨y, hbox.2, rfl⟩))
  · right
    rintro ⟨x, y⟩ hp
    have hbox : x ∈ Icc a b ∧
        y ∈ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) := hp.1
    have hprojection :
        x ∉ crossingFibers U a b y₀ rho ∨
          y ∉ horizontalCrossingFibers U a b y₀ rho := by
      simpa only [crossingProjectionProduct, Set.mem_prod, not_and_or] using hp.2
    rcases hprojection with hx | hy
    · rcases verticalSegment_subset_or_subset_compl
          (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (x := x)
          ⟨hbox.1, hx⟩ with hvIn | hvOut
      · exact False.elim
          ((hhRefOut ⟨x, hbox.1, rfl⟩) (hvIn ⟨yRef, hyRef, rfl⟩))
      · exact hvOut ⟨y, hbox.2, rfl⟩
    · rcases horizontalSegment_subset_or_subset_compl
          (U := U) (a := a) (b := b) (y₀ := y₀) (rho := rho) (y := y)
          ⟨hbox.2, hy⟩ with hhIn | hhOut
      · exact False.elim
          ((hvRefOut ⟨y, hbox.2, rfl⟩) (hhIn ⟨xRef, hxRef, rfl⟩))
      · exact hhOut ⟨x, hbox.1, rfl⟩

/-- Equivalent minority-phase form: one phase inside the box is confined to the
product of the two localized frontier projections. -/
theorem projectionBox_phase_subset_crossingProjectionProduct
    {U : Set PlanePoint} {a b y₀ rho : ℝ}
    (hxGood : ¬ Icc a b ⊆ crossingFibers U a b y₀ rho)
    (hyGood : ¬ Icc (y₀ - 2 * rho) (y₀ + 2 * rho) ⊆
      horizontalCrossingFibers U a b y₀ rho) :
    U ∩ projectionBox a b y₀ rho ⊆
        crossingProjectionProduct U a b y₀ rho ∨
      Uᶜ ∩ projectionBox a b y₀ rho ⊆
        crossingProjectionProduct U a b y₀ rho := by
  rcases projectionBox_diff_crossingProjectionProduct_commonPhase
      hxGood hyGood with hin | hout
  · right
    intro p hp
    by_contra hpProjection
    exact hp.1 (hin ⟨hp.2, hpProjection⟩)
  · left
    intro p hp
    by_contra hpProjection
    exact (hout ⟨hp.2, hpProjection⟩) hp.1

end CMVRelaxation
