/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryOrderTopology
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Topology.UnitInterval

/-!
# Closed-interval parameterizations of completed boundary chains

A nontrivial separable complete dense linear order is reconstructed from a
countable dense suborder.  Cantor's theorem identifies that suborder with the
rational open unit interval, and the Dedekind factor embeddings identify both
completions.  The resulting order isomorphisms are then transported through the
proved equality between each chain's order topology and planar subspace
topology.
-/

open Set Function Filter TopologicalSpace
open scoped Topology

noncomputable section

namespace SeparableLinearContinuum

universe u v

/-- A Dedekind factor embedding onto a complete dense order is surjective when
its original range is dense.  This is the completion-uniqueness step used
below; it does not assume an ambient real coordinate. -/
theorem dedekindFactorEmbedding_surjective_of_denseRange
    {α : Type u} {β : Type v} [CompleteLinearOrder α] [LinearOrder β]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    (f : β ↪o α) (hf : DenseRange f) :
    Surjective (DedekindCut.factorEmbedding f) := by
  intro x
  let A : DedekindCut β :=
    { extent := f ⁻¹' Iic x
      intent := f ⁻¹' Ici x
      upperPolar_extent := by
        ext b
        change (∀ ⦃a : β⦄, f a ≤ x → a ≤ b) ↔ x ≤ f b
        constructor
        · intro h
          by_contra hxb
          have hlt : f b < x := lt_of_not_ge hxb
          obtain ⟨z, hzRange, hz⟩ := hf.exists_between hlt
          rcases hzRange with ⟨a, rfl⟩
          exact (not_lt_of_ge (f.monotone (h hz.2.le))) hz.1
        · intro h a ha
          exact f.le_iff_le.mp (ha.trans h)
      lowerPolar_intent := by
        ext a
        change (∀ ⦃b : β⦄, x ≤ f b → a ≤ b) ↔ f a ≤ x
        constructor
        · intro h
          by_contra hax
          have hlt : x < f a := lt_of_not_ge hax
          obtain ⟨z, hzRange, hz⟩ := hf.exists_between hlt
          rcases hzRange with ⟨b, rfl⟩
          exact (not_lt_of_ge (f.monotone (h hz.1.le))) hz.2
        · intro h b hb
          exact f.le_iff_le.mp (h.trans hb) }
  refine ⟨A, ?_⟩
  rw [DedekindCut.factorEmbedding_apply]
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨a, ha, rfl⟩
    exact ha
  · by_contra hx
    have hlt : sSup (f '' A.left) < x := lt_of_not_ge hx
    obtain ⟨z, hzRange, hz⟩ := hf.exists_between hlt
    rcases hzRange with ⟨a, rfl⟩
    have haLeft : a ∈ A.left := hz.2.le
    have haImage : f a ∈ f '' A.left := ⟨a, haLeft, rfl⟩
    exact (not_lt_of_ge (le_sSup haImage)) hz.1

/-- The order isomorphism from the Dedekind completion of a dense suborder onto
its complete target. -/
noncomputable def dedekindOrderIsoOfDenseRange
    {α : Type u} {β : Type v} [CompleteLinearOrder α] [LinearOrder β]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    (f : β ↪o α) (hf : DenseRange f) : DedekindCut β ≃o α :=
  StrictMono.orderIsoOfRightInverse (DedekindCut.factorEmbedding f)
    (DedekindCut.factorEmbedding f).strictMono
    (invFun (DedekindCut.factorEmbedding f))
    (rightInverse_invFun
      (dedekindFactorEmbedding_surjective_of_denseRange f hf))

/-- Every nontrivial separable complete dense linear order is order-isomorphic
to the real closed unit interval. -/
theorem exists_orderIso_unitInterval (α : Type u) [CompleteLinearOrder α]
    [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SeparableSpace α] [Nontrivial α] :
    Nonempty (α ≃o Set.Icc (0 : ℝ) 1) := by
  obtain ⟨s, hsCountable, hsDense, hsNoBot, hsNoTop⟩ :=
    exists_countable_dense_no_bot_top α
  let S := s
  letI : Countable S := hsCountable.to_subtype
  obtain ⟨m, hmS, _hm⟩ := hsDense.exists_between (bot_lt_top : (⊥ : α) < ⊤)
  letI : Nonempty S := ⟨⟨m, hmS⟩⟩
  letI : DenselyOrdered S :=
    { dense := by
        intro a b hab
        obtain ⟨c, hcS, hc⟩ := hsDense.exists_between hab
        exact ⟨⟨c, hcS⟩, hc⟩ }
  letI : NoMinOrder S :=
    { exists_lt := by
        intro a
        have ha : (⊥ : α) < a := by
          rw [bot_lt_iff_ne_bot]
          intro h
          exact hsNoBot ⊥ isBot_bot (h ▸ a.property)
        obtain ⟨c, hcS, hc⟩ := hsDense.exists_between ha
        exact ⟨⟨c, hcS⟩, hc.2⟩ }
  letI : NoMaxOrder S :=
    { exists_gt := by
        intro a
        have ha : (a : α) < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro h
          exact hsNoTop ⊤ isTop_top (h ▸ a.property)
        obtain ⟨c, hcS, hc⟩ := hsDense.exists_between ha
        exact ⟨⟨c, hcS⟩, hc.1⟩ }
  let QI := Set.Ioo (0 : ℚ) 1
  letI : Nonempty QI := Set.nonempty_Ioo_subtype (by norm_num)
  let eSQ : S ≃o QI := Classical.choice (@Order.iso_of_countable_dense S QI
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance)
  let qEmbed : QI ↪o Set.Icc (0 : ℝ) 1 :=
    OrderEmbedding.ofStrictMono
      (fun q => ⟨(q.1 : ℝ), by
        constructor
        · exact_mod_cast q.property.1.le
        · exact_mod_cast q.property.2.le⟩)
      (by
        intro a b hab
        change (a.1 : ℝ) < (b.1 : ℝ)
        exact_mod_cast hab)
  have hqDense : DenseRange qEmbed := by
    rw [DenseRange, dense_iff_exists_between]
    intro a b hab
    obtain ⟨q, hq⟩ := exists_rat_btwn (show (a.1 : ℝ) < b.1 from hab)
    have hq0 : (0 : ℚ) < q := by
      exact_mod_cast a.property.1.trans_lt hq.1
    have hq1 : q < (1 : ℚ) := by
      exact_mod_cast hq.2.trans_le b.property.2
    let q' : QI := ⟨q, hq0, hq1⟩
    refine ⟨qEmbed q', ⟨q', rfl⟩, ?_⟩
    exact hq
  let sAlpha : S ↪o α := OrderEmbedding.subtype s
  have hsAlphaDense : DenseRange sAlpha := by
    rw [DenseRange]
    have hrange : range (sAlpha : S → α) = s := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact hsDense
  let sUnit : S ↪o Set.Icc (0 : ℝ) 1 := eSQ.toOrderEmbedding.trans qEmbed
  have hsUnitDense : DenseRange sUnit := by
    rw [DenseRange]
    have hrange : range (sUnit : S → Set.Icc (0 : ℝ) 1) =
        range (qEmbed : QI → Set.Icc (0 : ℝ) 1) := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨eSQ a, rfl⟩
      · rintro ⟨q, rfl⟩
        obtain ⟨a, rfl⟩ := eSQ.surjective q
        exact ⟨a, rfl⟩
    rw [hrange]
    exact hqDense
  let sourceCompletion : DedekindCut S ≃o α :=
    dedekindOrderIsoOfDenseRange sAlpha hsAlphaDense
  let unitCompletion : DedekindCut S ≃o Set.Icc (0 : ℝ) 1 :=
    dedekindOrderIsoOfDenseRange sUnit hsUnitDense
  exact ⟨sourceCompletion.symm.trans unitCompletion⟩

/-- A chosen order isomorphism supplied by the classification theorem. -/
noncomputable def orderIsoUnitInterval (α : Type u) [CompleteLinearOrder α]
    [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SeparableSpace α] [Nontrivial α] :
    α ≃o Set.Icc (0 : ℝ) 1 :=
  Classical.choice (exists_orderIso_unitInterval α)

end SeparableLinearContinuum

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

variable {E U : Set PlanePoint}

/-- Distinct split points make the left completed chain nontrivial. -/
theorem leftCompletedChainNontrivial (D : SelectedBoundaryTopologyInput E U) :
    Nontrivial D.leftCompletedChain :=
  ⟨⟨D.leftCompletedChainBottom, D.leftCompletedChainTop, by
    intro h
    exact D.lowerSplitPoint_ne_upperSplitPoint (congrArg Subtype.val h)⟩⟩

/-- Distinct split points make the right completed chain nontrivial. -/
theorem rightCompletedChainNontrivial (D : SelectedBoundaryTopologyInput E U) :
    Nontrivial D.rightCompletedChain :=
  ⟨⟨D.rightCompletedChainBottom, D.rightCompletedChainTop, by
    intro h
    exact D.lowerSplitPoint_ne_upperSplitPoint (congrArg Subtype.val h)⟩⟩

/-- The intrinsic left-chain order is the real closed unit interval order. -/
noncomputable def leftCompletedChainOrderIsoUnitInterval
    (D : SelectedBoundaryTopologyInput E U) :
    letI : LE D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLE
    letI : LT D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLT
    letI : Preorder D.leftCompletedChain :=
      D.leftCompletedChainLinearOrder.toPreorder
    letI : LinearOrder D.leftCompletedChain := D.leftCompletedChainLinearOrder
    D.leftCompletedChain ≃o Set.Icc (0 : ℝ) 1 := by
  letI : LE D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLE
  letI : LT D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLT
  letI : LinearOrder D.leftCompletedChain := D.leftCompletedChainLinearOrder
  letI : Preorder D.leftCompletedChain :=
    D.leftCompletedChainLinearOrder.toPreorder
  letI : CompleteLinearOrder D.leftCompletedChain :=
    D.leftCompletedChainCompleteLinearOrder
  letI : DenselyOrdered D.leftCompletedChain :=
    D.leftCompletedChain_denselyOrdered
  letI : OrderTopology D.leftCompletedChain :=
    D.leftCompletedChainPlanarOrderTopology
  letI : Nontrivial D.leftCompletedChain := D.leftCompletedChainNontrivial
  exact SeparableLinearContinuum.orderIsoUnitInterval D.leftCompletedChain

/-- The intrinsic right-chain order is the real closed unit interval order. -/
noncomputable def rightCompletedChainOrderIsoUnitInterval
    (D : SelectedBoundaryTopologyInput E U) :
    letI : LE D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLE
    letI : LT D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLT
    letI : Preorder D.rightCompletedChain :=
      D.rightCompletedChainLinearOrder.toPreorder
    letI : LinearOrder D.rightCompletedChain := D.rightCompletedChainLinearOrder
    D.rightCompletedChain ≃o Set.Icc (0 : ℝ) 1 := by
  letI : LE D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLE
  letI : LT D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLT
  letI : LinearOrder D.rightCompletedChain := D.rightCompletedChainLinearOrder
  letI : Preorder D.rightCompletedChain :=
    D.rightCompletedChainLinearOrder.toPreorder
  letI : CompleteLinearOrder D.rightCompletedChain :=
    D.rightCompletedChainCompleteLinearOrder
  letI : DenselyOrdered D.rightCompletedChain :=
    D.rightCompletedChain_denselyOrdered
  letI : OrderTopology D.rightCompletedChain :=
    D.rightCompletedChainPlanarOrderTopology
  letI : Nontrivial D.rightCompletedChain := D.rightCompletedChainNontrivial
  exact SeparableLinearContinuum.orderIsoUnitInterval D.rightCompletedChain

/-- Endpoint-preserving planar-subspace parameterization of the completed left
chain by the real closed unit interval. -/
noncomputable def leftCompletedChainHomeomorph
    (D : SelectedBoundaryTopologyInput E U) :
    Set.Icc (0 : ℝ) 1 ≃ₜ D.leftCompletedChain := by
  letI : LE D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLE
  letI : LT D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLT
  letI : LinearOrder D.leftCompletedChain := D.leftCompletedChainLinearOrder
  letI : Preorder D.leftCompletedChain :=
    D.leftCompletedChainLinearOrder.toPreorder
  letI : CompleteLinearOrder D.leftCompletedChain :=
    D.leftCompletedChainCompleteLinearOrder
  letI : DenselyOrdered D.leftCompletedChain :=
    D.leftCompletedChain_denselyOrdered
  letI : OrderTopology D.leftCompletedChain :=
    D.leftCompletedChainPlanarOrderTopology
  letI : Nontrivial D.leftCompletedChain := D.leftCompletedChainNontrivial
  exact D.leftCompletedChainOrderIsoUnitInterval.symm.toHomeomorph

/-- Endpoint-preserving planar-subspace parameterization of the completed right
chain by the real closed unit interval. -/
noncomputable def rightCompletedChainHomeomorph
    (D : SelectedBoundaryTopologyInput E U) :
    Set.Icc (0 : ℝ) 1 ≃ₜ D.rightCompletedChain := by
  letI : LE D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLE
  letI : LT D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLT
  letI : LinearOrder D.rightCompletedChain := D.rightCompletedChainLinearOrder
  letI : Preorder D.rightCompletedChain :=
    D.rightCompletedChainLinearOrder.toPreorder
  letI : CompleteLinearOrder D.rightCompletedChain :=
    D.rightCompletedChainCompleteLinearOrder
  letI : DenselyOrdered D.rightCompletedChain :=
    D.rightCompletedChain_denselyOrdered
  letI : OrderTopology D.rightCompletedChain :=
    D.rightCompletedChainPlanarOrderTopology
  letI : Nontrivial D.rightCompletedChain := D.rightCompletedChainNontrivial
  exact D.rightCompletedChainOrderIsoUnitInterval.symm.toHomeomorph

/-- The left-chain parameterization starts at the intrinsic lower split point. -/
theorem leftCompletedChainHomeomorph_zero
    (D : SelectedBoundaryTopologyInput E U) :
    ((D.leftCompletedChainHomeomorph ⟨0, by norm_num⟩ :
        D.leftCompletedChain) : PlanePoint) = D.lowerSplitPoint := by
  letI : LE D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLE
  letI : LT D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLT
  letI : Preorder D.leftCompletedChain :=
    D.leftCompletedChainLinearOrder.toPreorder
  letI : LinearOrder D.leftCompletedChain := D.leftCompletedChainLinearOrder
  let e := D.leftCompletedChainOrderIsoUnitInterval
  have hle : e.symm ⟨0, by norm_num⟩ ≤ D.leftCompletedChainBottom := by
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    exact (e D.leftCompletedChainBottom).property.1
  have hge : D.leftCompletedChainBottom ≤ e.symm ⟨0, by norm_num⟩ :=
    D.leftCompletedChainBottom_le _
  exact congrArg Subtype.val
    (D.leftCompletedChainLinearOrder.le_antisymm _ _ hle hge)

/-- The left-chain parameterization ends at the intrinsic upper split point. -/
theorem leftCompletedChainHomeomorph_one
    (D : SelectedBoundaryTopologyInput E U) :
    ((D.leftCompletedChainHomeomorph ⟨1, by norm_num⟩ :
        D.leftCompletedChain) : PlanePoint) = D.upperSplitPoint := by
  letI : LE D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLE
  letI : LT D.leftCompletedChain := D.leftCompletedChainLinearOrder.toLT
  letI : Preorder D.leftCompletedChain :=
    D.leftCompletedChainLinearOrder.toPreorder
  letI : LinearOrder D.leftCompletedChain := D.leftCompletedChainLinearOrder
  let e := D.leftCompletedChainOrderIsoUnitInterval
  have hle : e.symm ⟨1, by norm_num⟩ ≤ D.leftCompletedChainTop :=
    D.leftCompletedChain_le_top _
  have hge : D.leftCompletedChainTop ≤ e.symm ⟨1, by norm_num⟩ := by
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    exact (e D.leftCompletedChainTop).property.2
  exact congrArg Subtype.val
    (D.leftCompletedChainLinearOrder.le_antisymm _ _ hle hge)

/-- The right-chain parameterization starts at the intrinsic lower split point. -/
theorem rightCompletedChainHomeomorph_zero
    (D : SelectedBoundaryTopologyInput E U) :
    ((D.rightCompletedChainHomeomorph ⟨0, by norm_num⟩ :
        D.rightCompletedChain) : PlanePoint) = D.lowerSplitPoint := by
  letI : LE D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLE
  letI : LT D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLT
  letI : Preorder D.rightCompletedChain :=
    D.rightCompletedChainLinearOrder.toPreorder
  letI : LinearOrder D.rightCompletedChain := D.rightCompletedChainLinearOrder
  let e := D.rightCompletedChainOrderIsoUnitInterval
  have hle : e.symm ⟨0, by norm_num⟩ ≤ D.rightCompletedChainBottom := by
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    exact (e D.rightCompletedChainBottom).property.1
  have hge : D.rightCompletedChainBottom ≤ e.symm ⟨0, by norm_num⟩ :=
    D.rightCompletedChainBottom_le _
  exact congrArg Subtype.val
    (D.rightCompletedChainLinearOrder.le_antisymm _ _ hle hge)

/-- The right-chain parameterization ends at the intrinsic upper split point. -/
theorem rightCompletedChainHomeomorph_one
    (D : SelectedBoundaryTopologyInput E U) :
    ((D.rightCompletedChainHomeomorph ⟨1, by norm_num⟩ :
        D.rightCompletedChain) : PlanePoint) = D.upperSplitPoint := by
  letI : LE D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLE
  letI : LT D.rightCompletedChain := D.rightCompletedChainLinearOrder.toLT
  letI : Preorder D.rightCompletedChain :=
    D.rightCompletedChainLinearOrder.toPreorder
  letI : LinearOrder D.rightCompletedChain := D.rightCompletedChainLinearOrder
  let e := D.rightCompletedChainOrderIsoUnitInterval
  have hle : e.symm ⟨1, by norm_num⟩ ≤ D.rightCompletedChainTop :=
    D.rightCompletedChain_le_top _
  have hge : D.rightCompletedChainTop ≤ e.symm ⟨1, by norm_num⟩ := by
    apply e.le_iff_le.mp
    rw [e.apply_symm_apply]
    exact (e D.rightCompletedChainTop).property.2
  exact congrArg Subtype.val
    (D.rightCompletedChainLinearOrder.le_antisymm _ _ hle hge)

/-- The planar image of the left parameterization is exactly the completed
left chain. -/
theorem range_leftCompletedChainHomeomorph
    (D : SelectedBoundaryTopologyInput E U) :
    range (fun t => ((D.leftCompletedChainHomeomorph t :
      D.leftCompletedChain) : PlanePoint)) = D.leftCompletedChain := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact (D.leftCompletedChainHomeomorph t).property
  · intro hp
    let q : D.leftCompletedChain := ⟨p, hp⟩
    exact ⟨D.leftCompletedChainHomeomorph.symm q,
      congrArg Subtype.val (D.leftCompletedChainHomeomorph.apply_symm_apply q)⟩

/-- The planar image of the right parameterization is exactly the completed
right chain. -/
theorem range_rightCompletedChainHomeomorph
    (D : SelectedBoundaryTopologyInput E U) :
    range (fun t => ((D.rightCompletedChainHomeomorph t :
      D.rightCompletedChain) : PlanePoint)) = D.rightCompletedChain := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact (D.rightCompletedChainHomeomorph t).property
  · intro hp
    let q : D.rightCompletedChain := ⟨p, hp⟩
    exact ⟨D.rightCompletedChainHomeomorph.symm q,
      congrArg Subtype.val (D.rightCompletedChainHomeomorph.apply_symm_apply q)⟩

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
