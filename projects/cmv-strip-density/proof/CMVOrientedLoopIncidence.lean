import CMVOrientedLoopPiecewiseAtlas

/-!
# Derived finite-arc incidence at localized boundary cuts

The compact chart-cut system contains no supplied adjacency data.  This module
isolates each derived cut point inside its actual interval chart.  The two
punctured parameter half-intervals therefore contain no other global cut point;
they are the two local germs from which cyclic incidence is assembled.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- A positive compact-core radius around one derived cut point which contains
no other point of the finite global cut set.  This is selected from the actual
interval chart and finiteness of `cutPoints`; no incidence ordering is supplied. -/
structure CutPointCoreNeighborhood
    (D : FiniteChartCutSystem A) (v : D.cutPoints) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_coreRadius : radius < (A.intervalAt v.1).coreRadius
  no_other_cutPoint :
    ∀ t : (A.intervalAt v.1).CoreParameter,
      |(t : ℝ)| < radius → (t : ℝ) ≠ 0 →
        (A.intervalAt v.1).corePoint t ∉ D.cutPoints

namespace CutPointCoreNeighborhood

variable {D : FiniteChartCutSystem A} {v : D.cutPoints}

/-- The zero compact-core parameter at a cut point. -/
def zeroCoreParameter (D : FiniteChartCutSystem A) (v : D.cutPoints) :
    (A.intervalAt v.1).CoreParameter :=
  ⟨0, by
    exact ⟨le_of_lt (neg_neg_of_pos (A.intervalAt v.1).coreRadius_pos),
      le_of_lt (A.intervalAt v.1).coreRadius_pos⟩⟩

/-- The zero compact-core parameter is the indexing cut point. -/
theorem corePoint_zero (D : FiniteChartCutSystem A) (v : D.cutPoints) :
    (A.intervalAt v.1).corePoint (zeroCoreParameter D v) = v.1 := by
  let C := A.intervalAt v.1
  have hparameter :
      C.coreParameterToParameterInterval (zeroCoreParameter D v) =
        C.zeroParameter := by
    apply Subtype.ext
    rfl
  change (C.parameterHomeomorph.symm
    (C.coreParameterToParameterInterval (zeroCoreParameter D v))).1 = v.1
  rw [hparameter, ← C.parameterHomeomorph_base,
    C.parameterHomeomorph.symm_apply_apply]
  rfl

end CutPointCoreNeighborhood

/-- Every derived cut point admits an actual compact-core neighborhood avoiding
all other cut points. -/
theorem exists_cutPointCoreNeighborhood
    (D : FiniteChartCutSystem A) (v : D.cutPoints) :
    Nonempty (CutPointCoreNeighborhood D v) := by
  classical
  let C := A.intervalAt v.1
  let z : C.CoreParameter := CutPointCoreNeighborhood.zeroCoreParameter D v
  let others : Set (FrontierSpace O) :=
    (D.cutPoints.erase v.1 : Finset (FrontierSpace O))
  have hothersClosed : IsClosed others := by
    exact (D.cutPoints.erase v.1).finite_toSet.isClosed
  have hvOthers : v.1 ∉ others := by
    simp [others]
  have hzPoint : C.corePoint z = v.1 := by
    simpa only [C, z] using CutPointCoreNeighborhood.corePoint_zero D v
  have hzPreimage : z ∈ C.corePoint ⁻¹' othersᶜ := by
    change C.corePoint z ∉ others
    simpa only [hzPoint] using hvOthers
  have hopen : IsOpen (C.corePoint ⁻¹' othersᶜ) :=
    hothersClosed.isOpen_compl.preimage C.continuous_corePoint
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hopen z hzPreimage
  let rho : ℝ := min epsilon C.coreRadius / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact div_pos (lt_min hepsilon C.coreRadius_pos) (by norm_num)
  have hrhoEpsilon : rho < epsilon := by
    dsimp only [rho]
    have hle := min_le_left epsilon C.coreRadius
    linarith
  have hrhoCore : rho < C.coreRadius := by
    dsimp only [rho]
    have hminPos : 0 < min epsilon C.coreRadius :=
      lt_min hepsilon C.coreRadius_pos
    have hle := min_le_right epsilon C.coreRadius
    linarith
  refine ⟨{
    radius := rho
    radius_pos := hrho
    radius_lt_coreRadius := by simpa only [C] using hrhoCore
    no_other_cutPoint := ?_
  }⟩
  intro t htRho htZero htCut
  have htCoreDist : dist t z < epsilon := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(t : ℝ) - 0| < epsilon
    simpa only [sub_zero] using htRho.trans hrhoEpsilon
  have htNotOthers : C.corePoint t ∉ others := by
    exact hball (Metric.mem_ball.mpr htCoreDist)
  apply htNotOthers
  have htPointNe : C.corePoint t ≠ v.1 := by
    intro htPoint
    have htEq : t = z := C.injective_corePoint (htPoint.trans hzPoint.symm)
    apply htZero
    exact congrArg Subtype.val htEq
  exact Finset.mem_erase.mpr ⟨htPointNe, htCut⟩

/-- Canonical choice of the cut-free compact-core neighborhood. -/
noncomputable def cutPointCoreNeighborhood
    (D : FiniteChartCutSystem A) (v : D.cutPoints) :
    CutPointCoreNeighborhood D v :=
  Classical.choice (D.exists_cutPointCoreNeighborhood v)

namespace CutPointCoreNeighborhood

variable {D : FiniteChartCutSystem A} {v : D.cutPoints}

/-- The cut-free negative local half-interval in compact-core coordinates. -/
def negativeParameters (N : CutPointCoreNeighborhood D v) :
    Set (A.intervalAt v.1).CoreParameter :=
  {t | -N.radius < (t : ℝ) ∧ (t : ℝ) < 0}

/-- The cut-free positive local half-interval in compact-core coordinates. -/
def positiveParameters (N : CutPointCoreNeighborhood D v) :
    Set (A.intervalAt v.1).CoreParameter :=
  {t | 0 < (t : ℝ) ∧ (t : ℝ) < N.radius}

/-- Every negative local parameter realizes an actual point in the global cut
complement. -/
def negativePoint (N : CutPointCoreNeighborhood D v)
    (t : N.negativeParameters) : D.CutSpace :=
  ⟨(A.intervalAt v.1).corePoint t.1, by
    apply N.no_other_cutPoint t.1
    · rw [abs_lt]
      exact ⟨t.2.1, t.2.2.trans N.radius_pos⟩
    · exact ne_of_lt t.2.2⟩

/-- Every positive local parameter realizes an actual point in the global cut
complement. -/
def positivePoint (N : CutPointCoreNeighborhood D v)
    (t : N.positiveParameters) : D.CutSpace :=
  ⟨(A.intervalAt v.1).corePoint t.1, by
    apply N.no_other_cutPoint t.1
    · rw [abs_lt]
      exact ⟨(neg_neg_of_pos N.radius_pos).trans t.2.1, t.2.2⟩
    · exact ne_of_gt t.2.1⟩

/-- Both local half-intervals are nonempty. -/
theorem negativeParameters_nonempty (N : CutPointCoreNeighborhood D v) :
    N.negativeParameters.Nonempty := by
  let t : (A.intervalAt v.1).CoreParameter :=
    ⟨-(N.radius / 2), by
      constructor <;>
        linarith [N.radius_pos, N.radius_lt_coreRadius]⟩
  exact ⟨t, by
    change -N.radius < -(N.radius / 2) ∧ -(N.radius / 2) < 0
    constructor <;> linarith [N.radius_pos]⟩

theorem positiveParameters_nonempty (N : CutPointCoreNeighborhood D v) :
    N.positiveParameters.Nonempty := by
  let t : (A.intervalAt v.1).CoreParameter :=
    ⟨N.radius / 2, by
      constructor <;>
        linarith [N.radius_pos, N.radius_lt_coreRadius]⟩
  exact ⟨t, by
    change 0 < N.radius / 2 ∧ N.radius / 2 < N.radius
    constructor <;> linarith [N.radius_pos]⟩

/-- Each cut-free local half-interval is connected. -/
theorem isConnected_negativeParameters (N : CutPointCoreNeighborhood D v) :
    IsConnected N.negativeParameters := by
  constructor
  · exact N.negativeParameters_nonempty
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage :
        Subtype.val '' N.negativeParameters = Ioo (-N.radius) 0 := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hs
      · intro ht
        let s : (A.intervalAt v.1).CoreParameter :=
          ⟨t, by
            constructor <;>
              linarith [ht.1, ht.2, N.radius_pos,
                N.radius_lt_coreRadius]⟩
        exact ⟨s, ht, rfl⟩
    rw [himage]
    exact isPreconnected_Ioo

theorem isConnected_positiveParameters (N : CutPointCoreNeighborhood D v) :
    IsConnected N.positiveParameters := by
  constructor
  · exact N.positiveParameters_nonempty
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage :
        Subtype.val '' N.positiveParameters = Ioo 0 N.radius := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hs
      · intro ht
        let s : (A.intervalAt v.1).CoreParameter :=
          ⟨t, by
            constructor <;>
              linarith [ht.1, ht.2, N.radius_pos,
                N.radius_lt_coreRadius]⟩
        exact ⟨s, ht, rfl⟩
    rw [himage]
    exact isPreconnected_Ioo

/-- Membership in one quotient-indexed open arc is exactly equality of the
connected-component class in the global cut complement. -/
theorem mem_finiteArcInterior_iff_componentClass
    (D : FiniteChartCutSystem A) (x : D.CutSpace) (e : D.ArcIndex) :
    x.1 ∈ D.finiteArcInterior e ↔
      (x : ConnectedComponents D.CutSpace) = e := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : x = y := Subtype.ext hyx.symm
    rw [hxy, ← D.arcRepresentative_class e]
    exact ConnectedComponents.coe_eq_coe.mpr
      (connectedComponent_eq hy).symm
  · intro hx
    have hclasses :
        (x : ConnectedComponents D.CutSpace) =
          (D.arcRepresentative e : ConnectedComponents D.CutSpace) := by
      rw [D.arcRepresentative_class e]
      exact hx
    have hcomponents :
        connectedComponent x = connectedComponent (D.arcRepresentative e) :=
      ConnectedComponents.coe_eq_coe.mp hclasses
    exact ⟨x, by
      rw [← hcomponents]
      exact mem_connectedComponent, rfl⟩

/-- The actual cut-complement points realized by the negative local germ vary
continuously. -/
theorem continuous_negativePoint (N : CutPointCoreNeighborhood D v) :
    Continuous N.negativePoint := by
  apply Continuous.subtype_mk
  exact (A.intervalAt v.1).continuous_corePoint.comp continuous_subtype_val

/-- The actual cut-complement points realized by the positive local germ vary
continuously. -/
theorem continuous_positivePoint (N : CutPointCoreNeighborhood D v) :
    Continuous N.positivePoint := by
  apply Continuous.subtype_mk
  exact (A.intervalAt v.1).continuous_corePoint.comp continuous_subtype_val

/-- Each cut-free local germ remains connected after realization in the actual
global cut complement. -/
theorem isConnected_range_negativePoint
    (N : CutPointCoreNeighborhood D v) :
    IsConnected (Set.range N.negativePoint) := by
  letI : ConnectedSpace N.negativeParameters :=
    isConnected_iff_connectedSpace.mp N.isConnected_negativeParameters
  exact isConnected_range N.continuous_negativePoint

theorem isConnected_range_positivePoint
    (N : CutPointCoreNeighborhood D v) :
    IsConnected (Set.range N.positivePoint) := by
  letI : ConnectedSpace N.positiveParameters :=
    isConnected_iff_connectedSpace.mp N.isConnected_positiveParameters
  exact isConnected_range N.continuous_positivePoint

/-- A fixed actual point and quotient-indexed global arc on the negative local
germ. -/
noncomputable def negativeRepresentative
    (N : CutPointCoreNeighborhood D v) : N.negativeParameters :=
  Classical.choice (Set.nonempty_coe_sort.mpr N.negativeParameters_nonempty)

noncomputable def negativeArcIndex
    (N : CutPointCoreNeighborhood D v) : D.ArcIndex :=
  (N.negativePoint N.negativeRepresentative :
    ConnectedComponents D.CutSpace)

/-- A fixed actual point and quotient-indexed global arc on the positive local
germ. -/
noncomputable def positiveRepresentative
    (N : CutPointCoreNeighborhood D v) : N.positiveParameters :=
  Classical.choice (Set.nonempty_coe_sort.mpr N.positiveParameters_nonempty)

noncomputable def positiveArcIndex
    (N : CutPointCoreNeighborhood D v) : D.ArcIndex :=
  (N.positivePoint N.positiveRepresentative :
    ConnectedComponents D.CutSpace)

/-- Every point of a cut-free local germ belongs to its selected global open
arc, so no local incidence has been supplied by the definitions. -/
theorem negativePoint_mem_finiteArcInterior
    (N : CutPointCoreNeighborhood D v) (t : N.negativeParameters) :
    (N.negativePoint t).1 ∈ D.finiteArcInterior N.negativeArcIndex := by
  rw [mem_finiteArcInterior_iff_componentClass]
  apply ConnectedComponents.coe_eq_coe.mpr
  apply connectedComponent_eq
  exact N.isConnected_range_negativePoint.subset_connectedComponent
    ⟨t, rfl⟩
    ⟨N.negativeRepresentative, rfl⟩

theorem positivePoint_mem_finiteArcInterior
    (N : CutPointCoreNeighborhood D v) (t : N.positiveParameters) :
    (N.positivePoint t).1 ∈ D.finiteArcInterior N.positiveArcIndex := by
  rw [mem_finiteArcInterior_iff_componentClass]
  apply ConnectedComponents.coe_eq_coe.mpr
  apply connectedComponent_eq
  exact N.isConnected_range_positivePoint.subset_connectedComponent
    ⟨t, rfl⟩
    ⟨N.positiveRepresentative, rfl⟩

/-- The indexing cut point is approached by the negative local germ. -/
theorem cutPoint_mem_closure_negativeParameters
    (N : CutPointCoreNeighborhood D v) :
    CutPointCoreNeighborhood.zeroCoreParameter D v ∈
      closure N.negativeParameters := by
  let C := A.intervalAt v.1
  let z : C.CoreParameter :=
    CutPointCoreNeighborhood.zeroCoreParameter D v
  let s : ℕ → C.CoreParameter := fun n =>
    ⟨-N.radius / (n + 2 : ℝ), by
      have hn : (0 : ℝ) < n + 2 := by positivity
      have hfrac : N.radius / (n + 2 : ℝ) < N.radius := by
        rw [div_lt_iff₀ hn]
        nlinarith [N.radius_pos]
      have hnegative : -N.radius < -N.radius / (n + 2 : ℝ) := by
        rw [neg_div]
        exact neg_lt_neg hfrac
      have hbelowZero :
          -N.radius / (n + 2 : ℝ) < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos N.radius_pos) hn
      constructor <;>
        linarith [N.radius_pos, N.radius_lt_coreRadius]⟩
  have hsMem (n : ℕ) : s n ∈ N.negativeParameters := by
    change -N.radius < -N.radius / (n + 2 : ℝ) ∧
      -N.radius / (n + 2 : ℝ) < 0
    have hn : (0 : ℝ) < n + 2 := by positivity
    have hfrac : N.radius / (n + 2 : ℝ) < N.radius := by
      rw [div_lt_iff₀ hn]
      nlinarith [N.radius_pos]
    constructor
    · rw [neg_div]
      exact neg_lt_neg hfrac
    · exact div_neg_of_neg_of_pos (neg_neg_of_pos N.radius_pos) hn
  have hsLim : Tendsto s atTop (𝓝 z) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun n : ℕ => -N.radius / (n + 2 : ℝ))
      atTop (𝓝 0)
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => N.radius / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    simpa only [neg_div, neg_zero] using hdiv.neg
  rw [mem_closure_iff_seq_limit]
  exact ⟨s, hsMem, hsLim⟩

/-- The indexing cut point is approached by the positive local germ. -/
theorem cutPoint_mem_closure_positiveParameters
    (N : CutPointCoreNeighborhood D v) :
    CutPointCoreNeighborhood.zeroCoreParameter D v ∈
      closure N.positiveParameters := by
  let C := A.intervalAt v.1
  let z : C.CoreParameter :=
    CutPointCoreNeighborhood.zeroCoreParameter D v
  let s : ℕ → C.CoreParameter := fun n =>
    ⟨N.radius / (n + 2 : ℝ), by
      have hn : (0 : ℝ) < n + 2 := by positivity
      have hpositive : 0 < N.radius / (n + 2 : ℝ) :=
        div_pos N.radius_pos hn
      have hfrac : N.radius / (n + 2 : ℝ) < N.radius := by
        rw [div_lt_iff₀ hn]
        nlinarith [N.radius_pos]
      constructor <;>
        linarith [N.radius_pos, N.radius_lt_coreRadius]⟩
  have hsMem (n : ℕ) : s n ∈ N.positiveParameters := by
    change 0 < N.radius / (n + 2 : ℝ) ∧
      N.radius / (n + 2 : ℝ) < N.radius
    have hn : (0 : ℝ) < n + 2 := by positivity
    constructor
    · exact div_pos N.radius_pos hn
    · rw [div_lt_iff₀ hn]
      nlinarith [N.radius_pos]
  have hsLim : Tendsto s atTop (𝓝 z) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun n : ℕ => N.radius / (n + 2 : ℝ))
      atTop (𝓝 0)
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
  rw [mem_closure_iff_seq_limit]
  exact ⟨s, hsMem, hsLim⟩

/-- The negative local germ determines an actual quotient-indexed arc incident
to the indexing cut point. -/
theorem cutPoint_mem_negativeArcClosure
    (N : CutPointCoreNeighborhood D v) :
    v.1 ∈ D.finiteArcClosure N.negativeArcIndex := by
  rw [finiteArcClosure]
  have hzImage :
      (A.intervalAt v.1).corePoint
          (CutPointCoreNeighborhood.zeroCoreParameter D v) ∈
        closure ((A.intervalAt v.1).corePoint '' N.negativeParameters) := by
    exact image_closure_subset_closure_image
      (A.intervalAt v.1).continuous_corePoint
      ⟨CutPointCoreNeighborhood.zeroCoreParameter D v,
        N.cutPoint_mem_closure_negativeParameters, rfl⟩
  rw [CutPointCoreNeighborhood.corePoint_zero D v] at hzImage
  apply closure_mono (s := (A.intervalAt v.1).corePoint ''
    N.negativeParameters) ?_ hzImage
  rintro q ⟨t, ht, rfl⟩
  exact N.negativePoint_mem_finiteArcInterior ⟨t, ht⟩

/-- The positive local germ determines an actual quotient-indexed arc incident
to the indexing cut point. -/
theorem cutPoint_mem_positiveArcClosure
    (N : CutPointCoreNeighborhood D v) :
    v.1 ∈ D.finiteArcClosure N.positiveArcIndex := by
  rw [finiteArcClosure]
  have hzImage :
      (A.intervalAt v.1).corePoint
          (CutPointCoreNeighborhood.zeroCoreParameter D v) ∈
        closure ((A.intervalAt v.1).corePoint '' N.positiveParameters) := by
    exact image_closure_subset_closure_image
      (A.intervalAt v.1).continuous_corePoint
      ⟨CutPointCoreNeighborhood.zeroCoreParameter D v,
        N.cutPoint_mem_closure_positiveParameters, rfl⟩
  rw [CutPointCoreNeighborhood.corePoint_zero D v] at hzImage
  apply closure_mono (s := (A.intervalAt v.1).corePoint ''
    N.positiveParameters) ?_ hzImage
  rintro q ⟨t, ht, rfl⟩
  exact N.positivePoint_mem_finiteArcInterior ⟨t, ht⟩

/-- Both actual local germs are represented in the finite incidence family at
the cut point. -/
theorem negativeArcIndex_mem_incidentArc
    (N : CutPointCoreNeighborhood D v) :
    Nonempty {e : D.IncidentArc v | e.1 = N.negativeArcIndex} :=
  ⟨⟨⟨N.negativeArcIndex, N.cutPoint_mem_negativeArcClosure⟩, rfl⟩⟩

theorem positiveArcIndex_mem_incidentArc
    (N : CutPointCoreNeighborhood D v) :
    Nonempty {e : D.IncidentArc v | e.1 = N.positiveArcIndex} :=
  ⟨⟨⟨N.positiveArcIndex, N.cutPoint_mem_positiveArcClosure⟩, rfl⟩⟩

end CutPointCoreNeighborhood
namespace CutPointCoreNeighborhood

variable {D : FiniteChartCutSystem A} {v : D.cutPoints}


/-- The actual open frontier neighborhood corresponding to the cut-free
two-sided parameter interval. -/
def localNeighborhood (N : CutPointCoreNeighborhood D v) :
    Set (FrontierSpace O) :=
  Subtype.val '' {q : (A.intervalAt v.1).localDomain |
    ((A.intervalAt v.1).parameterHomeomorph q : ℝ) ∈
      Ioo (-N.radius) N.radius}

theorem isOpen_localNeighborhood (N : CutPointCoreNeighborhood D v) :
    IsOpen N.localNeighborhood := by
  apply (A.intervalAt v.1).isOpen_localDomain.isOpenMap_subtype_val
  exact isOpen_Ioo.preimage
    (continuous_subtype_val.comp
      (A.intervalAt v.1).parameterHomeomorph.continuous)

theorem cutPoint_mem_localNeighborhood
    (N : CutPointCoreNeighborhood D v) :
    v.1 ∈ N.localNeighborhood := by
  refine ⟨(A.intervalAt v.1).baseInLocalDomain, ?_, rfl⟩
  change
    ((A.intervalAt v.1).parameterHomeomorph
      (A.intervalAt v.1).baseInLocalDomain : ℝ) ∈
        Ioo (-N.radius) N.radius
  rw [(A.intervalAt v.1).parameterHomeomorph_base]
  exact ⟨neg_neg_of_pos N.radius_pos, N.radius_pos⟩

/-- Every point in the small actual frontier neighborhood has a compact-core
parameter of absolute value below the selected radius. -/
theorem exists_coreParameter_of_mem_localNeighborhood
    (N : CutPointCoreNeighborhood D v) {q : FrontierSpace O}
    (hq : q ∈ N.localNeighborhood) :
    ∃ t : (A.intervalAt v.1).CoreParameter,
      |(t : ℝ)| < N.radius ∧
      (A.intervalAt v.1).corePoint t = q := by
  let C := A.intervalAt v.1
  rcases hq with ⟨qLocal, hqParameter, rfl⟩
  change
    -(N.radius) < (C.parameterHomeomorph qLocal : ℝ) ∧
      (C.parameterHomeomorph qLocal : ℝ) < N.radius at hqParameter
  let t : C.CoreParameter :=
    ⟨(C.parameterHomeomorph qLocal : ℝ), by
      constructor <;>
        linarith [hqParameter.1, hqParameter.2,
          N.radius_lt_coreRadius]⟩
  refine ⟨t, ?_, ?_⟩
  · rw [abs_lt]
    exact hqParameter
  · unfold ActualFrontierIntervalChart.corePoint
    have hparameter :
        C.coreParameterToParameterInterval t =
          C.parameterHomeomorph qLocal := by
      apply Subtype.ext
      rfl
    rw [hparameter, C.parameterHomeomorph.symm_apply_apply]

/-- The selected vertex is the only global cut point in its small actual
frontier neighborhood. -/
theorem eq_cutPoint_of_mem_localNeighborhood
    (N : CutPointCoreNeighborhood D v) {q : FrontierSpace O}
    (hqLocal : q ∈ N.localNeighborhood) (hqCut : q ∈ D.cutPoints) :
    q = v.1 := by
  obtain ⟨t, htSmall, htPoint⟩ :=
    N.exists_coreParameter_of_mem_localNeighborhood hqLocal
  by_contra hqv
  have htZero : (t : ℝ) ≠ 0 := by
    intro ht
    have htEq :
        t = CutPointCoreNeighborhood.zeroCoreParameter D v := by
      apply Subtype.ext
      exact ht
    apply hqv
    rw [← htPoint, htEq,
      CutPointCoreNeighborhood.corePoint_zero D v]
  apply N.no_other_cutPoint t htSmall htZero
  rw [htPoint]
  exact hqCut

/-- Every quotient-indexed arc incident to a cut point is one of the two arcs
derived from the negative and positive local germs.  This is the degree-at-most
two half of the cyclic incidence theorem; no adjacency list is assumed. -/
theorem incidentArc_eq_negativeArcIndex_or_positiveArcIndex
    (N : CutPointCoreNeighborhood D v) (e : D.IncidentArc v) :
    e.1 = N.negativeArcIndex ∨ e.1 = N.positiveArcIndex := by
  have hvClosure : v.1 ∈ closure (D.finiteArcInterior e.1) := by
    simpa only [finiteArcClosure] using e.2
  have hinter :
      (D.finiteArcInterior e.1 ∩ N.localNeighborhood).Nonempty :=
    (closure_inter_open_nonempty_iff N.isOpen_localNeighborhood).mp
      ⟨v.1, hvClosure, N.cutPoint_mem_localNeighborhood⟩
  obtain ⟨q, hqArc, hqLocal⟩ := hinter
  have hqNotCut :
      q ∉ D.cutPoints :=
    D.finiteArcInterior_subset_cutSpaceCarrier e.1 hqArc
  let qCut : D.CutSpace := ⟨q, hqNotCut⟩
  have hqClass :
      (qCut : ConnectedComponents D.CutSpace) = e.1 :=
    (mem_finiteArcInterior_iff_componentClass D qCut e.1).mp hqArc
  obtain ⟨t, htSmall, htPoint⟩ :=
    N.exists_coreParameter_of_mem_localNeighborhood hqLocal
  have htZero : (t : ℝ) ≠ 0 := by
    intro ht
    have htEq :
        t = CutPointCoreNeighborhood.zeroCoreParameter D v := by
      apply Subtype.ext
      exact ht
    have hqv : q = v.1 := by
      rw [← htPoint, htEq,
        CutPointCoreNeighborhood.corePoint_zero D v]
    exact hqNotCut (hqv ▸ v.2)
  rcases lt_or_gt_of_ne htZero with htNeg | htPos
  · left
    have htBounds := (abs_lt.mp htSmall)
    let tNeg : N.negativeParameters := ⟨t, htBounds.1, htNeg⟩
    have htMem :
        (N.negativePoint tNeg).1 ∈
          D.finiteArcInterior N.negativeArcIndex :=
      N.negativePoint_mem_finiteArcInterior tNeg
    have htClass :
        (N.negativePoint tNeg : ConnectedComponents D.CutSpace) =
          N.negativeArcIndex :=
      (mem_finiteArcInterior_iff_componentClass D
        (N.negativePoint tNeg) N.negativeArcIndex).mp htMem
    have hpoint : N.negativePoint tNeg = qCut := by
      apply Subtype.ext
      exact htPoint
    calc
      e.1 = (qCut : ConnectedComponents D.CutSpace) := hqClass.symm
      _ = (N.negativePoint tNeg : ConnectedComponents D.CutSpace) := by
        rw [hpoint]
      _ = N.negativeArcIndex := htClass
  · right
    have htBounds := (abs_lt.mp htSmall)
    let tPos : N.positiveParameters := ⟨t, htPos, htBounds.2⟩
    have htMem :
        (N.positivePoint tPos).1 ∈
          D.finiteArcInterior N.positiveArcIndex :=
      N.positivePoint_mem_finiteArcInterior tPos
    have htClass :
        (N.positivePoint tPos : ConnectedComponents D.CutSpace) =
          N.positiveArcIndex :=
      (mem_finiteArcInterior_iff_componentClass D
        (N.positivePoint tPos) N.positiveArcIndex).mp htMem
    have hpoint : N.positivePoint tPos = qCut := by
      apply Subtype.ext
      exact htPoint
    calc
      e.1 = (qCut : ConnectedComponents D.CutSpace) := hqClass.symm
      _ = (N.positivePoint tPos : ConnectedComponents D.CutSpace) := by
        rw [hpoint]
      _ = N.positiveArcIndex := htClass

/-- Closure incidence is exactly membership in one of the two chart-derived
local germ classes. -/
theorem cutPoint_mem_finiteArcClosure_iff_localGermArc
    (N : CutPointCoreNeighborhood D v) (e : D.ArcIndex) :
    v.1 ∈ D.finiteArcClosure e ↔
      e = N.negativeArcIndex ∨ e = N.positiveArcIndex := by
  constructor
  · intro he
    exact N.incidentArc_eq_negativeArcIndex_or_positiveArcIndex ⟨e, he⟩
  · rintro (rfl | rfl)
    · exact N.cutPoint_mem_negativeArcClosure
    · exact N.cutPoint_mem_positiveArcClosure

/-- A closed symmetric parameter interval strictly inside the cut-free local
core. -/
abbrev symmetricParameters (N : CutPointCoreNeighborhood D v) :=
  (Icc (-(N.radius / 2)) (N.radius / 2) : Set ℝ)

/-- A symmetric local parameter as a parameter of the actual compact core. -/
def symmetricCoreParameter (N : CutPointCoreNeighborhood D v)
    (t : N.symmetricParameters) :
    (A.intervalAt v.1).CoreParameter :=
  ⟨t.1, by
    have ht := t.2
    change -(N.radius / 2) ≤ (t : ℝ) ∧
      (t : ℝ) ≤ N.radius / 2 at ht
    constructor <;>
      linarith [ht.1, ht.2, N.radius_pos,
        N.radius_lt_coreRadius]⟩
/-- The actual frontier point represented by a symmetric local parameter. -/
def symmetricPoint (N : CutPointCoreNeighborhood D v)
    (t : N.symmetricParameters) : FrontierSpace O :=
  (A.intervalAt v.1).corePoint (N.symmetricCoreParameter t)

theorem continuous_symmetricPoint (N : CutPointCoreNeighborhood D v) :
    Continuous N.symmetricPoint := by
  apply (A.intervalAt v.1).continuous_corePoint.comp
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem injective_symmetricPoint (N : CutPointCoreNeighborhood D v) :
    Function.Injective N.symmetricPoint := by
  intro s t hst
  apply Subtype.ext
  have hcore :=
    (A.intervalAt v.1).injective_corePoint hst
  exact congrArg
    (fun x : (A.intervalAt v.1).CoreParameter => (x : ℝ)) hcore

theorem symmetricPoint_zero (N : CutPointCoreNeighborhood D v) :
    N.symmetricPoint
        ⟨0, by constructor <;> linarith [N.radius_pos]⟩ = v.1 := by
  have hcore :
      N.symmetricCoreParameter
          ⟨0, by constructor <;> linarith [N.radius_pos]⟩ =
        CutPointCoreNeighborhood.zeroCoreParameter D v := by
    apply Subtype.ext
    rfl
  rw [symmetricPoint, hcore,
    CutPointCoreNeighborhood.corePoint_zero D v]

/-- If the two local germs had the same quotient class, the entire small
symmetric local interval would lie in that one compact arc closure. -/
theorem symmetricPoint_mem_negativeArcClosure_of_germs_eq
    (N : CutPointCoreNeighborhood D v)
    (hGerms : N.negativeArcIndex = N.positiveArcIndex)
    (t : N.symmetricParameters) :
    N.symmetricPoint t ∈ D.finiteArcClosure N.negativeArcIndex := by
  by_cases htZero : (t : ℝ) = 0
  · have ht :
        t = ⟨0, by constructor <;> linarith [N.radius_pos]⟩ := by
      apply Subtype.ext
      exact htZero
    rw [ht, N.symmetricPoint_zero]
    exact N.cutPoint_mem_negativeArcClosure
  rcases lt_or_gt_of_ne htZero with htNeg | htPos
  · rw [finiteArcClosure]
    apply subset_closure
    have htBounds := t.2
    change -(N.radius / 2) ≤ (t : ℝ) ∧
      (t : ℝ) ≤ N.radius / 2 at htBounds
    let tNeg : N.negativeParameters :=
      ⟨N.symmetricCoreParameter t, by
        change -N.radius < (t : ℝ)
        linarith [htBounds.1, N.radius_pos], htNeg⟩
    simpa only [symmetricPoint, negativePoint, tNeg] using
      N.negativePoint_mem_finiteArcInterior tNeg
  · rw [finiteArcClosure]
    apply subset_closure
    have htBounds := t.2
    change -(N.radius / 2) ≤ (t : ℝ) ∧
      (t : ℝ) ≤ N.radius / 2 at htBounds
    let tPos : N.positiveParameters :=
      ⟨N.symmetricCoreParameter t, htPos, by
        change (t : ℝ) < N.radius
        linarith [htBounds.2, N.radius_pos]⟩
    have htMem :=
      N.positivePoint_mem_finiteArcInterior tPos
    rw [← hGerms] at htMem
    simpa only [symmetricPoint, positivePoint, tPos] using htMem

/-- The negative and positive local germs determine different compact arcs.
Otherwise an embedded closed-interval arc would contain a two-sided ambient
neighborhood of one of its endpoints. -/
theorem negativeArcIndex_ne_positiveArcIndex
    (N : CutPointCoreNeighborhood D v) :
    N.negativeArcIndex ≠ N.positiveArcIndex := by
  intro hGerms
  let e : D.ArcIndex := N.negativeArcIndex
  let i : D.centers := D.finiteArcChart e
  let x : D.CutSpace := D.arcRepresentative e
  have hx : x.1 ∈ (D.arc i).coreInterior := by
    exact D.arcRepresentative_mem_finiteArcChart_coreInterior e
  let H := D.cutComponentClosedArcHomeomorph i x
  let closedPoint : N.symmetricParameters →
      D.cutComponentClosedArc i x :=
    fun t => ⟨N.symmetricPoint t, by
      rw [← D.finiteArcClosure_eq_selectedClosedArc e]
      exact N.symmetricPoint_mem_negativeArcClosure_of_germs_eq
        hGerms t⟩
  have hclosedPoint : Continuous closedPoint := by
    apply Continuous.subtype_mk
    exact N.continuous_symmetricPoint
  let f : N.symmetricParameters →
      D.cutComponentClosedCoreParameterSet i x :=
    fun t => H.symm (closedPoint t)
  have hf : Continuous f := H.symm.continuous.comp hclosedPoint
  let phi : N.symmetricParameters → ℝ :=
    fun t => ((f t).1 : ℝ)
  have hphi : Continuous phi := by
    exact continuous_subtype_val.comp
      (continuous_subtype_val.comp hf)
  have hphiInjective : Function.Injective phi := by
    intro s t hst
    have hfst : f s = f t := by
      apply Subtype.ext
      apply Subtype.ext
      exact hst
    have hpoints : closedPoint s = closedPoint t := by
      calc
        closedPoint s = H (f s) := (H.apply_symm_apply _).symm
        _ = H (f t) := congrArg H hfst
        _ = closedPoint t := H.apply_symm_apply _
    have hsymmetric :
        N.symmetricPoint s = N.symmetricPoint t :=
      congrArg
        (fun q : D.cutComponentClosedArc i x =>
          (q : FrontierSpace O)) hpoints
    exact N.injective_symmetricPoint hsymmetric
  letI : Fact (-(N.radius / 2) ≤ N.radius / 2) :=
    ⟨by linarith [N.radius_pos]⟩
  rcases hphi.strictMono_of_inj_boundedOrder' hphiInjective with
    hmono | hanti
  · let tNeg : N.symmetricParameters :=
      ⟨-(N.radius / 2), by
        constructor
        · exact le_rfl
        · linarith [N.radius_pos]⟩
    let tZero : N.symmetricParameters :=
      ⟨0, by constructor <;> linarith [N.radius_pos]⟩
    have htNegZero : tNeg < tZero := by
      change -(N.radius / 2) < 0
      linarith [N.radius_pos]
    have hlt := hmono htNegZero
    have hbounds : sInf (D.cutComponentRealParameterImage i x) ≤
        phi tNeg := by
      exact (f tNeg).2.1
    have hvEndpoint :=
      (D.cutPoint_mem_finiteArcClosure_iff_endpoint v.2 e).mp
        N.cutPoint_mem_negativeArcClosure
    rcases hvEndpoint with hvLeft | hvRight
    · have hmap :
          (D.arc i).corePoint (f tZero).1 = v.1 := by
        change (H (f tZero)).1 = v.1
        rw [H.apply_symm_apply]
        exact N.symmetricPoint_zero
      have hparameter :=
        (D.arc i).injective_corePoint
          (hmap.trans hvLeft)
      have hreal := congrArg
        (fun z : (D.arc i).CoreParameter => (z : ℝ)) hparameter
      have hzero :
          phi tZero =
            sInf (D.cutComponentRealParameterImage i x) := by
        exact hreal
      linarith
    · have hmap :
          (D.arc i).corePoint (f tZero).1 = v.1 := by
        change (H (f tZero)).1 = v.1
        rw [H.apply_symm_apply]
        exact N.symmetricPoint_zero
      have hparameter :=
        (D.arc i).injective_corePoint
          (hmap.trans hvRight)
      have hreal := congrArg
        (fun z : (D.arc i).CoreParameter => (z : ℝ)) hparameter
      have hzero :
          phi tZero =
            sSup (D.cutComponentRealParameterImage i x) := by
        exact hreal
      let tPos : N.symmetricParameters :=
        ⟨N.radius / 2, by
          constructor
          · linarith [N.radius_pos]
          · exact le_rfl⟩
      have htZeroPos : tZero < tPos := by
        change 0 < N.radius / 2
        linarith [N.radius_pos]
      have hltPos := hmono htZeroPos
      have hupper : phi tPos ≤
          sSup (D.cutComponentRealParameterImage i x) :=
        (f tPos).2.2
      linarith
  · let tZero : N.symmetricParameters :=
      ⟨0, by constructor <;> linarith [N.radius_pos]⟩
    let tPos : N.symmetricParameters :=
      ⟨N.radius / 2, by
        constructor
        · linarith [N.radius_pos]
        · exact le_rfl⟩
    have htZeroPos : tZero < tPos := by
      change 0 < N.radius / 2
      linarith [N.radius_pos]
    have hlt := hanti htZeroPos
    have hlower : sInf (D.cutComponentRealParameterImage i x) ≤
        phi tPos := (f tPos).2.1
    have hvEndpoint :=
      (D.cutPoint_mem_finiteArcClosure_iff_endpoint v.2 e).mp
        N.cutPoint_mem_negativeArcClosure
    rcases hvEndpoint with hvLeft | hvRight
    · have hmap :
          (D.arc i).corePoint (f tZero).1 = v.1 := by
        change (H (f tZero)).1 = v.1
        rw [H.apply_symm_apply]
        exact N.symmetricPoint_zero
      have hparameter :=
        (D.arc i).injective_corePoint
          (hmap.trans hvLeft)
      have hreal := congrArg
        (fun z : (D.arc i).CoreParameter => (z : ℝ)) hparameter
      have hzero :
          phi tZero =
            sInf (D.cutComponentRealParameterImage i x) := by
        exact hreal
      linarith
    · have hmap :
          (D.arc i).corePoint (f tZero).1 = v.1 := by
        change (H (f tZero)).1 = v.1
        rw [H.apply_symm_apply]
        exact N.symmetricPoint_zero
      have hparameter :=
        (D.arc i).injective_corePoint
          (hmap.trans hvRight)
      have hreal := congrArg
        (fun z : (D.arc i).CoreParameter => (z : ℝ)) hparameter
      have hzero :
          phi tZero =
            sSup (D.cutComponentRealParameterImage i x) := by
        exact hreal
      let tNeg : N.symmetricParameters :=
        ⟨-(N.radius / 2), by
          constructor
          · exact le_rfl
          · linarith [N.radius_pos]⟩
      have htNegZero : tNeg < tZero := by
        change -(N.radius / 2) < 0
        linarith [N.radius_pos]
      have hltNeg := hanti htNegZero
      have hupper : phi tNeg ≤
          sSup (D.cutComponentRealParameterImage i x) :=
        (f tNeg).2.2
      linarith

/-- The two local germs enumerate every arc incident to the cut point. -/
noncomputable def incidentArcOfBool
    (N : CutPointCoreNeighborhood D v) : Bool → D.IncidentArc v
  | false => ⟨N.negativeArcIndex, N.cutPoint_mem_negativeArcClosure⟩
  | true => ⟨N.positiveArcIndex, N.cutPoint_mem_positiveArcClosure⟩

theorem incidentArcOfBool_surjective
    (N : CutPointCoreNeighborhood D v) :
    Function.Surjective N.incidentArcOfBool := by
  intro e
  rcases N.incidentArc_eq_negativeArcIndex_or_positiveArcIndex e with
    he | he
  · refine ⟨false, ?_⟩
    apply Subtype.ext
    exact he.symm
  · refine ⟨true, ?_⟩
    apply Subtype.ext
    exact he.symm

/-- Derived finite-graph degree bound: every actual cut vertex is incident to
at most two quotient-indexed compact arcs. -/
theorem incidentArc_natCard_le_two
    (N : CutPointCoreNeighborhood D v) :
    Nat.card (D.IncidentArc v) ≤ 2 := by
  letI : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  letI : Fintype (D.IncidentArc v) := Fintype.ofFinite _
  simpa using Fintype.card_le_of_surjective N.incidentArcOfBool
    N.incidentArcOfBool_surjective

theorem incidentArcOfBool_injective
    (N : CutPointCoreNeighborhood D v) :
    Function.Injective N.incidentArcOfBool := by
  intro b c hbc
  cases b <;> cases c
  · rfl
  · exfalso
    exact N.negativeArcIndex_ne_positiveArcIndex
      (congrArg Subtype.val hbc)
  · exfalso
    exact N.negativeArcIndex_ne_positiveArcIndex
      (congrArg Subtype.val hbc).symm
  · rfl

/-- The two actual local chart germs are equivalent to the full finite type of
arcs incident to the cut point. -/
noncomputable def incidentArcEquivBool
    (N : CutPointCoreNeighborhood D v) :
    Bool ≃ D.IncidentArc v :=
  Equiv.ofBijective N.incidentArcOfBool
    ⟨N.incidentArcOfBool_injective, N.incidentArcOfBool_surjective⟩

/-- Every actual cut vertex in the derived compact-arc graph has degree exactly
two. -/
theorem incidentArc_natCard_eq_two
    (N : CutPointCoreNeighborhood D v) :
    Nat.card (D.IncidentArc v) = 2 := by
  letI : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  letI : Fintype (D.IncidentArc v) := Fintype.ofFinite _
  simpa using (Fintype.card_congr N.incidentArcEquivBool).symm

/-- Exchange the two actual arcs incident to the cut point. -/
noncomputable def otherIncidentArc
    (N : CutPointCoreNeighborhood D v) :
    Equiv.Perm (D.IncidentArc v) :=
  N.incidentArcEquivBool.symm.trans
    (Equiv.boolNot.trans N.incidentArcEquivBool)

theorem otherIncidentArc_ne
    (N : CutPointCoreNeighborhood D v) (e : D.IncidentArc v) :
    N.otherIncidentArc e ≠ e := by
  intro he
  have heBool :=
    congrArg N.incidentArcEquivBool.symm he
  simp only [otherIncidentArc, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.boolNot_apply,
    Equiv.symm_apply_apply] at heBool
  generalize N.incidentArcEquivBool.symm e = b at heBool
  cases b <;> simp at heBool

@[simp] theorem otherIncidentArc_otherIncidentArc
    (N : CutPointCoreNeighborhood D v) (e : D.IncidentArc v) :
    N.otherIncidentArc (N.otherIncidentArc e) = e := by
  simp only [otherIncidentArc, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.boolNot_apply, Bool.not_not,
    Equiv.symm_apply_apply]

end CutPointCoreNeighborhood

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
