/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundarySourceTraceAdapter
import CMVBoundaryGraphAtlas
import CMVBoundaryLocalAtlasSpecimen

/-!
# Height-completion specimens

The independently defined Euclidean disk and the literal nonconvex shelf
polygon instantiate the same intrinsic height-support and section-endpoint
producer.  The shelf application also records its genuine unequal one-sided
right-endpoint limits and its complete jump slice.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

open CMVRelaxation
open CMVSourceClassification
open SelectedBoundaryTopologyInput

namespace UnitDisk

open CMVFigureFour
open CMVFigureFour.FiniteCrossingExample

/-- The independently defined open unit disk is regular open. -/
theorem interior_closure_openUnitDisk :
    interior (closure openUnitDisk) = openUnitDisk := by
  change interior (closure CMVRelaxation.unitDisk) = CMVRelaxation.unitDisk
  rw [CMVRelaxation.unitDisk_eq_preimage_ball,
    ← planeEuclideanHomeomorph.preimage_closure,
    closure_ball (0 : EuclideanPlane) one_ne_zero,
    ← planeEuclideanHomeomorph.preimage_interior,
    interior_closedBall (0 : EuclideanPlane) one_ne_zero]

/-- The selected almost-everywhere representative fixes the disk exactly. -/
theorem aeOpenRepresentative_openUnitDisk :
    aeOpenRepresentative openUnitDisk = openUnitDisk := by
  apply Set.Subset.antisymm
  · have hsubset : aeOpenRepresentative openUnitDisk ⊆
        interior (closure openUnitDisk) :=
      interior_maximal
        (aeOpenRepresentative_subset_closure_self openUnitDisk)
        (isOpen_aeOpenRepresentative openUnitDisk)
    simpa only [interior_closure_openUnitDisk] using hsubset
  · exact open_subset_aeOpenRepresentative_self isOpen_openUnitDisk

/-- The disk is connected, derived from the Euclidean ball model. -/
theorem isConnected_openUnitDisk : IsConnected openUnitDisk := by
  change IsConnected CMVRelaxation.unitDisk
  rw [CMVRelaxation.unitDisk_eq_preimage_ball,
    planeEuclideanHomeomorph.isConnected_preimage]
  exact Metric.isConnected_ball (by norm_num)

/-- Every literal disk section is order connected. -/
theorem ordConnected_horizontalSection_openUnitDisk (y : ℝ) :
    (CMVSourceClassification.horizontalSection openUnitDisk y).OrdConnected := by
  rw [Set.ordConnected_iff_uIcc_subset]
  intro x hx z hz w hw
  change x ^ 2 + y ^ 2 < 1 at hx
  change z ^ 2 + y ^ 2 < 1 at hz
  change w ^ 2 + y ^ 2 < 1
  rcases Set.mem_uIcc.mp hw with hw | hw
  · by_cases hw0 : 0 ≤ w
    · have hz0 : 0 ≤ z := hw0.trans hw.2
      have hsq : w ^ 2 ≤ z ^ 2 := (sq_le_sq₀ hw0 hz0).2 hw.2
      linarith
    · have hwneg : w ≤ 0 := le_of_not_ge hw0
      have hxneg : x ≤ 0 := hw.1.trans hwneg
      have habs : |w| ≤ |x| := by
        rw [abs_of_nonpos hwneg, abs_of_nonpos hxneg]
        linarith
      have hsq : w ^ 2 ≤ x ^ 2 := (sq_le_sq).2 habs
      linarith
  · by_cases hw0 : 0 ≤ w
    · have hx0 : 0 ≤ x := hw0.trans hw.2
      have hsq : w ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hw0 hx0).2 hw.2
      linarith
    · have hwneg : w ≤ 0 := le_of_not_ge hw0
      have hzneg : z ≤ 0 := hw.1.trans hwneg
      have habs : |w| ≤ |z| := by
        rw [abs_of_nonpos hwneg, abs_of_nonpos hzneg]
        linarith
      have hsq : w ^ 2 ≤ z ^ 2 := (sq_le_sq).2 habs
      linarith

/-- The required AE interval-section hypothesis is proved from the disk
inequality, not supplied as a section formula. -/
theorem hasAEIntervalHorizontalSections_openUnitDisk :
    HasAEIntervalHorizontalSections openUnitDisk := by
  filter_upwards [] with y
  exact ⟨CMVSourceClassification.horizontalSection openUnitDisk y,
    ordConnected_horizontalSection_openUnitDisk y,
    Filter.EventuallyEq.rfl⟩

/-- The disk's actual atlas transported to its exactly selected representative. -/
noncomputable def selectedBoundaryAtlas :
    BoundaryHalfSpaceAtlas (aeOpenRepresentative openUnitDisk) := by
  rw [aeOpenRepresentative_openUnitDisk]
  exact boundaryAtlas

/-- The disk instantiates the unchanged topology input. -/
noncomputable def selectedTopologyInput :
    SelectedBoundaryTopologyInput openUnitDisk openUnitDisk where
  representative_nonempty := ⟨(0, 0), by norm_num [openUnitDisk]⟩
  representative_open := isOpen_openUnitDisk
  representative_bounded := isBounded_openUnitDisk
  representative_connected := isConnected_openUnitDisk
  carrier_ae := Filter.Eventually.of_forall (fun _ => rfl)
  interval_sections := hasAEIntervalHorizontalSections_openUnitDisk
  local_atlas := selectedBoundaryAtlas

/-- The intrinsic occupied-height producer recovers the exact disk band. -/
theorem occupiedHeights_eq :
    selectedTopologyInput.occupiedHeights = Ioo (-1 : ℝ) 1 := by
  unfold SelectedBoundaryTopologyInput.occupiedHeights
  rw [aeOpenRepresentative_openUnitDisk]
  ext y
  constructor
  · rintro ⟨⟨x, z⟩, hz, rfl⟩
    change x ^ 2 + z ^ 2 < 1 at hz
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg (z - 1),
      sq_nonneg (z + 1)]
  · intro hy
    refine ⟨(0, y), ?_, rfl⟩
    change 0 ^ 2 + y ^ 2 < 1
    nlinarith [mul_pos (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)]

@[simp] theorem lowerHeight_eq : selectedTopologyInput.lowerHeight = -1 := by
  rw [SelectedBoundaryTopologyInput.lowerHeight, occupiedHeights_eq]
  norm_num

@[simp] theorem upperHeight_eq : selectedTopologyInput.upperHeight = 1 := by
  rw [SelectedBoundaryTopologyInput.upperHeight, occupiedHeights_eq]
  norm_num

@[simp] theorem leftEndpoint_zero :
    selectedTopologyInput.leftEndpoint 0 = -1 := by
  rw [SelectedBoundaryTopologyInput.leftEndpoint,
    aeOpenRepresentative_openUnitDisk, horizontalSection_openUnitDisk_zero]
  norm_num

@[simp] theorem rightEndpoint_zero :
    selectedTopologyInput.rightEndpoint 0 = 1 := by
  rw [SelectedBoundaryTopologyInput.rightEndpoint,
    aeOpenRepresentative_openUnitDisk, horizontalSection_openUnitDisk_zero]
  norm_num

/-- The generic producer places the concrete disk endpoints on its actual
frontier. -/
theorem zero_endpoints_mem_frontier :
    ((-1, 0) : PlanePoint) ∈ frontier openUnitDisk ∧
      ((1, 0) : PlanePoint) ∈ frontier openUnitDisk := by
  have hzero : (0 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  simpa only [aeOpenRepresentative_openUnitDisk, leftEndpoint_zero,
    rightEndpoint_zero] using
    And.intro (selectedTopologyInput.leftEndpoint_mem_frontier hzero)
      (selectedTopologyInput.rightEndpoint_mem_frontier hzero)

/-- The generic regulation theorem supplies all four finite endpoint limits at
the disk's middle height. -/
theorem endpointLimits_zero :
    (∃ L, Tendsto selectedTopologyInput.leftEndpoint (𝓝[<] (0 : ℝ)) (𝓝 L)) ∧
    (∃ L, Tendsto selectedTopologyInput.leftEndpoint (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    (∃ R, Tendsto selectedTopologyInput.rightEndpoint (𝓝[<] (0 : ℝ)) (𝓝 R)) ∧
    (∃ R, Tendsto selectedTopologyInput.rightEndpoint (𝓝[>] (0 : ℝ)) (𝓝 R)) := by
  have hzero : (0 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  exact ⟨selectedTopologyInput.exists_leftEndpoint_limit_nhdsLT hzero,
    selectedTopologyInput.exists_leftEndpoint_limit_nhdsGT hzero,
    selectedTopologyInput.exists_rightEndpoint_limit_nhdsLT hzero,
    selectedTopologyInput.exists_rightEndpoint_limit_nhdsGT hzero⟩

/-- The generic extreme-slice formulas apply to the two disk poles. -/
theorem extreme_frontierSections_eq_endpointLimits :
    selectedTopologyInput.frontierSection (-1) =
        Icc (Function.rightLim selectedTopologyInput.leftEndpoint (-1))
          (Function.rightLim selectedTopologyInput.rightEndpoint (-1)) ∧
      selectedTopologyInput.frontierSection 1 =
        Icc (Function.leftLim selectedTopologyInput.leftEndpoint 1)
          (Function.leftLim selectedTopologyInput.rightEndpoint 1) := by
  simpa only [lowerHeight_eq, upperHeight_eq] using
    And.intro selectedTopologyInput.lower_frontierSection_eq_Icc_endpointLimits
      selectedTopologyInput.upper_frontierSection_eq_Icc_endpointLimits

/-- The two intrinsic completed chains recover the actual disk frontier. -/
theorem frontier_eq_union_completedChains :
    frontier openUnitDisk =
      selectedTopologyInput.leftCompletedChain ∪
        selectedTopologyInput.rightCompletedChain := by
  simpa only [aeOpenRepresentative_openUnitDisk] using
    selectedTopologyInput.frontier_eq_union_completedChains

/-- Both completed disk chains are actual compact subsets of the plane. -/
theorem completedChains_compact :
    IsCompact selectedTopologyInput.leftCompletedChain ∧
      IsCompact selectedTopologyInput.rightCompletedChain :=
  ⟨selectedTopologyInput.isCompact_leftCompletedChain,
    selectedTopologyInput.isCompact_rightCompletedChain⟩

/-- The disk's completed chains share exactly their intrinsic bottom and top
split points. -/
theorem completedChains_inter_eq_splitPoints :
    selectedTopologyInput.leftCompletedChain ∩
        selectedTopologyInput.rightCompletedChain =
      {selectedTopologyInput.lowerSplitPoint,
        selectedTopologyInput.upperSplitPoint} :=
  selectedTopologyInput.completedChains_inter_eq

theorem completedChain_splitPoints_distinct :
    selectedTopologyInput.lowerSplitPoint ≠
      selectedTopologyInput.upperSplitPoint :=
  selectedTopologyInput.lowerSplitPoint_ne_upperSplitPoint

/-- The disk's two intrinsic traversals have no adjacent points and retain
separable planar-subspace carriers. -/
theorem completedChain_intrinsic_order_data :
    @DenselyOrdered selectedTopologyInput.leftCompletedChain
        selectedTopologyInput.leftCompletedChainLinearOrder.toLT ∧
      @DenselyOrdered selectedTopologyInput.rightCompletedChain
        selectedTopologyInput.rightCompletedChainLinearOrder.toLT ∧
      TopologicalSpace.SeparableSpace
        selectedTopologyInput.leftCompletedChain ∧
      TopologicalSpace.SeparableSpace
        selectedTopologyInput.rightCompletedChain := by
  exact ⟨selectedTopologyInput.leftCompletedChain_denselyOrdered,
    selectedTopologyInput.rightCompletedChain_denselyOrdered,
    selectedTopologyInput.leftCompletedChain_separableSpace,
    selectedTopologyInput.rightCompletedChain_separableSpace⟩

/-- The disk's lower and upper split points are the extrema of both intrinsic
traversal orders. -/
theorem completedChain_order_extrema :
    letI : LE selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder.toLE
    letI : LT selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder.toLT
    letI : LinearOrder selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder
    letI : OrderBot selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainOrderBot
    letI : OrderTop selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainOrderTop
    letI : LE selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder.toLE
    letI : LT selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder.toLT
    letI : LinearOrder selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder
    letI : OrderBot selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainOrderBot
    letI : OrderTop selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainOrderTop
    (((⊥ : selectedTopologyInput.leftCompletedChain) : PlanePoint) =
        selectedTopologyInput.lowerSplitPoint) ∧
      (((⊤ : selectedTopologyInput.leftCompletedChain) : PlanePoint) =
        selectedTopologyInput.upperSplitPoint) ∧
      (((⊥ : selectedTopologyInput.rightCompletedChain) : PlanePoint) =
        selectedTopologyInput.lowerSplitPoint) ∧
      (((⊤ : selectedTopologyInput.rightCompletedChain) : PlanePoint) =
        selectedTopologyInput.upperSplitPoint) := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-- The disk's inherited planar topologies are exactly the two height-first
order topologies. -/
theorem completedChain_topology_agreement :
    (inferInstance :
        TopologicalSpace selectedTopologyInput.leftCompletedChain) =
        @Preorder.topology selectedTopologyInput.leftCompletedChain
          selectedTopologyInput.leftCompletedChainLinearOrder.toPreorder ∧
      (inferInstance :
        TopologicalSpace selectedTopologyInput.rightCompletedChain) =
        @Preorder.topology selectedTopologyInput.rightCompletedChain
          selectedTopologyInput.rightCompletedChainLinearOrder.toPreorder :=
  ⟨selectedTopologyInput.leftCompletedChain_topology_eq_orderTopology,
    selectedTopologyInput.rightCompletedChain_topology_eq_orderTopology⟩

noncomputable abbrev leftCompletedChainCompleteOrder :
    CompleteLinearOrder selectedTopologyInput.leftCompletedChain :=
  selectedTopologyInput.leftCompletedChainCompleteLinearOrder

noncomputable abbrev rightCompletedChainCompleteOrder :
    CompleteLinearOrder selectedTopologyInput.rightCompletedChain :=
  selectedTopologyInput.rightCompletedChainCompleteLinearOrder

/-- The disk's actual completed left chain uses the generic closed-unit-interval
parameterization. -/
noncomputable def leftCompletedChainParameterization :
    Set.Icc (0 : ℝ) 1 ≃ₜ selectedTopologyInput.leftCompletedChain :=
  selectedTopologyInput.leftCompletedChainHomeomorph

/-- The disk's actual completed right chain uses the same generic producer. -/
noncomputable def rightCompletedChainParameterization :
    Set.Icc (0 : ℝ) 1 ≃ₜ selectedTopologyInput.rightCompletedChain :=
  selectedTopologyInput.rightCompletedChainHomeomorph

/-- Both disk parameterizations preserve the intrinsic lower and upper split
points. -/
theorem completedChainParameterizations_endpoints :
    ((leftCompletedChainParameterization ⟨0, by norm_num⟩ :
        selectedTopologyInput.leftCompletedChain) : PlanePoint) =
          selectedTopologyInput.lowerSplitPoint ∧
      ((leftCompletedChainParameterization ⟨1, by norm_num⟩ :
        selectedTopologyInput.leftCompletedChain) : PlanePoint) =
          selectedTopologyInput.upperSplitPoint ∧
      ((rightCompletedChainParameterization ⟨0, by norm_num⟩ :
        selectedTopologyInput.rightCompletedChain) : PlanePoint) =
          selectedTopologyInput.lowerSplitPoint ∧
      ((rightCompletedChainParameterization ⟨1, by norm_num⟩ :
        selectedTopologyInput.rightCompletedChain) : PlanePoint) =
          selectedTopologyInput.upperSplitPoint := by
  exact ⟨selectedTopologyInput.leftCompletedChainHomeomorph_zero,
    selectedTopologyInput.leftCompletedChainHomeomorph_one,
    selectedTopologyInput.rightCompletedChainHomeomorph_zero,
    selectedTopologyInput.rightCompletedChainHomeomorph_one⟩

/-- The two disk parameterizations are onto the two actual completed planar
chains, not merely abstract copies. -/
theorem completedChainParameterizations_ranges :
    range (fun t => ((leftCompletedChainParameterization t :
      selectedTopologyInput.leftCompletedChain) : PlanePoint)) =
        selectedTopologyInput.leftCompletedChain ∧
      range (fun t => ((rightCompletedChainParameterization t :
        selectedTopologyInput.rightCompletedChain) : PlanePoint)) =
          selectedTopologyInput.rightCompletedChain :=
  ⟨selectedTopologyInput.range_leftCompletedChainHomeomorph,
    selectedTopologyInput.range_rightCompletedChainHomeomorph⟩

/-- The disk's complete frontier loop is the generic concatenation of its two
actual completed chains. -/
noncomputable def simpleBoundaryLoop : ℝ → PlanePoint :=
  selectedTopologyInput.completedBoundaryLoop

theorem continuous_simpleBoundaryLoop : Continuous simpleBoundaryLoop :=
  selectedTopologyInput.continuous_completedBoundaryLoop

theorem simpleBoundaryLoop_closed :
    simpleBoundaryLoop 0 = simpleBoundaryLoop 2 :=
  selectedTopologyInput.completedBoundaryLoop_closed

theorem simpleBoundaryLoop_injOn_Ico :
    Set.InjOn simpleBoundaryLoop (Set.Ico (0 : ℝ) 2) :=
  selectedTopologyInput.completedBoundaryLoop_injOn_Ico

theorem simpleBoundaryLoop_image :
    simpleBoundaryLoop '' Set.Icc (0 : ℝ) 2 = frontier openUnitDisk := by
  simpa only [simpleBoundaryLoop, aeOpenRepresentative_openUnitDisk] using
    selectedTopologyInput.image_completedBoundaryLoop_Icc

theorem frontier_connected_from_simpleBoundaryLoop :
    IsConnected (frontier openUnitDisk) := by
  simpa only [aeOpenRepresentative_openUnitDisk] using
    selectedTopologyInput.isConnected_frontier_aeOpenRepresentative

end UnitDisk

namespace StepPolygon

/-- The intrinsic occupied-height producer recovers the complete shelf band. -/
theorem occupiedHeights_eq :
    selectedTopologyInput.occupiedHeights = Ioo (0 : ℝ) 2 := by
  unfold SelectedBoundaryTopologyInput.occupiedHeights
  rw [aeOpenRepresentative_carrier]
  ext y
  constructor
  · rintro ⟨⟨x, z⟩, hz, rfl⟩
    rw [mem_carrier] at hz
    rcases hz with hz | hz
    · exact ⟨hz.2.2.1, hz.2.2.2.trans (by norm_num)⟩
    · exact ⟨hz.2.2.1, hz.2.2.2⟩
  · intro hy
    refine ⟨((1 / 2 : ℝ), y), ?_, rfl⟩
    rw [mem_carrier]
    by_cases hy1 : y < 1
    · exact Or.inl ⟨by norm_num, by norm_num, hy.1, hy1⟩
    · exact Or.inr ⟨by norm_num, by norm_num, hy.1, hy.2⟩

@[simp] theorem lowerHeight_eq : selectedTopologyInput.lowerHeight = 0 := by
  rw [SelectedBoundaryTopologyInput.lowerHeight, occupiedHeights_eq]
  norm_num

@[simp] theorem upperHeight_eq : selectedTopologyInput.upperHeight = 2 := by
  rw [SelectedBoundaryTopologyInput.upperHeight, occupiedHeights_eq]
  norm_num

/-- The left endpoint is fixed along the entire occupied band. -/
theorem leftEndpoint_eq_zero {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 2) :
    selectedTopologyInput.leftEndpoint y = 0 := by
  rw [SelectedBoundaryTopologyInput.leftEndpoint,
    aeOpenRepresentative_carrier]
  by_cases hy1 : y < 1
  · rw [horizontalSection_eq_wide ⟨hy.1, hy1⟩]
    norm_num
  · rw [horizontalSection_eq_narrow hy.1 (le_of_not_gt hy1) hy.2]
    norm_num

/-- Below the shelf the right endpoint is two. -/
theorem rightEndpoint_eq_two {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    selectedTopologyInput.rightEndpoint y = 2 := by
  rw [SelectedBoundaryTopologyInput.rightEndpoint,
    aeOpenRepresentative_carrier,
    horizontalSection_eq_wide ⟨hy0, hy1⟩]
  norm_num

/-- At and above the shelf the right endpoint is one. -/
theorem rightEndpoint_eq_one {y : ℝ}
    (hy0 : 0 < y) (hy1 : 1 ≤ y) (hy2 : y < 2) :
    selectedTopologyInput.rightEndpoint y = 1 := by
  rw [SelectedBoundaryTopologyInput.rightEndpoint,
    aeOpenRepresentative_carrier,
    horizontalSection_eq_narrow hy0 hy1 hy2]
  norm_num

/-- Genuine lower-side convergence of the discontinuous shelf endpoint. -/
theorem tendsto_rightEndpoint_nhdsLT_one :
    Tendsto selectedTopologyInput.rightEndpoint (𝓝[<] (1 : ℝ)) (𝓝 2) := by
  have hpos : Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    isOpen_Ioi.mem_nhds (by norm_num)
  have heq : selectedTopologyInput.rightEndpoint =ᶠ[𝓝[<] (1 : ℝ)]
      fun _ => (2 : ℝ) := by
    filter_upwards [Filter.Eventually.filter_mono inf_le_left hpos,
      self_mem_nhdsWithin] with y hy0 hy1
    exact rightEndpoint_eq_two hy0 hy1
  exact tendsto_const_nhds.congr' heq.symm

/-- Genuine upper-side convergence of the discontinuous shelf endpoint. -/
theorem tendsto_rightEndpoint_nhdsGT_one :
    Tendsto selectedTopologyInput.rightEndpoint (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have htwo : Iio (2 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    isOpen_Iio.mem_nhds (by norm_num)
  have heq : selectedTopologyInput.rightEndpoint =ᶠ[𝓝[>] (1 : ℝ)]
      fun _ => (1 : ℝ) := by
    filter_upwards [Filter.Eventually.filter_mono inf_le_left htwo,
      self_mem_nhdsWithin] with y hy2 hy1
    change y < 2 at hy2
    change 1 < y at hy1
    exact rightEndpoint_eq_one (by linarith) hy1.le hy2
  exact tendsto_const_nhds.congr' heq.symm

/-- The generic canonical lower-side limit agrees with the direct shelf
calculation. -/
theorem rightEndpoint_leftLim_one :
    Function.leftLim selectedTopologyInput.rightEndpoint 1 = 2 := by
  have hy : (1 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  exact tendsto_nhds_unique
    (selectedTopologyInput.tendsto_rightEndpoint_nhdsLT_leftLim hy)
    tendsto_rightEndpoint_nhdsLT_one

/-- The generic jump-completion theorem recovers the shelf's entire right
frontier segment from its endpoint limit. -/
theorem generic_right_jump_segment_one :
    Icc (1 : ℝ) 2 ⊆ selectedTopologyInput.frontierSection 1 := by
  have hy : (1 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  have hendpoint : selectedTopologyInput.rightEndpoint 1 = 1 :=
    rightEndpoint_eq_one (by norm_num) (by norm_num) (by norm_num)
  simpa only [hendpoint, rightEndpoint_leftLim_one] using
    selectedTopologyInput.Icc_rightEndpoint_leftLim_subset_frontierSection hy

/-- The canonical upper-side limit of the shelf endpoint is its directly
computed value one. -/
theorem rightEndpoint_rightLim_one :
    Function.rightLim selectedTopologyInput.rightEndpoint 1 = 1 := by
  have hy : (1 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  exact tendsto_nhds_unique
    (selectedTopologyInput.tendsto_rightEndpoint_nhdsGT_rightLim hy)
    tendsto_rightEndpoint_nhdsGT_one

/-- The complete reentrant shelf is assigned to the right oriented chain,
including both endpoint values. -/
theorem shelf_subset_rightCompletedChain :
    (fun x : ℝ => (x, 1)) '' Icc 1 2 ⊆
      selectedTopologyInput.rightCompletedChain := by
  rintro _ ⟨x, hx, rfl⟩
  apply Or.inr
  apply Or.inl
  have hy : (1 : ℝ) ∈ selectedTopologyInput.occupiedHeights := by
    rw [occupiedHeights_eq]
    norm_num
  refine ⟨hy, ?_⟩
  rw [rightEndpoint_leftLim_one, rightEndpoint_rightLim_one]
  simpa [uIcc] using hx

/-- The intrinsic right-chain order traverses the shelf jump from its
lower-side value `2` to its upper-side value `1`. -/
theorem shelf_jump_order {x z : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    (hz : z ∈ Icc (1 : ℝ) 2) (hxz : x < z) :
    @LT.lt _ selectedTopologyInput.rightCompletedChainLinearOrder.toLT
      ⟨(z, 1), shelf_subset_rightCompletedChain ⟨z, hz, rfl⟩⟩
      ⟨(x, 1), shelf_subset_rightCompletedChain ⟨x, hx, rfl⟩⟩ := by
  apply selectedTopologyInput.rightCompletedChain_lt_of_same_snd_of_backward
  · rfl
  · rw [occupiedHeights_eq]
    norm_num
  · rw [rightEndpoint_leftLim_one, rightEndpoint_rightLim_one]
    norm_num
  · exact hxz

/-- The shelf-height frontier slice retains both the ordinary left endpoint and
the complete horizontal endpoint-jump segment. -/
theorem frontierSection_one :
    selectedTopologyInput.frontierSection 1 =
      ({0} : Set ℝ) ∪ Icc 1 2 := by
  rw [SelectedBoundaryTopologyInput.frontierSection,
    aeOpenRepresentative_carrier, frontier_carrier]
  ext x
  norm_num [boundary]
  constructor <;> aesop

/-- The bottom extreme slice is the full compact width-two interval. -/
theorem lower_frontierSection :
    selectedTopologyInput.frontierSection selectedTopologyInput.lowerHeight =
      Icc (0 : ℝ) 2 := by
  rw [lowerHeight_eq, SelectedBoundaryTopologyInput.frontierSection,
    aeOpenRepresentative_carrier, frontier_carrier]
  ext x
  norm_num [boundary]
  constructor <;> aesop

/-- The top extreme slice is the full compact width-one interval. -/
theorem upper_frontierSection :
    selectedTopologyInput.frontierSection selectedTopologyInput.upperHeight =
      Icc (0 : ℝ) 1 := by
  rw [upperHeight_eq, SelectedBoundaryTopologyInput.frontierSection,
    aeOpenRepresentative_carrier, frontier_carrier]
  ext x
  norm_num [boundary]
  constructor <;> aesop

/-- The two intrinsic completed chains recover the actual nonconvex shelf
frontier, without deleting its reentrant jump segment. -/
theorem frontier_eq_union_completedChains :
    frontier carrier =
      selectedTopologyInput.leftCompletedChain ∪
        selectedTopologyInput.rightCompletedChain := by
  simpa only [aeOpenRepresentative_carrier] using
    selectedTopologyInput.frontier_eq_union_completedChains

/-- Both completed shelf chains are actual compact subsets of the plane. -/
theorem completedChains_compact :
    IsCompact selectedTopologyInput.leftCompletedChain ∧
      IsCompact selectedTopologyInput.rightCompletedChain :=
  ⟨selectedTopologyInput.isCompact_leftCompletedChain,
    selectedTopologyInput.isCompact_rightCompletedChain⟩

/-- The shelf's completed chains share exactly their intrinsic bottom and top
split points. -/
theorem completedChains_inter_eq_splitPoints :
    selectedTopologyInput.leftCompletedChain ∩
        selectedTopologyInput.rightCompletedChain =
      {selectedTopologyInput.lowerSplitPoint,
        selectedTopologyInput.upperSplitPoint} :=
  selectedTopologyInput.completedChains_inter_eq

theorem completedChain_splitPoints_distinct :
    selectedTopologyInput.lowerSplitPoint ≠
      selectedTopologyInput.upperSplitPoint :=
  selectedTopologyInput.lowerSplitPoint_ne_upperSplitPoint

/-- The discontinuous shelf has no adjacent points in either intrinsic
traversal order, including across its reentrant horizontal segment. -/
theorem completedChain_intrinsic_order_data :
    @DenselyOrdered selectedTopologyInput.leftCompletedChain
        selectedTopologyInput.leftCompletedChainLinearOrder.toLT ∧
      @DenselyOrdered selectedTopologyInput.rightCompletedChain
        selectedTopologyInput.rightCompletedChainLinearOrder.toLT ∧
      TopologicalSpace.SeparableSpace
        selectedTopologyInput.leftCompletedChain ∧
      TopologicalSpace.SeparableSpace
        selectedTopologyInput.rightCompletedChain := by
  exact ⟨selectedTopologyInput.leftCompletedChain_denselyOrdered,
    selectedTopologyInput.rightCompletedChain_denselyOrdered,
    selectedTopologyInput.leftCompletedChain_separableSpace,
    selectedTopologyInput.rightCompletedChain_separableSpace⟩

/-- The shelf's lower and upper split points are the extrema of both intrinsic
traversal orders. -/
theorem completedChain_order_extrema :
    letI : LE selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder.toLE
    letI : LT selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder.toLT
    letI : LinearOrder selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainLinearOrder
    letI : OrderBot selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainOrderBot
    letI : OrderTop selectedTopologyInput.leftCompletedChain :=
      selectedTopologyInput.leftCompletedChainOrderTop
    letI : LE selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder.toLE
    letI : LT selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder.toLT
    letI : LinearOrder selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainLinearOrder
    letI : OrderBot selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainOrderBot
    letI : OrderTop selectedTopologyInput.rightCompletedChain :=
      selectedTopologyInput.rightCompletedChainOrderTop
    (((⊥ : selectedTopologyInput.leftCompletedChain) : PlanePoint) =
        selectedTopologyInput.lowerSplitPoint) ∧
      (((⊤ : selectedTopologyInput.leftCompletedChain) : PlanePoint) =
        selectedTopologyInput.upperSplitPoint) ∧
      (((⊥ : selectedTopologyInput.rightCompletedChain) : PlanePoint) =
        selectedTopologyInput.lowerSplitPoint) ∧
      (((⊤ : selectedTopologyInput.rightCompletedChain) : PlanePoint) =
        selectedTopologyInput.upperSplitPoint) := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-- The discontinuous shelf's planar chain topologies still agree exactly with
the height-first orders across the reentrant jump. -/
theorem completedChain_topology_agreement :
    (inferInstance :
        TopologicalSpace selectedTopologyInput.leftCompletedChain) =
        @Preorder.topology selectedTopologyInput.leftCompletedChain
          selectedTopologyInput.leftCompletedChainLinearOrder.toPreorder ∧
      (inferInstance :
        TopologicalSpace selectedTopologyInput.rightCompletedChain) =
        @Preorder.topology selectedTopologyInput.rightCompletedChain
          selectedTopologyInput.rightCompletedChainLinearOrder.toPreorder :=
  ⟨selectedTopologyInput.leftCompletedChain_topology_eq_orderTopology,
    selectedTopologyInput.rightCompletedChain_topology_eq_orderTopology⟩

noncomputable abbrev leftCompletedChainCompleteOrder :
    CompleteLinearOrder selectedTopologyInput.leftCompletedChain :=
  selectedTopologyInput.leftCompletedChainCompleteLinearOrder

noncomputable abbrev rightCompletedChainCompleteOrder :
    CompleteLinearOrder selectedTopologyInput.rightCompletedChain :=
  selectedTopologyInput.rightCompletedChainCompleteLinearOrder

/-- The discontinuous shelf's completed left chain is parameterized by the
same generic closed-unit-interval producer as the disk. -/
noncomputable def leftCompletedChainParameterization :
    Set.Icc (0 : ℝ) 1 ≃ₜ selectedTopologyInput.leftCompletedChain :=
  selectedTopologyInput.leftCompletedChainHomeomorph

/-- The discontinuous shelf's completed right chain is parameterized by the
same generic producer, including its horizontal reentrant jump segment. -/
noncomputable def rightCompletedChainParameterization :
    Set.Icc (0 : ℝ) 1 ≃ₜ selectedTopologyInput.rightCompletedChain :=
  selectedTopologyInput.rightCompletedChainHomeomorph

/-- Both shelf parameterizations preserve the intrinsic lower and upper split
points despite the right-chain jump at height one. -/
theorem completedChainParameterizations_endpoints :
    ((leftCompletedChainParameterization ⟨0, by norm_num⟩ :
        selectedTopologyInput.leftCompletedChain) : PlanePoint) =
          selectedTopologyInput.lowerSplitPoint ∧
      ((leftCompletedChainParameterization ⟨1, by norm_num⟩ :
        selectedTopologyInput.leftCompletedChain) : PlanePoint) =
          selectedTopologyInput.upperSplitPoint ∧
      ((rightCompletedChainParameterization ⟨0, by norm_num⟩ :
        selectedTopologyInput.rightCompletedChain) : PlanePoint) =
          selectedTopologyInput.lowerSplitPoint ∧
      ((rightCompletedChainParameterization ⟨1, by norm_num⟩ :
        selectedTopologyInput.rightCompletedChain) : PlanePoint) =
          selectedTopologyInput.upperSplitPoint := by
  exact ⟨selectedTopologyInput.leftCompletedChainHomeomorph_zero,
    selectedTopologyInput.leftCompletedChainHomeomorph_one,
    selectedTopologyInput.rightCompletedChainHomeomorph_zero,
    selectedTopologyInput.rightCompletedChainHomeomorph_one⟩

/-- The shelf parameterizations are onto both actual completed planar chains;
the discontinuous reentrant shelf is therefore retained in the image. -/
theorem completedChainParameterizations_ranges :
    range (fun t => ((leftCompletedChainParameterization t :
      selectedTopologyInput.leftCompletedChain) : PlanePoint)) =
        selectedTopologyInput.leftCompletedChain ∧
      range (fun t => ((rightCompletedChainParameterization t :
        selectedTopologyInput.rightCompletedChain) : PlanePoint)) =
          selectedTopologyInput.rightCompletedChain :=
  ⟨selectedTopologyInput.range_leftCompletedChainHomeomorph,
    selectedTopologyInput.range_rightCompletedChainHomeomorph⟩

/-- The discontinuous shelf's complete frontier loop uses the same generic
concatenation and retains its full reentrant horizontal jump. -/
noncomputable def simpleBoundaryLoop : ℝ → PlanePoint :=
  selectedTopologyInput.completedBoundaryLoop

theorem continuous_simpleBoundaryLoop : Continuous simpleBoundaryLoop :=
  selectedTopologyInput.continuous_completedBoundaryLoop

theorem simpleBoundaryLoop_closed :
    simpleBoundaryLoop 0 = simpleBoundaryLoop 2 :=
  selectedTopologyInput.completedBoundaryLoop_closed

theorem simpleBoundaryLoop_injOn_Ico :
    Set.InjOn simpleBoundaryLoop (Set.Ico (0 : ℝ) 2) :=
  selectedTopologyInput.completedBoundaryLoop_injOn_Ico

theorem simpleBoundaryLoop_image :
    simpleBoundaryLoop '' Set.Icc (0 : ℝ) 2 = frontier carrier := by
  simpa only [simpleBoundaryLoop, aeOpenRepresentative_carrier] using
    selectedTopologyInput.image_completedBoundaryLoop_Icc

theorem frontier_connected_from_simpleBoundaryLoop :
    IsConnected (frontier carrier) := by
  simpa only [aeOpenRepresentative_carrier] using
    selectedTopologyInput.isConnected_frontier_aeOpenRepresentative

end StepPolygon

namespace UnboundedNullDisk

open CMVFigureFour.FiniteCrossingExample

/-- An unbounded planar-null modification of the independent unit-disk
representative. -/
def unboundedNullLine : Set PlanePoint := {p | p.2 = 0}

@[simp] theorem volume_unboundedNullLine :
    volume unboundedNullLine = 0 := by
  exact volume_horizontalLine 0

theorem unboundedNullLine_not_bounded :
    ¬ Bornology.IsBounded unboundedNullLine := by
  intro hbounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  have hCnonneg : 0 ≤ C := by
    have hzero := hC ((0, 0) : PlanePoint) rfl
    simpa using hzero
  have hCplus : 0 ≤ C + 1 := by linarith
  have hlarge := hC ((C + 1, 0) : PlanePoint) rfl
  have hnorm : ‖((C + 1, 0) : PlanePoint)‖ = C + 1 := by
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hCplus, hCplus]
  rw [hnorm] at hlarge
  linarith

/-- The actual source differs from its bounded open representative by the
unbounded null line. -/
def sourceCarrier : Set PlanePoint :=
  openUnitDisk ∪ unboundedNullLine

theorem sourceCarrier_ae_openUnitDisk :
    sourceCarrier =ᵐ[volume] openUnitDisk := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null (t := unboundedNullLine)
    · rintro p ⟨hpSource, hpNotDisk⟩
      rcases hpSource with hpDisk | hpLine
      · exact (hpNotDisk hpDisk).elim
      · exact hpLine
    · exact volume_unboundedNullLine
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpDisk, hpNotSource⟩
      exact (hpNotSource (Or.inl hpDisk)).elim
    · exact measure_empty

theorem sourceCarrier_ne_openUnitDisk :
    sourceCarrier ≠ openUnitDisk := by
  intro hEq
  have hmem : ((2, 0) : PlanePoint) ∈ sourceCarrier := by
    exact Or.inr rfl
  rw [hEq] at hmem
  norm_num [openUnitDisk] at hmem

theorem sourceCarrier_not_bounded :
    ¬ Bornology.IsBounded sourceCarrier := by
  intro hbounded
  apply unboundedNullLine_not_bounded
  exact hbounded.subset (fun _ hp => Or.inr hp)

theorem hasAEIntervalHorizontalSections_sourceCarrier :
    HasAEIntervalHorizontalSections sourceCarrier := by
  have hslices :=
    ae_horizontalSection_congr_ae sourceCarrier_ae_openUnitDisk
  filter_upwards [hslices,
    UnitDisk.hasAEIntervalHorizontalSections_openUnitDisk] with y hsourceDisk hDisk
  rcases hDisk with ⟨I, hI, hDiskI⟩
  exact ⟨I, hI, hsourceDisk.trans hDiskI⟩

theorem aeOpenRepresentative_sourceCarrier :
    aeOpenRepresentative sourceCarrier = openUnitDisk := by
  rw [aeOpenRepresentative_congr_ae sourceCarrier_ae_openUnitDisk,
    UnitDisk.aeOpenRepresentative_openUnitDisk]

noncomputable def selectedBoundaryAtlas :
    BoundaryHalfSpaceAtlas (aeOpenRepresentative sourceCarrier) := by
  rw [aeOpenRepresentative_congr_ae sourceCarrier_ae_openUnitDisk]
  exact UnitDisk.selectedBoundaryAtlas

/-- The topology producer stores only the bounded disk representative while
its original carrier is genuinely unbounded. -/
noncomputable def selectedTopologyInput :
    SelectedBoundaryTopologyInput sourceCarrier openUnitDisk where
  representative_nonempty :=
    UnitDisk.selectedTopologyInput.representative_nonempty
  representative_open := UnitDisk.selectedTopologyInput.representative_open
  representative_bounded :=
    UnitDisk.selectedTopologyInput.representative_bounded
  representative_connected :=
    UnitDisk.selectedTopologyInput.representative_connected
  carrier_ae := sourceCarrier_ae_openUnitDisk
  interval_sections := hasAEIntervalHorizontalSections_sourceCarrier
  local_atlas := selectedBoundaryAtlas

/-- The trace is assigned only to the selected bounded representative, never to
the topological frontier of the AE-equal unbounded source. -/
noncomputable def selectedTrace :
    CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
      (aeOpenRepresentative sourceCarrier) :=
  selectedTopologyInput.closedBoundaryTrace

theorem continuous_selectedTrace : Continuous selectedTrace.trace :=
  selectedTopologyInput.continuous_closedBoundaryTrace

theorem selectedTrace_start_lt_finish :
    selectedTrace.start < selectedTrace.finish :=
  selectedTopologyInput.closedBoundaryTrace_start_lt_finish

theorem selectedTrace_injOn_Ico :
    Set.InjOn selectedTrace.trace
      (Set.Ico selectedTrace.start selectedTrace.finish) :=
  selectedTopologyInput.closedBoundaryTrace_injOn_Ico

theorem selectedRepresentative_isMinimizer_of_source
    {lam : ℝ} (hlam : 1 < lam)
    (hsource :
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
      (aeOpenRepresentative sourceCarrier) :=
  selectedTopologyInput.selectedRepresentative_isMinimizer_of_source
    hlam hsource

/-- Compiled scope contract: an actual unbounded AE modification receives a
trace only on its selected bounded representative, while arbitrary-density
source minimality is transported by the retained AE semantic theorem. -/
theorem selectedTrace_unboundedSource_compiledContract
    {lam : ℝ} (hlam : 1 < lam)
    (hsource :
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    sourceCarrier = openUnitDisk ∪ unboundedNullLine ∧
      volume unboundedNullLine = 0 ∧
      (¬ Bornology.IsBounded unboundedNullLine) ∧
      sourceCarrier ≠ openUnitDisk ∧
      (¬ Bornology.IsBounded sourceCarrier) ∧
      IsOpen openUnitDisk ∧
      Bornology.IsBounded openUnitDisk ∧
      sourceCarrier =ᵐ[volume] openUnitDisk ∧
      selectedTrace.start < selectedTrace.finish ∧
      Continuous selectedTrace.trace ∧
      Set.InjOn selectedTrace.trace
        (Set.Ico selectedTrace.start selectedTrace.finish) ∧
      selectedTrace.trace ''
          Set.Icc selectedTrace.start selectedTrace.finish =
        frontier (aeOpenRepresentative sourceCarrier) ∧
      (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
        (aeOpenRepresentative sourceCarrier) := by
  exact ⟨rfl, volume_unboundedNullLine, unboundedNullLine_not_bounded,
    sourceCarrier_ne_openUnitDisk, sourceCarrier_not_bounded,
    CMVFigureFour.FiniteCrossingExample.isOpen_openUnitDisk,
    CMVFigureFour.FiniteCrossingExample.isBounded_openUnitDisk,
    sourceCarrier_ae_openUnitDisk, selectedTrace_start_lt_finish,
    continuous_selectedTrace, selectedTrace_injOn_Ico,
    selectedTrace.complete_image,
    selectedRepresentative_isMinimizer_of_source hlam hsource⟩

end UnboundedNullDisk
end CMVBoundaryLocalAtlas
