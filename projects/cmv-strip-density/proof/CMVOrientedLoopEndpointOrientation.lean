import CMVOrientedLoopOrientation
import CMVOrientedLoopEmbeddedness

/-!
# Endpoint compatibility for occupied-left boundary arcs

This module connects the branch-independent orientation propagated across each
open finite arc to an actual regular trace entering that arc at one endpoint.
The proof uses only continuity and injectivity of the trace and the selected
embedded compact-arc coordinate; it never differentiates the topological arc
parameterization.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CMVRelaxation
open FiniteJunctionRepair
open CMVBoundaryLocalAtlas
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem
end CMVRelaxation


namespace CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem

variable {O : Set _root_.PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- A normalized finite-arc point, retained in the selected chart domain. -/
noncomputable def finiteArcPointLRLocalPoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) (u : unitInterval) :
    (D.arc (D.finiteArcChart e)).localDomain := by
  refine ⟨D.finiteArcPointLR e u, ?_⟩
  have hclosure := D.finiteArcPointLR_mem_finiteArcClosure e u
  rw [D.finiteArcClosure_eq_selectedClosedArc] at hclosure
  rcases hclosure with ⟨z, _hz, hq⟩
  rw [← hq]
  exact (D.arc (D.finiteArcChart e)).parameterHomeomorph.symm
    ((D.arc (D.finiteArcChart e)).coreParameterToParameterInterval z) |>.2

@[simp] theorem finiteArcPointLRLocalPoint_val
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) (u : unitInterval) :
    (D.finiteArcPointLRLocalPoint e u : FrontierSpace O) =
      D.finiteArcPointLR e u :=
  rfl

/-- The selected finite-arc chart coordinate of its normalized compact path is
the positive affine coordinate used to define that path. -/
theorem finiteArcPathLR_chartCoordinate
    (D : FiniteChartCutSystem A)
    (e : D.ArcIndex) (u : unitInterval) :
    ((D.arc (D.finiteArcChart e)).parameterHomeomorph
        (D.finiteArcPointLRLocalPoint e u) : ℝ) =
      D.finiteArcLowerParameter e + (u : ℝ) *
        (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e) := by
  let C := D.arc (D.finiteArcChart e)
  let z := D.finiteArcUnitCoreParameter e u
  have hlocal :
      C.parameterHomeomorph.symm (C.coreParameterToParameterInterval z) =
        D.finiteArcPointLRLocalPoint e u := by
    apply Subtype.ext
    rfl
  have hparameter := congrArg C.parameterHomeomorph hlocal
  rw [C.parameterHomeomorph.apply_symm_apply] at hparameter
  have hvalue :=
    congrArg (fun t : C.parameterInterval => (t : ℝ)) hparameter
  exact hvalue.symm.trans (by rfl)

/-- The frontier-subtype compact-arc parameterization is continuous. -/
theorem continuous_finiteArcPointLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Continuous (D.finiteArcPointLR e) := by
  apply Continuous.subtype_mk
  exact (D.finiteArcPathLR e).continuous

/-- The normalized compact-arc parameterization is a closed embedding. -/
theorem isClosedEmbedding_finiteArcPointLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Topology.IsClosedEmbedding (D.finiteArcPointLR e) :=
  (D.continuous_finiteArcPointLR e).isClosedEmbedding
    (D.finiteArcPointLR_injective e)

/-- The normalized parameter interval is homeomorphic to the literal selected
compact arc.  This exposes a continuous inverse without adding a second
parameterization convention. -/
noncomputable def finiteArcPointLRHomeomorph
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    unitInterval ≃ₜ D.finiteArcClosure e :=
  (Homeomorph.Set.univ unitInterval).symm |>.trans
    ((D.isClosedEmbedding_finiteArcPointLR e).isEmbedding.homeomorphImage
      Set.univ) |>.trans
    (Homeomorph.setCongr (by
      rw [Set.image_univ, D.range_finiteArcPointLR e]))

@[simp] theorem finiteArcPointLRHomeomorph_apply
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) (u : unitInterval) :
    (D.finiteArcPointLRHomeomorph e u :
      CMVBoundaryLocalAtlas.FrontierSpace O) = D.finiteArcPointLR e u :=
  rfl

@[simp] theorem finiteArcPointLRHomeomorph_symm_apply
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (q : D.finiteArcClosure e) :
    D.finiteArcPointLR e (D.finiteArcPointLRHomeomorph e |>.symm q) = q.1 := by
  have h := (D.finiteArcPointLRHomeomorph e).apply_symm_apply q
  exact congrArg Subtype.val h

@[simp] theorem finiteArcPointLRHomeomorph_symm_leftEndpoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (hleft : D.finiteArcLeftEndpoint e ∈ D.finiteArcClosure e) :
    (D.finiteArcPointLRHomeomorph e).symm
        ⟨D.finiteArcLeftEndpoint e, hleft⟩ = 0 := by
  apply (D.finiteArcPointLRHomeomorph e).injective
  apply Subtype.ext
  simpa only [D.finiteArcPointLRHomeomorph_apply,
    (D.finiteArcPointLRHomeomorph e).apply_symm_apply] using
      (D.finiteArcPointLR_zero e).symm

@[simp] theorem finiteArcPointLRHomeomorph_symm_rightEndpoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (hright : D.finiteArcRightEndpoint e ∈ D.finiteArcClosure e) :
    (D.finiteArcPointLRHomeomorph e).symm
        ⟨D.finiteArcRightEndpoint e, hright⟩ = 1 := by
  apply (D.finiteArcPointLRHomeomorph e).injective
  apply Subtype.ext
  simpa only [D.finiteArcPointLRHomeomorph_apply,
    (D.finiteArcPointLRHomeomorph e).apply_symm_apply] using
      (D.finiteArcPointLR_one e).symm

/-- The inverse compact-arc coordinate detects precisely the open arc. -/
theorem finiteArcPointLRHomeomorph_symm_mem_openUnitInterval_iff
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (q : D.finiteArcClosure e) :
    (((D.finiteArcPointLRHomeomorph e).symm q : unitInterval) : ℝ) ∈
        Ioo 0 1 ↔
      q.1 ∈ D.finiteArcInterior e := by
  rw [← D.finiteArcPointLR_mem_finiteArcInterior_iff e
    ((D.finiteArcPointLRHomeomorph e).symm q)]
  simp only [D.finiteArcPointLRHomeomorph_symm_apply]

/-- A continuous injective compact-interval coordinate starting at the left
endpoint of `unitInterval` must increase. -/
theorem strictMono_of_continuous_injective_Icc_start_eq_zero
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hstart : f ⟨a, ⟨le_rfl, hab.le⟩⟩ = 0) :
    StrictMono f := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exact hmono
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} :=
      ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} :=
      ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hyx : f y < f x := hanti hxy
    rw [show x = ⟨a, ⟨le_rfl, hab.le⟩⟩ by rfl, hstart] at hyx
    exact (not_lt_of_ge (f y).2.1) hyx

/-- A continuous injective compact-interval coordinate starting at the right
endpoint of `unitInterval` must decrease. -/
theorem strictAnti_of_continuous_injective_Icc_start_eq_one
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hstart : f ⟨a, ⟨le_rfl, hab.le⟩⟩ = 1) :
    StrictAnti f := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} :=
      ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} :=
      ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hxy' : f x < f y := hmono hxy
    rw [show x = ⟨a, ⟨le_rfl, hab.le⟩⟩ by rfl, hstart] at hxy'
    exact (not_lt_of_ge (f y).2.2) hxy'
  · exact hanti

/-- A continuous injective compact-interval coordinate ending at the left
endpoint of `unitInterval` must decrease. -/
theorem strictAnti_of_continuous_injective_Icc_end_eq_zero
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hend : f ⟨b, ⟨hab.le, le_rfl⟩⟩ = 0) :
    StrictAnti f := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} :=
      ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} :=
      ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hxy' : f x < f y := hmono hxy
    rw [show y = ⟨b, ⟨hab.le, le_rfl⟩⟩ by rfl, hend] at hxy'
    exact (not_lt_of_ge (f x).2.1) hxy'
  · exact hanti

/-- A continuous injective compact-interval coordinate ending at the right
endpoint of `unitInterval` must increase. -/
theorem strictMono_of_continuous_injective_Icc_end_eq_one
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hend : f ⟨b, ⟨hab.le, le_rfl⟩⟩ = 1) :
    StrictMono f := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exact hmono
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} :=
      ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} :=
      ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hyx : f y < f x := hanti hxy
    rw [show y = ⟨b, ⟨hab.le, le_rfl⟩⟩ by rfl, hend] at hyx
    exact (not_lt_of_ge (f x).2.2) hyx

/-- One half-edge endpoint retained in the closure of its incident compact
arc. -/
def halfEdgeClosurePoint
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.finiteArcClosure h.1.2 :=
  ⟨h.1.1.1, h.2⟩

/-- The inverse compact-arc coordinate sends a half-edge vertex to its exact
selected endpoint bit. -/
theorem finiteArcPointLRHomeomorph_symm_halfEdgeClosurePoint
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (D.finiteArcPointLRHomeomorph h.1.2).symm
        (D.halfEdgeClosurePoint h) =
      if (D.endpointHalfEdgeEquiv.symm h).2 then 1 else 0 := by
  obtain ⟨⟨e, endpointSide⟩, rfl⟩ := D.endpointHalfEdge_surjective h
  cases endpointSide
  · simp only [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge, Bool.false_eq_true,
      ↓reduceIte]
    change
      (D.finiteArcPointLRHomeomorph e).symm
          ⟨D.finiteArcLeftEndpoint e, _⟩ = 0
    exact D.finiteArcPointLRHomeomorph_symm_leftEndpoint e _
  · simp only [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
      ↓reduceIte]
    change
      (D.finiteArcPointLRHomeomorph e).symm
          ⟨D.finiteArcRightEndpoint e, _⟩ = 1
    exact D.finiteArcPointLRHomeomorph_symm_rightEndpoint e _

/-- Switching a half-edge at a cut vertex exchanges the negative and positive
local chart germs. -/
@[simp] theorem incidentArcEquivBool_symm_switchHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (D.cutPointCoreNeighborhood
        (D.switchHalfEdge h).1.1).incidentArcEquivBool.symm
        (D.incidentAtHalfEdge (D.switchHalfEdge h)) =
      !(D.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool.symm
        (D.incidentAtHalfEdge h) := by
  change
    (D.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool.symm
      ((D.cutPointCoreNeighborhood h.1.1).otherIncidentArc
        (D.incidentAtHalfEdge h)) = _
  simp only [CutPointCoreNeighborhood.otherIncidentArc, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.boolNot_apply]

/-- The half-edge represented by one of the two local chart germs at a cut
vertex. -/
noncomputable def localGermHalfEdge
    (D : FiniteChartCutSystem A) (v : D.cutPoints) (side : Bool) :
    D.HalfEdge :=
  ⟨(v, ((D.cutPointCoreNeighborhood v).incidentArcEquivBool side).1),
    ((D.cutPointCoreNeighborhood v).incidentArcEquivBool side).2⟩

@[simp] theorem incidentArcEquivBool_symm_localGermHalfEdge
    (D : FiniteChartCutSystem A) (v : D.cutPoints) (side : Bool) :
    (D.cutPointCoreNeighborhood v).incidentArcEquivBool.symm
        (D.incidentAtHalfEdge (D.localGermHalfEdge v side)) = side := by
  unfold localGermHalfEdge incidentAtHalfEdge
  rw [show
    (⟨((D.cutPointCoreNeighborhood v).incidentArcEquivBool side).1, _⟩ :
      D.IncidentArc v) =
        (D.cutPointCoreNeighborhood v).incidentArcEquivBool side by
      apply Subtype.ext
      rfl]
  exact
    (D.cutPointCoreNeighborhood v).incidentArcEquivBool.symm_apply_apply side

@[simp] theorem switchHalfEdge_localGermHalfEdge
    (D : FiniteChartCutSystem A) (v : D.cutPoints) (side : Bool) :
    D.switchHalfEdge (D.localGermHalfEdge v side) =
      D.localGermHalfEdge v (!side) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      ((D.cutPointCoreNeighborhood v).otherIncidentArc
        ((D.cutPointCoreNeighborhood v).incidentArcEquivBool side)).1 =
      ((D.cutPointCoreNeighborhood v).incidentArcEquivBool (!side)).1
    congr 1
    simp only [CutPointCoreNeighborhood.otherIncidentArc, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.boolNot_apply]

end CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem
namespace CMVRelaxation
open FiniteJunctionRepair
open CMVBoundaryLocalAtlas
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem


namespace OccupiedLeftArcBranchAssignment

variable {O : Set _root_.PlanePoint}
    {T : FinitePiecewiseRegularBoundaryTopology O}

/-- Common geometric data identifying an ordered occupied-left branch segment
with two points of a continuous injective path in one compact boundary arc. -/
structure EndpointArcPathAgreement
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (h : T.chartCuts.HalfEdge) where
  parameterStart : ℝ
  parameterEnd : ℝ
  parameterStart_lt_parameterEnd : parameterStart < parameterEnd
  path : {t : ℝ // t ∈ Icc parameterStart parameterEnd} →
    T.chartCuts.finiteArcClosure h.1.2
  path_continuous : Continuous path
  path_injective : Function.Injective path
  branchPoint : CMVBoundaryLocalAtlas.FrontierSpace O
  branchPoint_mem :
    branchPoint ∈ T.chartCuts.finiteArcInterior h.1.2
  branch : OccupiedLeftArcBranch O branchPoint.1
  neighborhood :
    OccupiedLeftArcCoordinateNeighborhood T h.1.2 branchPoint_mem branch
  pathEarlier : {t : ℝ // t ∈ Icc parameterStart parameterEnd}
  pathLater : {t : ℝ // t ∈ Icc parameterStart parameterEnd}
  pathEarlier_lt_pathLater : pathEarlier < pathLater
  neighborhoodEarlier : neighborhood.ParameterInterval
  neighborhoodLater : neighborhood.ParameterInterval
  neighborhoodEarlier_lt_neighborhoodLater :
    neighborhoodEarlier < neighborhoodLater
  pathEarlier_eq :
    (path pathEarlier).1 = neighborhood.point neighborhoodEarlier
  pathLater_eq :
    (path pathLater).1 = neighborhood.point neighborhoodLater

/-- An ordered occupied-left branch segment leaving a compact arc endpoint. -/
structure EndpointArcContinuation
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (h : T.chartCuts.HalfEdge)
    extends EndpointArcPathAgreement T h where
  path_start :
    path ⟨parameterStart,
      ⟨le_rfl, parameterStart_lt_parameterEnd.le⟩⟩ =
      T.chartCuts.halfEdgeClosurePoint h

/-- An ordered occupied-left branch segment approaching a compact arc
endpoint. -/
structure EndpointArcApproach
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (h : T.chartCuts.HalfEdge)
    extends EndpointArcPathAgreement T h where
  path_end :
    path ⟨parameterEnd,
      ⟨parameterStart_lt_parameterEnd.le, le_rfl⟩⟩ =
      T.chartCuts.halfEdgeClosurePoint h

theorem EndpointArcPathAgreement.inverse_pathEarlier
    {h : T.chartCuts.HalfEdge}
    (W : EndpointArcPathAgreement T h) :
    (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
        (W.path W.pathEarlier) =
      W.neighborhood.unitParameter W.neighborhoodEarlier := by
  apply (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).injective
  rw [(T.chartCuts.finiteArcPointLRHomeomorph h.1.2).apply_symm_apply]
  apply Subtype.ext
  change
    (W.path W.pathEarlier).1 =
      T.chartCuts.finiteArcPointLR h.1.2
        (W.neighborhood.unitParameter W.neighborhoodEarlier)
  rw [W.pathEarlier_eq, W.neighborhood.finiteArcPointLR_unitParameter]

theorem EndpointArcPathAgreement.inverse_pathLater
    {h : T.chartCuts.HalfEdge}
    (W : EndpointArcPathAgreement T h) :
    (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
        (W.path W.pathLater) =
      W.neighborhood.unitParameter W.neighborhoodLater := by
  apply (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).injective
  rw [(T.chartCuts.finiteArcPointLRHomeomorph h.1.2).apply_symm_apply]
  apply Subtype.ext
  change
    (W.path W.pathLater).1 =
      T.chartCuts.finiteArcPointLR h.1.2
        (W.neighborhood.unitParameter W.neighborhoodLater)
  rw [W.pathLater_eq, W.neighborhood.finiteArcPointLR_unitParameter]

/-- A continuous injective path that leaves a half-edge vertex through the
closure of that half-edge's arc has forced normalized direction: increasing
from a left endpoint and decreasing from a right endpoint. -/
theorem strictMonotone_finiteArcInverse_from_halfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    {a b : ℝ} (hab : a < b) (h : T.chartCuts.HalfEdge)
    (γ : {t : ℝ // t ∈ Icc a b} →
      T.chartCuts.finiteArcClosure h.1.2)
    (hγ : Continuous γ) (hγinj : Function.Injective γ)
    (hstart : γ ⟨a, ⟨le_rfl, hab.le⟩⟩ =
      T.chartCuts.halfEdgeClosurePoint h) :
    match B.halfEdgeEndpointSide h with
    | false => StrictMono
        (fun t => (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm (γ t))
    | true => StrictAnti
        (fun t => (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm (γ t)) := by
  obtain ⟨⟨e, endpointSide⟩, rfl⟩ :=
    T.chartCuts.endpointHalfEdge_surjective h
  cases endpointSide
  · simp only [B.halfEdgeEndpointSide_endpointHalfEdge]
    apply strictMono_of_continuous_injective_Icc_start_eq_zero hab
    · exact (T.chartCuts.finiteArcPointLRHomeomorph e).symm.continuous.comp hγ
    · exact
        (T.chartCuts.finiteArcPointLRHomeomorph e).symm.injective.comp hγinj
    · rw [hstart]
      simpa only [T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
        Bool.false_eq_true, ↓reduceIte] using
        T.chartCuts.finiteArcPointLRHomeomorph_symm_halfEdgeClosurePoint
          (T.chartCuts.endpointHalfEdge (e, false))
  · simp only [B.halfEdgeEndpointSide_endpointHalfEdge]
    apply strictAnti_of_continuous_injective_Icc_start_eq_one hab
    · exact (T.chartCuts.finiteArcPointLRHomeomorph e).symm.continuous.comp hγ
    · exact
        (T.chartCuts.finiteArcPointLRHomeomorph e).symm.injective.comp hγinj
    · rw [hstart]
      simpa only [T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
        Bool.true_eq, ↓reduceIte] using
        T.chartCuts.finiteArcPointLRHomeomorph_symm_halfEdgeClosurePoint
          (T.chartCuts.endpointHalfEdge (e, true))

/-- A continuous injective path that approaches a half-edge vertex through
the closure of that half-edge's arc has the reverse normalized direction:
decreasing toward a left endpoint and increasing toward a right endpoint. -/
theorem strictMonotone_finiteArcInverse_to_halfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    {a b : ℝ} (hab : a < b) (h : T.chartCuts.HalfEdge)
    (γ : {t : ℝ // t ∈ Icc a b} →
      T.chartCuts.finiteArcClosure h.1.2)
    (hγ : Continuous γ) (hγinj : Function.Injective γ)
    (hend : γ ⟨b, ⟨hab.le, le_rfl⟩⟩ =
      T.chartCuts.halfEdgeClosurePoint h) :
    match B.halfEdgeEndpointSide h with
    | false => StrictAnti
        (fun t => (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm (γ t))
    | true => StrictMono
        (fun t => (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm (γ t)) := by
  obtain ⟨⟨e, endpointSide⟩, rfl⟩ :=
    T.chartCuts.endpointHalfEdge_surjective h
  cases endpointSide
  · simp only [B.halfEdgeEndpointSide_endpointHalfEdge]
    apply strictAnti_of_continuous_injective_Icc_end_eq_zero hab
    · exact (T.chartCuts.finiteArcPointLRHomeomorph e).symm.continuous.comp hγ
    · exact
        (T.chartCuts.finiteArcPointLRHomeomorph e).symm.injective.comp hγinj
    · rw [hend]
      simpa only [T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
        Bool.false_eq_true, ↓reduceIte] using
        T.chartCuts.finiteArcPointLRHomeomorph_symm_halfEdgeClosurePoint
          (T.chartCuts.endpointHalfEdge (e, false))
  · simp only [B.halfEdgeEndpointSide_endpointHalfEdge]
    apply strictMono_of_continuous_injective_Icc_end_eq_one hab
    · exact (T.chartCuts.finiteArcPointLRHomeomorph e).symm.continuous.comp hγ
    · exact
        (T.chartCuts.finiteArcPointLRHomeomorph e).symm.injective.comp hγinj
    · rw [hend]
      simpa only [T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
        Bool.true_eq, ↓reduceIte] using
        T.chartCuts.finiteArcPointLRHomeomorph_symm_halfEdgeClosurePoint
          (T.chartCuts.endpointHalfEdge (e, true))

/-- Any geometric occupied-left continuation of a half-edge points away from
that endpoint in the propagated compact-arc orientation. -/
theorem representativeOrientationPointsAway_of_endpointArcContinuation
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge)
    (W : EndpointArcContinuation T h) :
    B.representativeOrientationPointsAway h = true := by
  have hdirection :=
    B.strictMonotone_finiteArcInverse_from_halfEdge
      W.parameterStart_lt_parameterEnd h W.path
      W.path_continuous W.path_injective W.path_start
  have hEarlier :
      (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
          (W.path W.pathEarlier) =
        W.neighborhood.unitParameter W.neighborhoodEarlier := by
    apply (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).injective
    rw [(T.chartCuts.finiteArcPointLRHomeomorph h.1.2).apply_symm_apply]
    apply Subtype.ext
    change
      (W.path W.pathEarlier).1 =
        T.chartCuts.finiteArcPointLR h.1.2
          (W.neighborhood.unitParameter W.neighborhoodEarlier)
    rw [W.pathEarlier_eq,
      W.neighborhood.finiteArcPointLR_unitParameter]
  have hLater :
      (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
          (W.path W.pathLater) =
        W.neighborhood.unitParameter W.neighborhoodLater := by
    apply (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).injective
    rw [(T.chartCuts.finiteArcPointLRHomeomorph h.1.2).apply_symm_apply]
    apply Subtype.ext
    change
      (W.path W.pathLater).1 =
        T.chartCuts.finiteArcPointLR h.1.2
          (W.neighborhood.unitParameter W.neighborhoodLater)
    rw [W.pathLater_eq,
      W.neighborhood.finiteArcPointLR_unitParameter]
  generalize hside :
    B.halfEdgeEndpointSide h = endpointSide at hdirection ⊢
  cases endpointSide
  · have hpathOrder :
        W.neighborhood.unitParameter W.neighborhoodEarlier <
          W.neighborhood.unitParameter W.neighborhoodLater := by
      have hmono :
          StrictMono (fun t =>
            (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
              (W.path t)) := by
        simpa only [hside] using hdirection
      simpa only [hEarlier, hLater] using
        hmono W.pathEarlier_lt_pathLater
    generalize harc :
      B.arcCoordinateIncreases h.1.2 = arcDirection
    cases arcDirection
    · have hbackward :=
        B.coordinateNeighborhood_strictAnti_unitParameter
          h.1.2 W.branchPoint W.branchPoint_mem W.branch W.neighborhood
          harc
          W.neighborhoodEarlier_lt_neighborhoodLater
      exact False.elim ((not_lt_of_ge hpathOrder.le) hbackward)
    · simp only [representativeOrientationPointsAway, hside, harc]
      rfl
  · have hpathOrder :
        W.neighborhood.unitParameter W.neighborhoodLater <
          W.neighborhood.unitParameter W.neighborhoodEarlier := by
      have hanti :
          StrictAnti (fun t =>
            (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
              (W.path t)) := by
        simpa only [hside] using hdirection
      simpa only [hEarlier, hLater] using
        hanti W.pathEarlier_lt_pathLater
    generalize harc :
      B.arcCoordinateIncreases h.1.2 = arcDirection
    cases arcDirection
    · simp only [representativeOrientationPointsAway, hside, harc]
      rfl
    · have hforward :=
        B.coordinateNeighborhood_strictMono_unitParameter
          h.1.2 W.branchPoint W.branchPoint_mem W.branch W.neighborhood
          harc
          W.neighborhoodEarlier_lt_neighborhoodLater
      exact False.elim ((not_lt_of_ge hpathOrder.le) hforward)



/-- Any geometric occupied-left approach to a half-edge points toward that
endpoint in the propagated compact-arc orientation. -/
theorem representativeOrientationPointsAway_of_endpointArcApproach
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge)
    (W : EndpointArcApproach T h) :
    B.representativeOrientationPointsAway h = false := by
  have hdirection :=
    B.strictMonotone_finiteArcInverse_to_halfEdge
      W.parameterStart_lt_parameterEnd h W.path
      W.path_continuous W.path_injective W.path_end
  have hEarlier :=
    W.toEndpointArcPathAgreement.inverse_pathEarlier
  have hLater :=
    W.toEndpointArcPathAgreement.inverse_pathLater
  generalize hside :
    B.halfEdgeEndpointSide h = endpointSide at hdirection ⊢
  cases endpointSide
  · have hpathOrder :
        W.neighborhood.unitParameter W.neighborhoodLater <
          W.neighborhood.unitParameter W.neighborhoodEarlier := by
      have hanti :
          StrictAnti (fun t =>
            (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
              (W.path t)) := by
        simpa only [hside] using hdirection
      simpa only [hEarlier, hLater] using
        hanti W.pathEarlier_lt_pathLater
    generalize harc :
      B.arcCoordinateIncreases h.1.2 = arcDirection
    cases arcDirection
    · simp only [representativeOrientationPointsAway, hside, harc]
      rfl
    · have hforward :=
        B.coordinateNeighborhood_strictMono_unitParameter
          h.1.2 W.branchPoint W.branchPoint_mem W.branch W.neighborhood
          harc
          W.neighborhoodEarlier_lt_neighborhoodLater
      exact False.elim ((not_lt_of_ge hpathOrder.le) hforward)
  · have hpathOrder :
        W.neighborhood.unitParameter W.neighborhoodEarlier <
          W.neighborhood.unitParameter W.neighborhoodLater := by
      have hmono :
          StrictMono (fun t =>
            (T.chartCuts.finiteArcPointLRHomeomorph h.1.2).symm
              (W.path t)) := by
        simpa only [hside] using hdirection
      simpa only [hEarlier, hLater] using
        hmono W.pathEarlier_lt_pathLater
    generalize harc :
      B.arcCoordinateIncreases h.1.2 = arcDirection
    cases arcDirection
    · have hbackward :=
        B.coordinateNeighborhood_strictAnti_unitParameter
          h.1.2 W.branchPoint W.branchPoint_mem W.branch W.neighborhood
          harc
          W.neighborhoodEarlier_lt_neighborhoodLater
      exact False.elim ((not_lt_of_ge hpathOrder.le) hbackward)
    · simp only [representativeOrientationPointsAway, hside, harc]
      rfl

/-- A single occupied-left regular trace, parametrized to the right from a
half-edge endpoint and staying in that half-edge's open finite arc thereafter.
The carrier field makes rebasing at an interior point geometric rather than
an orientation assumption. -/
structure RightSidedEndpointTrace
    (h : T.chartCuts.HalfEdge)
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide) where
  trace : OccupiedLeftRegularTrace axis side O h.1.1.1
  radius : ℝ
  radius_pos : 0 < radius
  frontier_mem : ∀ {t : ℝ},
    t ∈ Icc
      (occupiedLeftBaseParameter axis side h.1.1.1)
      (occupiedLeftBaseParameter axis side h.1.1.1 + radius) →
    occupiedLeftGraphTrace axis side trace.graph t ∈ frontier O
  arc_mem : ∀ {t : ℝ} (ht : t ∈ Ioc
      (occupiedLeftBaseParameter axis side h.1.1.1)
      (occupiedLeftBaseParameter axis side h.1.1.1 + radius)),
    (⟨occupiedLeftGraphTrace axis side trace.graph t,
      frontier_mem ⟨ht.1.le, ht.2⟩⟩ :
        CMVBoundaryLocalAtlas.FrontierSpace O) ∈
      T.chartCuts.finiteArcInterior h.1.2
  carrier_at : ∀ {t : ℝ}, t ∈ Ioc
      (occupiedLeftBaseParameter axis side h.1.1.1)
      (occupiedLeftBaseParameter axis side h.1.1.1 + radius) →
    ∀ᶠ q in 𝓝 (occupiedLeftGraphTrace axis side trace.graph t),
      q ∈ O ↔ q ∈ orientedGraphDomain axis side trace.graph

namespace RightSidedEndpointTrace

variable {h : T.chartCuts.HalfEdge}
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    (E : RightSidedEndpointTrace h axis side)

abbrev ParameterInterval :=
  Icc (occupiedLeftBaseParameter axis side h.1.1.1)
    (occupiedLeftBaseParameter axis side h.1.1.1 + E.radius)

def point (t : E.ParameterInterval) :
    CMVBoundaryLocalAtlas.FrontierSpace O :=
  ⟨occupiedLeftGraphTrace axis side E.trace.graph t.1,
    E.frontier_mem t.2⟩

@[simp] theorem point_base :
    E.point ⟨occupiedLeftBaseParameter axis side h.1.1.1,
      le_rfl, by linarith [E.radius_pos]⟩ = h.1.1 := by
  apply Subtype.ext
  exact E.trace.trace_base

theorem point_mem_closure (t : E.ParameterInterval) :
    E.point t ∈ T.chartCuts.finiteArcClosure h.1.2 := by
  by_cases ht : occupiedLeftBaseParameter axis side h.1.1.1 < t.1
  · apply subset_closure
    exact E.arc_mem ⟨ht, t.2.2⟩
  · have htbase :
        t.1 = occupiedLeftBaseParameter axis side h.1.1.1 :=
      le_antisymm (le_of_not_gt ht) t.2.1
    let base : E.ParameterInterval :=
      ⟨occupiedLeftBaseParameter axis side h.1.1.1,
        le_rfl, by linarith [E.radius_pos]⟩
    have htEq : t = base := Subtype.ext htbase
    rw [htEq, E.point_base]
    exact h.2

def closurePoint (t : E.ParameterInterval) :
    T.chartCuts.finiteArcClosure h.1.2 :=
  ⟨E.point t, E.point_mem_closure t⟩

theorem continuous_closurePoint : Continuous E.closurePoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact E.trace.trace_contDiff.continuous.comp continuous_subtype_val

theorem injective_closurePoint :
    Function.Injective E.closurePoint := by
  intro s t hst
  apply Subtype.ext
  exact E.trace.trace_injective
    (congrArg
      (fun q : T.chartCuts.finiteArcClosure h.1.2 => q.1.1) hst)

def midTime : E.ParameterInterval :=
  ⟨occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2,
    by linarith [E.radius_pos], by linarith [E.radius_pos]⟩

def midpoint : CMVBoundaryLocalAtlas.FrontierSpace O :=
  E.point E.midTime

theorem midpoint_mem_arc :
    E.midpoint ∈ T.chartCuts.finiteArcInterior h.1.2 := by
  apply E.arc_mem
  change occupiedLeftBaseParameter axis side h.1.1.1 <
      occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2 ∧
    occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2 ≤
      occupiedLeftBaseParameter axis side h.1.1.1 + E.radius
  constructor <;> linarith [E.radius_pos]

@[simp] theorem midpoint_val :
    E.midpoint.1 =
      occupiedLeftGraphTrace axis side E.trace.graph
        (occupiedLeftBaseParameter axis side h.1.1.1 +
          E.radius / 2) := rfl

@[simp] theorem baseParameter_midpoint :
    occupiedLeftBaseParameter axis side E.midpoint.1 =
      occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2 := by
  rw [← occupiedLeftTraceParameter_base, E.midpoint_val,
    occupiedLeftTraceParameter_trace]

noncomputable def midBranch :
    OccupiedLeftArcBranch O E.midpoint.1 where
  axis := axis
  side := side
  trace := E.trace.rebase (by
      rw [E.midpoint_val, occupiedLeftTraceParameter_trace])
    (E.carrier_at (by
      change occupiedLeftBaseParameter axis side h.1.1.1 <
          occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2 ∧
        occupiedLeftBaseParameter axis side h.1.1.1 + E.radius / 2 ≤
          occupiedLeftBaseParameter axis side h.1.1.1 + E.radius
      constructor <;> linarith [E.radius_pos]))

noncomputable def midNeighborhood :
    OccupiedLeftArcCoordinateNeighborhood T h.1.2 E.midpoint_mem_arc
      E.midBranch where
  radius := E.radius / 4
  radius_pos := by linarith [E.radius_pos]
  frontier_mem := by
    intro t ht
    apply E.frontier_mem
    change t ∈ Icc
      (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
      (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
    rw [E.baseParameter_midpoint] at ht
    constructor <;> linarith [ht.1, ht.2, E.radius_pos]
  arc_mem := by
    intro t ht
    apply E.arc_mem
    change t ∈ Icc
      (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
      (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
    rw [E.baseParameter_midpoint] at ht
    constructor <;> linarith [ht.1, ht.2, E.radius_pos]

def ambientTime (t : E.midNeighborhood.ParameterInterval) :
    E.ParameterInterval := by
  refine ⟨t.1, ?_⟩
  have ht := t.2
  change t.1 ∈ Icc
    (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
    (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
  rw [E.baseParameter_midpoint] at ht
  constructor <;> linarith [ht.1, ht.2, E.radius_pos]

@[simp] theorem midNeighborhood_point
    (t : E.midNeighborhood.ParameterInterval) :
    E.midNeighborhood.point t = E.point (E.ambientTime t) := rfl

def neighborhoodEarlier : E.midNeighborhood.ParameterInterval :=
  ⟨occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
      E.midpoint.1 - E.midNeighborhood.radius,
    le_rfl, by linarith [E.midNeighborhood.radius_pos]⟩

def neighborhoodLater : E.midNeighborhood.ParameterInterval :=
  ⟨occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
      E.midpoint.1 + E.midNeighborhood.radius,
    by linarith [E.midNeighborhood.radius_pos], le_rfl⟩

theorem neighborhoodEarlier_lt_neighborhoodLater :
    E.neighborhoodEarlier < E.neighborhoodLater := by
  change
    occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
          E.midpoint.1 - E.midNeighborhood.radius <
      occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
          E.midpoint.1 + E.midNeighborhood.radius
  linarith [E.midNeighborhood.radius_pos]

noncomputable def endpointArcContinuation :
    EndpointArcContinuation T h where
  parameterStart := occupiedLeftBaseParameter axis side h.1.1.1
  parameterEnd :=
    occupiedLeftBaseParameter axis side h.1.1.1 + E.radius
  parameterStart_lt_parameterEnd := by linarith [E.radius_pos]
  path := E.closurePoint
  path_continuous := E.continuous_closurePoint
  path_injective := E.injective_closurePoint
  branchPoint := E.midpoint
  branchPoint_mem := E.midpoint_mem_arc
  branch := E.midBranch
  neighborhood := E.midNeighborhood
  pathEarlier := E.ambientTime E.neighborhoodEarlier
  pathLater := E.ambientTime E.neighborhoodLater
  pathEarlier_lt_pathLater := E.neighborhoodEarlier_lt_neighborhoodLater
  neighborhoodEarlier := E.neighborhoodEarlier
  neighborhoodLater := E.neighborhoodLater
  neighborhoodEarlier_lt_neighborhoodLater :=
    E.neighborhoodEarlier_lt_neighborhoodLater
  pathEarlier_eq := by
    exact (E.midNeighborhood_point E.neighborhoodEarlier).symm
  pathLater_eq := by
    exact (E.midNeighborhood_point E.neighborhoodLater).symm
  path_start := by
    apply Subtype.ext
    exact E.point_base

/-- A right-parametrized occupied-left endpoint trace which immediately enters
the incident open arc forces the representative direction to point away from
that endpoint. -/
theorem representativeOrientationPointsAway_eq_true
    (B : OccupiedLeftArcBranchAssignment T)
    (E : RightSidedEndpointTrace h axis side) :
    B.representativeOrientationPointsAway h = true :=
  B.representativeOrientationPointsAway_of_endpointArcContinuation h
    E.endpointArcContinuation

end RightSidedEndpointTrace
/-- A single occupied-left regular trace, parametrized toward a half-edge
endpoint from the left and staying in that half-edge's open finite arc before
arrival. -/
structure LeftSidedEndpointTrace
    (h : T.chartCuts.HalfEdge)
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide) where
  trace : OccupiedLeftRegularTrace axis side O h.1.1.1
  radius : ℝ
  radius_pos : 0 < radius
  frontier_mem : ∀ {t : ℝ},
    t ∈ Icc
      (occupiedLeftBaseParameter axis side h.1.1.1 - radius)
      (occupiedLeftBaseParameter axis side h.1.1.1) →
    occupiedLeftGraphTrace axis side trace.graph t ∈ frontier O
  arc_mem : ∀ {t : ℝ} (ht : t ∈ Ico
      (occupiedLeftBaseParameter axis side h.1.1.1 - radius)
      (occupiedLeftBaseParameter axis side h.1.1.1)),
    (⟨occupiedLeftGraphTrace axis side trace.graph t,
      frontier_mem ⟨ht.1, ht.2.le⟩⟩ :
        CMVBoundaryLocalAtlas.FrontierSpace O) ∈
      T.chartCuts.finiteArcInterior h.1.2
  carrier_at : ∀ {t : ℝ}, t ∈ Ico
      (occupiedLeftBaseParameter axis side h.1.1.1 - radius)
      (occupiedLeftBaseParameter axis side h.1.1.1) →
    ∀ᶠ q in 𝓝 (occupiedLeftGraphTrace axis side trace.graph t),
      q ∈ O ↔ q ∈ orientedGraphDomain axis side trace.graph

namespace LeftSidedEndpointTrace

variable {h : T.chartCuts.HalfEdge}
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    (E : LeftSidedEndpointTrace h axis side)

abbrev ParameterInterval :=
  Icc (occupiedLeftBaseParameter axis side h.1.1.1 - E.radius)
    (occupiedLeftBaseParameter axis side h.1.1.1)

def point (t : E.ParameterInterval) :
    CMVBoundaryLocalAtlas.FrontierSpace O :=
  ⟨occupiedLeftGraphTrace axis side E.trace.graph t.1,
    E.frontier_mem t.2⟩

@[simp] theorem point_base :
    E.point ⟨occupiedLeftBaseParameter axis side h.1.1.1,
      by linarith [E.radius_pos], le_rfl⟩ = h.1.1 := by
  apply Subtype.ext
  exact E.trace.trace_base

theorem point_mem_closure (t : E.ParameterInterval) :
    E.point t ∈ T.chartCuts.finiteArcClosure h.1.2 := by
  by_cases ht : t.1 < occupiedLeftBaseParameter axis side h.1.1.1
  · apply subset_closure
    exact E.arc_mem ⟨t.2.1, ht⟩
  · have htbase :
        t.1 = occupiedLeftBaseParameter axis side h.1.1.1 :=
      le_antisymm t.2.2 (le_of_not_gt ht)
    let base : E.ParameterInterval :=
      ⟨occupiedLeftBaseParameter axis side h.1.1.1,
        by linarith [E.radius_pos], le_rfl⟩
    have htEq : t = base := Subtype.ext htbase
    rw [htEq, E.point_base]
    exact h.2

def closurePoint (t : E.ParameterInterval) :
    T.chartCuts.finiteArcClosure h.1.2 :=
  ⟨E.point t, E.point_mem_closure t⟩

theorem continuous_closurePoint : Continuous E.closurePoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact E.trace.trace_contDiff.continuous.comp continuous_subtype_val

theorem injective_closurePoint :
    Function.Injective E.closurePoint := by
  intro s t hst
  apply Subtype.ext
  exact E.trace.trace_injective
    (congrArg
      (fun q : T.chartCuts.finiteArcClosure h.1.2 => q.1.1) hst)

def midTime : E.ParameterInterval :=
  ⟨occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2,
    by linarith [E.radius_pos], by linarith [E.radius_pos]⟩

def midpoint : CMVBoundaryLocalAtlas.FrontierSpace O :=
  E.point E.midTime

theorem midpoint_mem_arc :
    E.midpoint ∈ T.chartCuts.finiteArcInterior h.1.2 := by
  apply E.arc_mem
  change
    occupiedLeftBaseParameter axis side h.1.1.1 - E.radius ≤
        occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2 ∧
      occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2 <
        occupiedLeftBaseParameter axis side h.1.1.1
  constructor <;> linarith [E.radius_pos]

@[simp] theorem midpoint_val :
    E.midpoint.1 =
      occupiedLeftGraphTrace axis side E.trace.graph
        (occupiedLeftBaseParameter axis side h.1.1.1 -
          E.radius / 2) := rfl

@[simp] theorem baseParameter_midpoint :
    occupiedLeftBaseParameter axis side E.midpoint.1 =
      occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2 := by
  rw [← occupiedLeftTraceParameter_base, E.midpoint_val,
    occupiedLeftTraceParameter_trace]

noncomputable def midBranch :
    OccupiedLeftArcBranch O E.midpoint.1 where
  axis := axis
  side := side
  trace := E.trace.rebase (by
      rw [E.midpoint_val, occupiedLeftTraceParameter_trace])
    (E.carrier_at (by
      change
        occupiedLeftBaseParameter axis side h.1.1.1 - E.radius ≤
            occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2 ∧
          occupiedLeftBaseParameter axis side h.1.1.1 - E.radius / 2 <
            occupiedLeftBaseParameter axis side h.1.1.1
      constructor <;> linarith [E.radius_pos]))

noncomputable def midNeighborhood :
    OccupiedLeftArcCoordinateNeighborhood T h.1.2 E.midpoint_mem_arc
      E.midBranch where
  radius := E.radius / 4
  radius_pos := by linarith [E.radius_pos]
  frontier_mem := by
    intro t ht
    apply E.frontier_mem
    change t ∈ Icc
      (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
      (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
    rw [E.baseParameter_midpoint] at ht
    constructor <;> linarith [ht.1, ht.2, E.radius_pos]
  arc_mem := by
    intro t ht
    apply E.arc_mem
    change t ∈ Icc
      (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
      (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
    rw [E.baseParameter_midpoint] at ht
    constructor <;> linarith [ht.1, ht.2, E.radius_pos]

def ambientTime (t : E.midNeighborhood.ParameterInterval) :
    E.ParameterInterval := by
  refine ⟨t.1, ?_⟩
  have ht := t.2
  change t.1 ∈ Icc
    (occupiedLeftBaseParameter axis side E.midpoint.1 - E.radius / 4)
    (occupiedLeftBaseParameter axis side E.midpoint.1 + E.radius / 4) at ht
  rw [E.baseParameter_midpoint] at ht
  constructor <;> linarith [ht.1, ht.2, E.radius_pos]

@[simp] theorem midNeighborhood_point
    (t : E.midNeighborhood.ParameterInterval) :
    E.midNeighborhood.point t = E.point (E.ambientTime t) := rfl

def neighborhoodEarlier : E.midNeighborhood.ParameterInterval :=
  ⟨occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
      E.midpoint.1 - E.midNeighborhood.radius,
    le_rfl, by linarith [E.midNeighborhood.radius_pos]⟩

def neighborhoodLater : E.midNeighborhood.ParameterInterval :=
  ⟨occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
      E.midpoint.1 + E.midNeighborhood.radius,
    by linarith [E.midNeighborhood.radius_pos], le_rfl⟩

theorem neighborhoodEarlier_lt_neighborhoodLater :
    E.neighborhoodEarlier < E.neighborhoodLater := by
  change
    occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
          E.midpoint.1 - E.midNeighborhood.radius <
      occupiedLeftBaseParameter E.midBranch.axis E.midBranch.side
          E.midpoint.1 + E.midNeighborhood.radius
  linarith [E.midNeighborhood.radius_pos]

noncomputable def endpointArcApproach :
    EndpointArcApproach T h where
  parameterStart :=
    occupiedLeftBaseParameter axis side h.1.1.1 - E.radius
  parameterEnd := occupiedLeftBaseParameter axis side h.1.1.1
  parameterStart_lt_parameterEnd := by linarith [E.radius_pos]
  path := E.closurePoint
  path_continuous := E.continuous_closurePoint
  path_injective := E.injective_closurePoint
  branchPoint := E.midpoint
  branchPoint_mem := E.midpoint_mem_arc
  branch := E.midBranch
  neighborhood := E.midNeighborhood
  pathEarlier := E.ambientTime E.neighborhoodEarlier
  pathLater := E.ambientTime E.neighborhoodLater
  pathEarlier_lt_pathLater := E.neighborhoodEarlier_lt_neighborhoodLater
  neighborhoodEarlier := E.neighborhoodEarlier
  neighborhoodLater := E.neighborhoodLater
  neighborhoodEarlier_lt_neighborhoodLater :=
    E.neighborhoodEarlier_lt_neighborhoodLater
  pathEarlier_eq := by
    exact (E.midNeighborhood_point E.neighborhoodEarlier).symm
  pathLater_eq := by
    exact (E.midNeighborhood_point E.neighborhoodLater).symm
  path_end := by
    apply Subtype.ext
    exact E.point_base

/-- A left-parametrized occupied-left endpoint trace which stays in the
incident open arc until arrival forces the representative direction to point
toward that endpoint. -/
theorem representativeOrientationPointsAway_eq_false
    (B : OccupiedLeftArcBranchAssignment T)
    (E : LeftSidedEndpointTrace h axis side) :
    B.representativeOrientationPointsAway h = false :=
  B.representativeOrientationPointsAway_of_endpointArcApproach h
    E.endpointArcApproach

end LeftSidedEndpointTrace


/-- Endpoint compatibility reduces to one geometric parity bit per vertex.
The bit may depend on the selected chart, but not on the incident arc. -/
theorem isSwitchCompatible_of_localGermParity
    (B : OccupiedLeftArcBranchAssignment T)
    (parity : T.chartCuts.cutPoints → Bool)
    (hparity : ∀ h : T.chartCuts.HalfEdge,
      B.representativeOrientationPointsAway h =
        ((T.chartCuts.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool.symm
          (T.chartCuts.incidentAtHalfEdge h) != parity h.1.1)) :
    B.IsSwitchCompatible := by
  intro h
  rw [hparity, hparity]
  rw [T.chartCuts.incidentArcEquivBool_symm_switchHalfEdge]
  rw [T.chartCuts.switchHalfEdge_vertex]
  generalize
    (T.chartCuts.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool.symm
      (T.chartCuts.incidentAtHalfEdge h) = b
  generalize parity h.1.1 = s
  cases b <;> cases s <;> rfl

/-- Geometric endpoint condition separated from the walk permutation: at each
actual cut vertex, exactly one incident half-edge points away in the
occupied-left orientation. -/
def HasUniqueOccupiedLeftOutgoingAtCutPoints
    (B : OccupiedLeftArcBranchAssignment T) : Prop :=
  ∀ v : T.chartCuts.cutPoints,
    ∃! h : T.chartCuts.HalfEdge,
      h.1.1 = v ∧ B.representativeOrientationPointsAway h = true

/-- Exactly one occupied-left outgoing branch at every degree-two cut vertex
is sufficient for switch compatibility.  No tangent collinearity is used. -/
theorem isSwitchCompatible_of_uniqueOccupiedLeftOutgoingAtCutPoints
    (B : OccupiedLeftArcBranchAssignment T)
    (hunique : B.HasUniqueOccupiedLeftOutgoingAtCutPoints) :
    B.IsSwitchCompatible := by
  intro h
  obtain ⟨g, hg, hgUnique⟩ := hunique h.1.1
  by_cases hh : B.representativeOrientationPointsAway h = true
  · have hhg : h = g := hgUnique h ⟨rfl, hh⟩
    have hswitchFalse :
        B.representativeOrientationPointsAway
            (T.chartCuts.switchHalfEdge h) = false := by
      cases hs :
          B.representativeOrientationPointsAway
            (T.chartCuts.switchHalfEdge h)
      · rfl
      · exfalso
        have hswitchg :
            T.chartCuts.switchHalfEdge h = g :=
          hgUnique (T.chartCuts.switchHalfEdge h)
            ⟨T.chartCuts.switchHalfEdge_vertex h, hs⟩
        apply T.chartCuts.switchHalfEdge_arc_ne h
        exact congrArg (fun z : T.chartCuts.HalfEdge => z.1.2)
          (hswitchg.trans hhg.symm)
    rw [hh, hswitchFalse]
    rfl
  · have hhFalse :
        B.representativeOrientationPointsAway h = false := by
      cases hb : B.representativeOrientationPointsAway h
      · rfl
      · exact (hh hb).elim
    have hvertex : g.1.1 = h.1.1 := hg.1
    rcases T.chartCuts.eq_or_eq_switchHalfEdge_of_vertex_eq
        (h := g) (g := h) hvertex with hgh | hgswitch
    · have : B.representativeOrientationPointsAway h = true := by
        rw [← hgh]
        exact hg.2
      exact (hh this).elim
    · have hswitchTrue :
          B.representativeOrientationPointsAway
              (T.chartCuts.switchHalfEdge h) = true := by
        rw [← hgswitch]
        exact hg.2
      rw [hhFalse, hswitchTrue]
      rfl

/-- It suffices to compare the two canonical local germs once at each cut
vertex. -/
theorem isSwitchCompatible_of_localGermPair
    (B : OccupiedLeftArcBranchAssignment T)
    (hpair : ∀ v : T.chartCuts.cutPoints,
      B.representativeOrientationPointsAway
          (T.chartCuts.localGermHalfEdge v true) =
        !B.representativeOrientationPointsAway
          (T.chartCuts.localGermHalfEdge v false)) :
    B.IsSwitchCompatible := by
  intro h
  let side :=
    (T.chartCuts.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool.symm
      (T.chartCuts.incidentAtHalfEdge h)
  have hh : h = T.chartCuts.localGermHalfEdge h.1.1 side := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hincident :
          T.chartCuts.incidentAtHalfEdge h =
            (T.chartCuts.cutPointCoreNeighborhood h.1.1).incidentArcEquivBool
              side := by
        apply
          (T.chartCuts.cutPointCoreNeighborhood
            h.1.1).incidentArcEquivBool.symm.injective
        simp only [side, Equiv.symm_apply_apply]
      exact congrArg Subtype.val hincident
  cases hs : side with
  | false =>
      rw [hh, T.chartCuts.switchHalfEdge_localGermHalfEdge]
      simpa only [hs, Bool.not_false] using hpair h.1.1
  | true =>
      rw [hh, T.chartCuts.switchHalfEdge_localGermHalfEdge]
      simpa only [hs, Bool.not_true, Bool.not_not] using
        (congrArg (fun b : Bool => !b) (hpair h.1.1)).symm

/-- Switch compatibility is exactly one occupied-left reversal per cut
vertex. -/
theorem isSwitchCompatible_iff_localGermPair
    (B : OccupiedLeftArcBranchAssignment T) :
    B.IsSwitchCompatible ↔
      ∀ v : T.chartCuts.cutPoints,
        B.representativeOrientationPointsAway
            (T.chartCuts.localGermHalfEdge v true) =
          !B.representativeOrientationPointsAway
            (T.chartCuts.localGermHalfEdge v false) := by
  constructor
  · intro hB v
    simpa only [T.chartCuts.switchHalfEdge_localGermHalfEdge,
      Bool.not_false] using
        hB (T.chartCuts.localGermHalfEdge v false)
  · exact B.isSwitchCompatible_of_localGermPair

/-- A geometric outgoing-germ witness at one cut vertex immediately gives the
two canonical local germs opposite endpoint orientations. -/
theorem localGermPair_of_localOutgoingGerm
    (B : OccupiedLeftArcBranchAssignment T)
    (v : T.chartCuts.cutPoints)
    (hlocal : ∃ outgoing : Bool,
      B.representativeOrientationPointsAway
          (T.chartCuts.localGermHalfEdge v outgoing) = true ∧
      B.representativeOrientationPointsAway
          (T.chartCuts.localGermHalfEdge v (!outgoing)) = false) :
    B.representativeOrientationPointsAway
        (T.chartCuts.localGermHalfEdge v true) =
      !B.representativeOrientationPointsAway
        (T.chartCuts.localGermHalfEdge v false) := by
  obtain ⟨outgoing, hout, hin⟩ := hlocal
  cases outgoing <;> simp_all

/-- A local geometric choice of exactly one outgoing occupied-left germ at
every cut vertex discharges the global switch condition. -/
theorem isSwitchCompatible_of_localOutgoingGerm
    (B : OccupiedLeftArcBranchAssignment T)
    (hlocal : ∀ v : T.chartCuts.cutPoints,
      ∃ outgoing : Bool,
        B.representativeOrientationPointsAway
            (T.chartCuts.localGermHalfEdge v outgoing) = true ∧
        B.representativeOrientationPointsAway
            (T.chartCuts.localGermHalfEdge v (!outgoing)) = false) :
    B.IsSwitchCompatible := by
  apply B.isSwitchCompatible_of_localGermPair
  intro v
  exact B.localGermPair_of_localOutgoingGerm v (hlocal v)

/-- Right-sided outgoing and left-sided incoming occupied-left traces at each
cut vertex discharge switch compatibility.  The axes and graph sides may
differ between the two incident germs. -/
theorem isSwitchCompatible_of_oneSidedEndpointTraces
    (B : OccupiedLeftArcBranchAssignment T)
    (htraces : (v : T.chartCuts.cutPoints) →
      Σ outgoing : Bool,
        (Σ axis : SpliceCutAxis,
          Σ side : SpliceGraphOccupiedSide,
            RightSidedEndpointTrace
              (T.chartCuts.localGermHalfEdge v outgoing) axis side) ×
        (Σ axis : SpliceCutAxis,
          Σ side : SpliceGraphOccupiedSide,
            LeftSidedEndpointTrace
              (T.chartCuts.localGermHalfEdge v (!outgoing)) axis side)) :
    B.IsSwitchCompatible := by
  apply B.isSwitchCompatible_of_localOutgoingGerm
  intro v
  obtain
    ⟨outgoing, ⟨axisOut, sideOut, hout⟩, ⟨axisIn, sideIn, hin⟩⟩ :=
      htraces v
  exact ⟨outgoing,
    hout.representativeOrientationPointsAway_eq_true B,
    hin.representativeOrientationPointsAway_eq_false B⟩

/-- Paired outgoing and incoming endpoint-path witnesses at every cut vertex
discharge switch compatibility without assuming any orientation Boolean. -/
theorem isSwitchCompatible_of_endpointArcTraces
    (B : OccupiedLeftArcBranchAssignment T)
    (htraces : (v : T.chartCuts.cutPoints) →
      Σ outgoing : Bool,
        EndpointArcContinuation T
            (T.chartCuts.localGermHalfEdge v outgoing) ×
          EndpointArcApproach T
            (T.chartCuts.localGermHalfEdge v (!outgoing))) :
    B.IsSwitchCompatible := by
  apply B.isSwitchCompatible_of_localOutgoingGerm
  intro v
  obtain ⟨outgoing, hout, hin⟩ := htraces v
  exact ⟨outgoing,
    B.representativeOrientationPointsAway_of_endpointArcContinuation
      (T.chartCuts.localGermHalfEdge v outgoing) hout,
    B.representativeOrientationPointsAway_of_endpointArcApproach
      (T.chartCuts.localGermHalfEdge v (!outgoing)) hin⟩

/-- If all cut vertices are ordinary smooth points, endpoint compatibility
reduces exactly to the one-sided trace-to-arc statement at each extracted
occupied-left regular trace. -/
theorem isSwitchCompatible_of_ordinaryCutPointTraces
    (B : OccupiedLeftArcBranchAssignment T)
    (hnonexceptional : ∀ v : T.chartCuts.cutPoints,
      v.1.1 ∉ T.exceptionalPoints)
    (htraceGerms : ∀ (v : T.chartCuts.cutPoints)
      (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide),
      OccupiedLeftRegularTrace axis side O v.1.1 →
        ∃ outgoing : Bool,
          B.representativeOrientationPointsAway
              (T.chartCuts.localGermHalfEdge v outgoing) = true ∧
          B.representativeOrientationPointsAway
              (T.chartCuts.localGermHalfEdge v (!outgoing)) = false) :
    B.IsSwitchCompatible := by
  apply B.isSwitchCompatible_of_localOutgoingGerm
  intro v
  obtain ⟨axis, side, ⟨trace⟩⟩ :=
    T.exists_regularTrace_away_exceptionalPoints v.1 (hnonexceptional v)
  exact htraceGerms v axis side trace

/-- Starting state whose next traversed arc uses the occupied-left direction.
The walk state itself is the incoming half-edge; `walkArcPath` traverses the
switched half-edge away from the common vertex. -/
noncomputable def occupiedLeftBoundaryLoopHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) : T.chartCuts.HalfEdge :=
  T.chartCuts.switchHalfEdge
    (B.representativeOrientedHalfEdge
      (T.chartCuts.boundaryLoopHalfEdge j).1.2)

@[simp] theorem boundaryLoopIndexOfHalfEdge_occupiedLeftBoundaryLoopHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) :
    T.chartCuts.boundaryLoopIndexOfHalfEdge
        (B.occupiedLeftBoundaryLoopHalfEdge j) = j := by
  rw [occupiedLeftBoundaryLoopHalfEdge,
    T.chartCuts.boundaryLoopIndexOfHalfEdge_switchHalfEdge]
  calc
    T.chartCuts.boundaryLoopIndexOfHalfEdge
        (B.representativeOrientedHalfEdge
          (T.chartCuts.boundaryLoopHalfEdge j).1.2) =
        T.chartCuts.arcBoundaryLoopIndex
          (B.representativeOrientedHalfEdge
            (T.chartCuts.boundaryLoopHalfEdge j).1.2).1.2 :=
      (T.chartCuts.arcBoundaryLoopIndex_eq_of_halfEdge_arc _).symm
    _ = T.chartCuts.arcBoundaryLoopIndex
          (T.chartCuts.boundaryLoopHalfEdge j).1.2 := by
      simp only [B.representativeOrientedHalfEdge_arc]
    _ = T.chartCuts.boundaryLoopIndexOfHalfEdge
          (T.chartCuts.boundaryLoopHalfEdge j) :=
      T.chartCuts.arcBoundaryLoopIndex_eq_of_halfEdge_arc _
    _ = j :=
      T.chartCuts.boundaryLoopIndexOfHalfEdge_boundaryLoopHalfEdge j

@[simp] theorem representativeOrientationPointsAway_occupiedLeftBoundaryLoopHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (j : T.chartCuts.BoundaryLoopIndex) :
    B.representativeOrientationPointsAway
        (B.occupiedLeftBoundaryLoopHalfEdge j) = false := by
  rw [occupiedLeftBoundaryLoopHalfEdge, hB]
  simp only [B.representativeOrientationPointsAway_orientedHalfEdge,
    Bool.not_true]

/-- Every state in the selected directed orbit is incoming in the
occupied-left convention. -/
theorem representativeOrientationPointsAway_iterate_occupiedLeftBoundaryLoopHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (j : T.chartCuts.BoundaryLoopIndex) (n : ℕ) :
    B.representativeOrientationPointsAway
        (((T.chartCuts.walkStep :
          T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
          (B.occupiedLeftBoundaryLoopHalfEdge j)) = false := by
  rw [B.representativeOrientationPointsAway_iterate_walkStep hB]
  exact B.representativeOrientationPointsAway_occupiedLeftBoundaryLoopHalfEdge
    hB j

/-- At every step, the half-edge actually traversed by `walkArcPath` is the
unique endpoint direction selected by the occupied-left arc orientation. -/
theorem switch_iterate_occupiedLeftBoundaryLoopHalfEdge_eq_oriented
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (j : T.chartCuts.BoundaryLoopIndex) (n : ℕ) :
    let state :=
      ((T.chartCuts.walkStep :
        T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
        (B.occupiedLeftBoundaryLoopHalfEdge j)
    T.chartCuts.switchHalfEdge state =
      B.representativeOrientedHalfEdge
        (T.chartCuts.switchHalfEdge state).1.2 := by
  dsimp only
  apply B.representativeOrientedHalfEdge_unique
  · rfl
  · rw [hB]
    simp only [
      B.representativeOrientationPointsAway_iterate_occupiedLeftBoundaryLoopHalfEdge
        hB j n,
      Bool.not_false]

/-- The selected closed walk based at the unique half-edge whose next
traversed arc follows the occupied-left direction.  Its combinatorial period
is unchanged; only the representative of the unoriented orbit is replaced. -/
noncomputable def occupiedLeftBoundaryGeometricWalkLoop
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) :
    T.chartCuts.GeometricWalkLoop (B.occupiedLeftBoundaryLoopHalfEdge j) :=
  T.chartCuts.minimalGeometricWalkLoop
    (B.occupiedLeftBoundaryLoopHalfEdge j)

@[simp] theorem occupiedLeftBoundaryGeometricWalkLoop_period
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) :
    (B.occupiedLeftBoundaryGeometricWalkLoop j).period =
      Function.minimalPeriod
        (T.chartCuts.walkStep :
          T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)
        (B.occupiedLeftBoundaryLoopHalfEdge j) :=
  rfl

/-- The occupied-left representative still traverses every compact arc in its
unoriented loop exactly once. -/
theorem existsUnique_lt_occupiedLeftPeriod_traversedArc_eq
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex)
    (e : T.chartCuts.ArcIndex)
    (he : T.chartCuts.arcBoundaryLoopIndex e = j) :
    ∃! n : ℕ,
      n < (B.occupiedLeftBoundaryGeometricWalkLoop j).period ∧
        (T.chartCuts.switchHalfEdge
          (((T.chartCuts.walkStep :
            T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
            (B.occupiedLeftBoundaryLoopHalfEdge j))).1.2 = e := by
  apply T.chartCuts.existsUnique_lt_minimalPeriod_traversedArc_eq
  exact he.trans
    (B.boundaryLoopIndexOfHalfEdge_occupiedLeftBoundaryLoopHalfEdge j).symm

/-- Replacing the arbitrary quotient representative by the occupied-left
representative preserves the complete selected loop image. -/
theorem occupiedLeftBoundaryGeometricWalkLoop_path_range_eq_iUnion_arcs
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) :
    Set.range (B.occupiedLeftBoundaryGeometricWalkLoop j).path =
      ⋃ e : {e : T.chartCuts.ArcIndex //
          T.chartCuts.arcBoundaryLoopIndex e = j},
        Set.range (T.chartCuts.finiteArcPathLR e.1) := by
  ext q
  change
    q ∈ Set.range
        (T.chartCuts.walkArcPathConcat
          (B.occupiedLeftBoundaryLoopHalfEdge j)
          (Function.minimalPeriod
            (T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)
            (B.occupiedLeftBoundaryLoopHalfEdge j))) ↔ _
  rw [T.chartCuts.mem_range_walkArcPathConcat_iff_of_pos
    (B.occupiedLeftBoundaryLoopHalfEdge j)
    (Function.minimalPeriod_pos_of_mem_periodicPts
      (T.chartCuts.walkStep_mem_periodicPts
        (B.occupiedLeftBoundaryLoopHalfEdge j))) q]
  constructor
  · rintro ⟨n, hn, hq⟩
    let e :=
      (T.chartCuts.switchHalfEdge
        (((T.chartCuts.walkStep :
          T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
          (B.occupiedLeftBoundaryLoopHalfEdge j))).1.2
    have he : T.chartCuts.arcBoundaryLoopIndex e = j := by
      exact
        (T.chartCuts.arcBoundaryLoopIndex_traversedArc
          (B.occupiedLeftBoundaryLoopHalfEdge j) n).trans
          (B.boundaryLoopIndexOfHalfEdge_occupiedLeftBoundaryLoopHalfEdge j)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨e, he⟩, ?_⟩
    rw [T.chartCuts.finiteArcPathLR_range]
    rw [← T.chartCuts.walkArcPath_range
      (((T.chartCuts.walkStep :
        T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
        (B.occupiedLeftBoundaryLoopHalfEdge j))]
    exact hq
  · intro hq
    obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hq
    have he :
        T.chartCuts.arcBoundaryLoopIndex e.1 =
          T.chartCuts.boundaryLoopIndexOfHalfEdge
            (B.occupiedLeftBoundaryLoopHalfEdge j) :=
      e.2.trans
        (B.boundaryLoopIndexOfHalfEdge_occupiedLeftBoundaryLoopHalfEdge j).symm
    obtain ⟨n, hn, harc⟩ :=
      T.chartCuts.exists_lt_minimalPeriod_traversedArc_eq
        (B.occupiedLeftBoundaryLoopHalfEdge j) e.1 he
    refine ⟨n, hn, ?_⟩
    rw [T.chartCuts.walkArcPath_range, harc,
      ← T.chartCuts.finiteArcPathLR_range]
    exact hqe

theorem occupiedLeftBoundaryGeometricWalkLoop_path_range_eq
    (B : OccupiedLeftArcBranchAssignment T)
    (j : T.chartCuts.BoundaryLoopIndex) :
    Set.range (B.occupiedLeftBoundaryGeometricWalkLoop j).path =
      Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path := by
  rw [B.occupiedLeftBoundaryGeometricWalkLoop_path_range_eq_iUnion_arcs,
    T.chartCuts.boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs]

/-- Under endpoint compatibility, every actual traversal piece of the selected
closed walk uses the unique occupied-left half-edge of its compact arc.  This
is the switch-then-cross convention: states are incoming, switched states are
outgoing. -/
theorem occupiedLeftBoundaryGeometricWalkLoop_traverses_orientedHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (j : T.chartCuts.BoundaryLoopIndex)
    (n : ℕ) :
    let state :=
      ((T.chartCuts.walkStep :
        T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
        (B.occupiedLeftBoundaryLoopHalfEdge j)
    T.chartCuts.switchHalfEdge state =
      B.representativeOrientedHalfEdge
        (T.chartCuts.switchHalfEdge state).1.2 :=
  B.switch_iterate_occupiedLeftBoundaryLoopHalfEdge_eq_oriented hB j n
end OccupiedLeftArcBranchAssignment
end CMVRelaxation
