/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVAEIntervalSections
import CMVFiniteCornerRepair
import CMVFigureFourSourceGeometry

/-!
# Preservation of genuine local boundary charts under AE selection

The selected representative repairs null punctures, but it cannot cross a
continuous strict graph boundary: every graph or unoccupied-side point has a
positive-volume complement patch in every ball.  The result is local and does
not assert that supplied charts exhaust the frontier.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology ContDiff

noncomputable section

namespace CMVRelaxation

/-- Membership in the selected representative depends only on the germ of the
carrier at the point. -/
theorem mem_aeOpenRepresentative_congr_nhds
    {A B : Set PlanePoint} {p : PlanePoint}
    (hAB : ∀ᶠ q in 𝓝 p, q ∈ A ↔ q ∈ B) :
    p ∈ aeOpenRepresentative A ↔ p ∈ aeOpenRepresentative B := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hAB
  constructor
  · rintro ⟨r, hr, hzero⟩
    refine ⟨min r delta, lt_min hr hdelta, measure_mono_null ?_ hzero⟩
    rintro q ⟨hqsmall, hqB⟩
    have hqr : q ∈ Metric.ball p r :=
      Metric.ball_subset_ball (min_le_left _ _) hqsmall
    have hqdelta : q ∈ Metric.ball p delta :=
      Metric.ball_subset_ball (min_le_right _ _) hqsmall
    exact ⟨hqr, fun hqA => hqB ((hball hqdelta).mp hqA)⟩
  · rintro ⟨r, hr, hzero⟩
    refine ⟨min r delta, lt_min hr hdelta, measure_mono_null ?_ hzero⟩
    rintro q ⟨hqsmall, hqA⟩
    have hqr : q ∈ Metric.ball p r :=
      Metric.ball_subset_ball (min_le_left _ _) hqsmall
    have hqdelta : q ∈ Metric.ball p delta :=
      Metric.ball_subset_ball (min_le_right _ _) hqsmall
    exact ⟨hqr, fun hqB => hqA ((hball hqdelta).mpr hqB)⟩

/-- Germ equality at one point gives selected-representative equality
throughout a smaller ball around that point. -/
theorem eventually_mem_aeOpenRepresentative_congr_nhds
    {A B : Set PlanePoint} {p : PlanePoint}
    (hAB : ∀ᶠ q in 𝓝 p, q ∈ A ↔ q ∈ B) :
    ∀ᶠ q in 𝓝 p,
      (q ∈ aeOpenRepresentative A ↔ q ∈ aeOpenRepresentative B) := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hAB
  have hhalf : 0 < delta / 2 := by positivity
  filter_upwards [Metric.ball_mem_nhds p hhalf] with q hq
  apply mem_aeOpenRepresentative_congr_nhds
  filter_upwards [Metric.ball_mem_nhds q hhalf] with z hz
  apply hball
  calc
    dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
    _ < delta / 2 + delta / 2 := add_lt_add hz hq
    _ = delta := by ring

/-- Every graph point and every point on the unoccupied side of a continuous
strict hypograph sees positive complement volume in every ball. -/
theorem strictHypograph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) {p : PlanePoint}
    (hp : ¬p.2 < f p.1) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball p r \ {q : PlanePoint | q.2 < f q.1}) := by
  have hple : f p.1 ≤ p.2 := le_of_not_gt hp
  let q : PlanePoint := (p.1, p.2 + r / 2)
  let V : Set PlanePoint :=
    Metric.ball p r ∩ {z : PlanePoint | f z.1 < z.2}
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [q, abs_of_pos hr]
    exact hr
  have hqext : f q.1 < q.2 := by
    dsimp [q]
    linarith
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt (hf.comp continuous_fst) continuous_snd)
  have hVpos : 0 < volume V :=
    hVopen.measure_pos volume ⟨q, hqball, hqext⟩
  have hVsub : V ⊆
      Metric.ball p r \ {q : PlanePoint | q.2 < f q.1} := by
    rintro z ⟨hzball, hzext⟩
    change f z.1 < z.2 at hzext
    refine ⟨hzball, ?_⟩
    intro hzgraph
    change z.2 < f z.1 at hzgraph
    exact (not_lt_of_ge hzgraph.le) hzext
  exact hVpos.trans_le (measure_mono hVsub)

/-- Graph-point specialization of the strict-hypograph complement estimate. -/
theorem strictHypograph_graph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < volume
      (Metric.ball ((x, f x) : PlanePoint) r \
        {q : PlanePoint | q.2 < f q.1}) := by
  exact strictHypograph_complement_volume_pos f hf (by simp) hr

/-- Every graph point and every point on the unoccupied side of a continuous
strict epigraph sees positive complement volume in every ball. -/
theorem strictEpigraph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) {p : PlanePoint}
    (hp : ¬f p.1 < p.2) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball p r \ {q : PlanePoint | f q.1 < q.2}) := by
  have hple : p.2 ≤ f p.1 := le_of_not_gt hp
  let q : PlanePoint := (p.1, p.2 - r / 2)
  let V : Set PlanePoint :=
    Metric.ball p r ∩ {z : PlanePoint | z.2 < f z.1}
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [q, abs_of_pos hr]
    exact hr
  have hqext : q.2 < f q.1 := by
    dsimp [q]
    linarith
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt continuous_snd (hf.comp continuous_fst))
  have hVpos : 0 < volume V :=
    hVopen.measure_pos volume ⟨q, hqball, hqext⟩
  have hVsub : V ⊆
      Metric.ball p r \ {q : PlanePoint | f q.1 < q.2} := by
    rintro z ⟨hzball, hzext⟩
    change z.2 < f z.1 at hzext
    refine ⟨hzball, ?_⟩
    intro hzgraph
    change f z.1 < z.2 at hzgraph
    exact (not_lt_of_ge hzgraph.le) hzext
  exact hVpos.trans_le (measure_mono hVsub)

/-- Graph-point specialization of the strict-epigraph complement estimate. -/
theorem strictEpigraph_graph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < volume
      (Metric.ball ((x, f x) : PlanePoint) r \
        {q : PlanePoint | f q.1 < q.2}) := by
  exact strictEpigraph_complement_volume_pos f hf (by simp) hr

/-- A continuous strict hypograph is fixed pointwise by AE selection. -/
theorem aeOpenRepresentative_strictHypograph
    (f : ℝ → ℝ) (hf : Continuous f) :
    aeOpenRepresentative {p : PlanePoint | p.2 < f p.1} =
      {p : PlanePoint | p.2 < f p.1} := by
  let U : Set PlanePoint := {p | p.2 < f p.1}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_snd (hf.comp continuous_fst)
  apply Set.Subset.antisymm
  · rintro p ⟨r, hr, hzero⟩
    by_contra hp
    have hpos : 0 < volume (Metric.ball p r \ U) := by
      exact strictHypograph_complement_volume_pos f hf (by simpa [U] using hp) hr
    exact hpos.ne' hzero
  · exact open_subset_aeOpenRepresentative_self hUopen

/-- A continuous strict epigraph is fixed pointwise by AE selection. -/
theorem aeOpenRepresentative_strictEpigraph
    (f : ℝ → ℝ) (hf : Continuous f) :
    aeOpenRepresentative {p : PlanePoint | f p.1 < p.2} =
      {p : PlanePoint | f p.1 < p.2} := by
  let U : Set PlanePoint := {p | f p.1 < p.2}
  have hUopen : IsOpen U :=
    isOpen_lt (hf.comp continuous_fst) continuous_snd
  apply Set.Subset.antisymm
  · rintro p ⟨r, hr, hzero⟩
    by_contra hp
    have hpos : 0 < volume (Metric.ball p r \ U) := by
      exact strictEpigraph_complement_volume_pos f hf (by simpa [U] using hp) hr
    exact hpos.ne' hzero
  · exact open_subset_aeOpenRepresentative_self hUopen

/-- A supplied continuous strict-hypograph germ is preserved at its base point.
The equality is local; no frontier equality follows. -/
theorem mem_aeOpenRepresentative_iff_of_eventually_strictHypograph
    {E U : Set PlanePoint} (hEU : E =ᵐ[volume] U)
    {p : PlanePoint} {f : ℝ → ℝ} (hf : Continuous f)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  let G : Set PlanePoint := {q | q.2 < f q.1}
  calc
    p ∈ aeOpenRepresentative U ↔ p ∈ aeOpenRepresentative G :=
      mem_aeOpenRepresentative_congr_nhds hlocal
    _ ↔ p ∈ G := by rw [aeOpenRepresentative_strictHypograph f hf]
    _ ↔ p ∈ U := hlocal.self_of_nhds.symm

/-- A supplied continuous strict-epigraph germ is preserved at its base point. -/
theorem mem_aeOpenRepresentative_iff_of_eventually_strictEpigraph
    {E U : Set PlanePoint} (hEU : E =ᵐ[volume] U)
    {p : PlanePoint} {f : ℝ → ℝ} (hf : Continuous f)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.1 < q.2) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  let G : Set PlanePoint := {q | f q.1 < q.2}
  calc
    p ∈ aeOpenRepresentative U ↔ p ∈ aeOpenRepresentative G :=
      mem_aeOpenRepresentative_congr_nhds hlocal
    _ ↔ p ∈ G := by rw [aeOpenRepresentative_strictEpigraph f hf]
    _ ↔ p ∈ U := hlocal.self_of_nhds.symm

/-- Every graph point and every point on the unoccupied right side of a
continuous graph over the second coordinate sees positive complement volume. -/
theorem strictLeftGraph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) {p : PlanePoint}
    (hp : ¬p.1 < f p.2) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball p r \ {q : PlanePoint | q.1 < f q.2}) := by
  have hple : f p.2 ≤ p.1 := le_of_not_gt hp
  let q : PlanePoint := (p.1 + r / 2, p.2)
  let V : Set PlanePoint :=
    Metric.ball p r ∩ {z : PlanePoint | f z.2 < z.1}
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [q, abs_of_pos hr]
    exact hr
  have hqext : f q.2 < q.1 := by
    dsimp [q]
    linarith
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt (hf.comp continuous_snd) continuous_fst)
  have hVpos : 0 < volume V :=
    hVopen.measure_pos volume ⟨q, hqball, hqext⟩
  have hVsub : V ⊆
      Metric.ball p r \ {q : PlanePoint | q.1 < f q.2} := by
    rintro z ⟨hzball, hzext⟩
    change f z.2 < z.1 at hzext
    refine ⟨hzball, ?_⟩
    intro hzgraph
    change z.1 < f z.2 at hzgraph
    exact (not_lt_of_ge hzgraph.le) hzext
  exact hVpos.trans_le (measure_mono hVsub)

/-- Every graph point and every point on the unoccupied left side of a
continuous graph over the second coordinate sees positive complement volume. -/
theorem strictRightGraph_complement_volume_pos
    (f : ℝ → ℝ) (hf : Continuous f) {p : PlanePoint}
    (hp : ¬f p.2 < p.1) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball p r \ {q : PlanePoint | f q.2 < q.1}) := by
  have hple : p.1 ≤ f p.2 := le_of_not_gt hp
  let q : PlanePoint := (p.1 - r / 2, p.2)
  let V : Set PlanePoint :=
    Metric.ball p r ∩ {z : PlanePoint | z.1 < f z.2}
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp [q, abs_of_pos hr]
    exact hr
  have hqext : q.1 < f q.2 := by
    dsimp [q]
    linarith
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt continuous_fst (hf.comp continuous_snd))
  have hVpos : 0 < volume V :=
    hVopen.measure_pos volume ⟨q, hqball, hqext⟩
  have hVsub : V ⊆
      Metric.ball p r \ {q : PlanePoint | f q.2 < q.1} := by
    rintro z ⟨hzball, hzext⟩
    change z.1 < f z.2 at hzext
    refine ⟨hzball, ?_⟩
    intro hzgraph
    change f z.2 < z.1 at hzgraph
    exact (not_lt_of_ge hzgraph.le) hzext
  exact hVpos.trans_le (measure_mono hVsub)

/-- A continuous strict left graph is fixed pointwise by AE selection. -/
theorem aeOpenRepresentative_strictLeftGraph
    (f : ℝ → ℝ) (hf : Continuous f) :
    aeOpenRepresentative {p : PlanePoint | p.1 < f p.2} =
      {p : PlanePoint | p.1 < f p.2} := by
  let U : Set PlanePoint := {p | p.1 < f p.2}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_fst (hf.comp continuous_snd)
  apply Set.Subset.antisymm
  · rintro p ⟨r, hr, hzero⟩
    by_contra hp
    have hpos : 0 < volume (Metric.ball p r \ U) := by
      exact strictLeftGraph_complement_volume_pos f hf
        (by simpa [U] using hp) hr
    exact hpos.ne' hzero
  · exact open_subset_aeOpenRepresentative_self hUopen

/-- A continuous strict right graph is fixed pointwise by AE selection. -/
theorem aeOpenRepresentative_strictRightGraph
    (f : ℝ → ℝ) (hf : Continuous f) :
    aeOpenRepresentative {p : PlanePoint | f p.2 < p.1} =
      {p : PlanePoint | f p.2 < p.1} := by
  let U : Set PlanePoint := {p | f p.2 < p.1}
  have hUopen : IsOpen U :=
    isOpen_lt (hf.comp continuous_snd) continuous_fst
  apply Set.Subset.antisymm
  · rintro p ⟨r, hr, hzero⟩
    by_contra hp
    have hpos : 0 < volume (Metric.ball p r \ U) := by
      exact strictRightGraph_complement_volume_pos f hf
        (by simpa [U] using hp) hr
    exact hpos.ne' hzero
  · exact open_subset_aeOpenRepresentative_self hUopen

/-- A supplied continuous strict-left-graph germ is preserved at its base
point. -/
theorem mem_aeOpenRepresentative_iff_of_eventually_strictLeftGraph
    {E U : Set PlanePoint} (hEU : E =ᵐ[volume] U)
    {p : PlanePoint} {f : ℝ → ℝ} (hf : Continuous f)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.1 < f q.2) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  let G : Set PlanePoint := {q | q.1 < f q.2}
  calc
    p ∈ aeOpenRepresentative U ↔ p ∈ aeOpenRepresentative G :=
      mem_aeOpenRepresentative_congr_nhds hlocal
    _ ↔ p ∈ G := by rw [aeOpenRepresentative_strictLeftGraph f hf]
    _ ↔ p ∈ U := hlocal.self_of_nhds.symm

/-- A supplied continuous strict-right-graph germ is preserved at its base
point. -/
theorem mem_aeOpenRepresentative_iff_of_eventually_strictRightGraph
    {E U : Set PlanePoint} (hEU : E =ᵐ[volume] U)
    {p : PlanePoint} {f : ℝ → ℝ} (hf : Continuous f)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.2 < q.1) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  let G : Set PlanePoint := {q | f q.2 < q.1}
  calc
    p ∈ aeOpenRepresentative U ↔ p ∈ aeOpenRepresentative G :=
      mem_aeOpenRepresentative_congr_nhds hlocal
    _ ↔ p ∈ G := by rw [aeOpenRepresentative_strictRightGraph f hf]
    _ ↔ p ∈ U := hlocal.self_of_nhds.symm

namespace LocalChartPreservation

open FiniteJunctionRepair

/-- A genuine continuous occupied-side graph germ.  It records only one local
membership model and does not assert that such germs cover any frontier. -/
def HasContinuousGraphGermOnSide
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (U : Set PlanePoint) (p : PlanePoint) : Prop :=
  ∃ f : ℝ → ℝ, Continuous f ∧
    match axis, side with
    | .vertical, .negative =>
        ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1
    | .vertical, .positive =>
        ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.1 < q.2
    | .horizontal, .negative =>
        ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.1 < f q.2
    | .horizontal, .positive =>
        ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.2 < q.1

/-- A vertical continuous graph germ through a frontier point actually passes
through that point.  This is the boundary-base fact retained after forgetting
the oriented smooth chart data. -/
theorem HasContinuousGraphGermOnSide.exists_vertical_graph_eq_base
    {side : SpliceGraphOccupiedSide} {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasContinuousGraphGermOnSide .vertical side U p)
    (hp : p ∈ frontier U) :
    ∃ f : ℝ → ℝ, Continuous f ∧ f p.1 = p.2 ∧
      match side with
      | .negative => ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1
      | .positive => ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.1 < q.2 := by
  rcases germ with ⟨f, hf, hlocal⟩
  cases side with
  | negative =>
      have hlocal' : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1 := by
        simpa using hlocal
      let G : Set PlanePoint := {q | q.2 < f q.1}
      obtain ⟨V, hVsub, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hlocal'
      have hUV : U ∩ V = G ∩ V := by
        ext q
        simp only [mem_inter_iff]
        constructor
        · intro hq
          exact ⟨(hVsub hq.2).mp hq.1, hq.2⟩
        · intro hq
          exact ⟨(hVsub hq.2).mpr hq.1, hq.2⟩
      have hfrontier : frontier U ∩ V = frontier G ∩ V :=
        frontier_inter_eq_of_inter_open_eq hVopen hUV
      have hpPair : p ∈ frontier U ∩ V := ⟨hp, hpV⟩
      rw [hfrontier] at hpPair
      have hpG : p ∈ frontier G := hpPair.1
      let g : PlanePoint → ℝ := fun q => q.2 - f q.1
      have hg : ContinuousAt g p :=
        continuousAt_snd.sub (hf.continuousAt.comp continuousAt_fst)
      have hpzero : g p = 0 := by
        apply eq_zero_of_mem_frontier_lt_of_continuousAt hg
        simpa only [G, g, sub_lt_zero] using hpG
      refine ⟨f, hf, ?_, ?_⟩
      · dsimp only [g] at hpzero
        linarith
      · simpa using hlocal'
  | positive =>
      have hlocal' : ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.1 < q.2 := by
        simpa using hlocal
      let G : Set PlanePoint := {q | f q.1 < q.2}
      obtain ⟨V, hVsub, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hlocal'
      have hUV : U ∩ V = G ∩ V := by
        ext q
        simp only [mem_inter_iff]
        constructor
        · intro hq
          exact ⟨(hVsub hq.2).mp hq.1, hq.2⟩
        · intro hq
          exact ⟨(hVsub hq.2).mpr hq.1, hq.2⟩
      have hfrontier : frontier U ∩ V = frontier G ∩ V :=
        frontier_inter_eq_of_inter_open_eq hVopen hUV
      have hpPair : p ∈ frontier U ∩ V := ⟨hp, hpV⟩
      rw [hfrontier] at hpPair
      have hpG : p ∈ frontier G := hpPair.1
      let g : PlanePoint → ℝ := fun q => f q.1 - q.2
      have hg : ContinuousAt g p :=
        (hf.continuousAt.comp continuousAt_fst).sub continuousAt_snd
      have hpzero : g p = 0 := by
        apply eq_zero_of_mem_frontier_lt_of_continuousAt hg
        simpa only [G, g, sub_lt_zero] using hpG
      refine ⟨f, hf, ?_, ?_⟩
      · dsimp only [g] at hpzero
        linarith
      · simpa using hlocal'

/-- On a justified smaller neighborhood, a supplied continuous graph chart
models the selected representative by the same strict occupied side. -/
theorem HasContinuousGraphGermOnSide.eventually_mem_aeOpenRepresentative_iff
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {E U : Set PlanePoint} {p : PlanePoint}
    (chart : HasContinuousGraphGermOnSide axis side U p)
    (hEU : E =ᵐ[volume] U) :
    ∀ᶠ q in 𝓝 p, (q ∈ aeOpenRepresentative E ↔ q ∈ U) := by
  rcases chart with ⟨f, hf, hlocal⟩
  rw [aeOpenRepresentative_congr_ae hEU]
  cases axis <;> cases side
  · let G : Set PlanePoint := {q | q.2 < f q.1}
    have hselected :=
      eventually_mem_aeOpenRepresentative_congr_nhds hlocal
    filter_upwards [hselected, hlocal] with q hq hqU
    calc
      q ∈ aeOpenRepresentative U ↔ q ∈ aeOpenRepresentative G := hq
      _ ↔ q ∈ G := by rw [aeOpenRepresentative_strictHypograph f hf]
      _ ↔ q ∈ U := hqU.symm
  · let G : Set PlanePoint := {q | f q.1 < q.2}
    have hselected :=
      eventually_mem_aeOpenRepresentative_congr_nhds hlocal
    filter_upwards [hselected, hlocal] with q hq hqU
    calc
      q ∈ aeOpenRepresentative U ↔ q ∈ aeOpenRepresentative G := hq
      _ ↔ q ∈ G := by rw [aeOpenRepresentative_strictEpigraph f hf]
      _ ↔ q ∈ U := hqU.symm
  · let G : Set PlanePoint := {q | q.1 < f q.2}
    have hselected :=
      eventually_mem_aeOpenRepresentative_congr_nhds hlocal
    filter_upwards [hselected, hlocal] with q hq hqU
    calc
      q ∈ aeOpenRepresentative U ↔ q ∈ aeOpenRepresentative G := hq
      _ ↔ q ∈ G := by rw [aeOpenRepresentative_strictLeftGraph f hf]
      _ ↔ q ∈ U := hqU.symm
  · let G : Set PlanePoint := {q | f q.2 < q.1}
    have hselected :=
      eventually_mem_aeOpenRepresentative_congr_nhds hlocal
    filter_upwards [hselected, hlocal] with q hq hqU
    calc
      q ∈ aeOpenRepresentative U ↔ q ∈ aeOpenRepresentative G := hq
      _ ↔ q ∈ G := by rw [aeOpenRepresentative_strictRightGraph f hf]
      _ ↔ q ∈ U := hqU.symm

/-- The same continuous graph germ, with the same orientation and occupied
side, is a chart of the selected representative. -/
theorem HasContinuousGraphGermOnSide.selected
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {E U : Set PlanePoint} {p : PlanePoint}
    (chart : HasContinuousGraphGermOnSide axis side U p)
    (hEU : E =ᵐ[volume] U) :
    HasContinuousGraphGermOnSide axis side
      (aeOpenRepresentative E) p := by
  have hselected := chart.eventually_mem_aeOpenRepresentative_iff hEU
  rcases chart with ⟨f, hf, hlocal⟩
  cases axis <;> cases side
  all_goals
    refine ⟨f, hf, ?_⟩
    filter_upwards [hselected, hlocal] with q hqSelected hqGraph
    exact hqSelected.trans hqGraph

/-- Every supplied genuine continuous graph germ is preserved pointwise by the
AE-invariant representative. -/
theorem HasContinuousGraphGermOnSide.mem_aeOpenRepresentative_iff
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {E U : Set PlanePoint} {p : PlanePoint}
    (chart : HasContinuousGraphGermOnSide axis side U p)
    (hEU : E =ᵐ[volume] U) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U := by
  rcases chart with ⟨f, hf, hlocal⟩
  cases axis <;> cases side
  · exact mem_aeOpenRepresentative_iff_of_eventually_strictHypograph
      hEU hf hlocal
  · exact mem_aeOpenRepresentative_iff_of_eventually_strictEpigraph
      hEU hf hlocal
  · exact mem_aeOpenRepresentative_iff_of_eventually_strictLeftGraph
      hEU hf hlocal
  · exact mem_aeOpenRepresentative_iff_of_eventually_strictRightGraph
      hEU hf hlocal

/-- A smooth oriented germ from the existing regular-boundary interface forgets
to the narrower continuous graph germ used by selection. -/
theorem continuousGraphGerm_of_orientedSmooth
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p) :
    HasContinuousGraphGermOnSide axis side U p := by
  cases axis <;> cases side
  · obtain ⟨f, hf, _hfp, hlocal⟩ :=
      germ.exists_eventually_occupiedGraphDomain
    exact ⟨f, hf.continuous, hlocal⟩
  · obtain ⟨f, hf, _hfp, hlocal⟩ :=
      germ.exists_eventually_occupiedGraphDomain
    exact ⟨f, hf.continuous, hlocal⟩
  · obtain ⟨f, hf, _hfp, hlocal⟩ :=
      germ.exists_eventually_occupiedGraphDomain
    exact ⟨f, hf.continuous, hlocal⟩
  · obtain ⟨f, hf, _hfp, hlocal⟩ :=
      germ.exists_eventually_occupiedGraphDomain
    exact ⟨f, hf.continuous, hlocal⟩

/-- Existing regular oriented graph germs therefore survive selection without
any frontier-identification premise. -/
theorem mem_aeOpenRepresentative_iff_of_orientedSmoothGraphGerm
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {E U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p)
    (hEU : E =ᵐ[volume] U) :
    p ∈ aeOpenRepresentative E ↔ p ∈ U :=
  (continuousGraphGerm_of_orientedSmooth germ).mem_aeOpenRepresentative_iff hEU

/-- A source-local oriented smooth graph germ survives passage to the selected
representative with the same defining function, graph, coordinate direction,
and occupied side.  Only its local carrier-membership equivalence changes. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.selected
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {E U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p)
    (hEU : E =ᵐ[volume] U) :
    HasOrientedSmoothBoundaryGraphGermOnSide axis side
      (aeOpenRepresentative E) p := by
  have hselected :=
    (continuousGraphGerm_of_orientedSmooth germ)
      |>.eventually_mem_aeOpenRepresentative_iff hEU
  cases axis <;> cases side <;>
    rcases germ with
      ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hside⟩
  all_goals
    refine ⟨g, φ, hg, htransverse, hφ, hφp, ?_, hside⟩
    filter_upwards [hselected, hlocal] with q hqSelected hqLocal
    exact ⟨hqSelected.trans hqLocal.1, hqLocal.2⟩


/-! ## Regular-circle specializations -/

open CMVFigureFour

/-- Signed defining function underlying one fixed orientation of the source
circle-side interface. -/
def signedCircleValue (side : CircleSide) (center : PlanePoint)
    (radius : ℝ) (q : PlanePoint) : ℝ :=
  side.sign * circleValue center radius q

theorem contDiff_signedCircleValue (side : CircleSide) (center : PlanePoint)
    (radius : ℝ) :
    ContDiff ℝ ∞ (signedCircleValue side center radius) := by
  unfold signedCircleValue circleValue
  fun_prop

/-- The signed circle gradient in the second coordinate. -/
theorem fderiv_signedCircleValue_snd
    (side : CircleSide) (center p : PlanePoint) (radius : ℝ) :
    fderiv ℝ (signedCircleValue side center radius) p (0, 1) =
      side.sign * (2 * (p.2 - center.2)) := by
  let g : PlanePoint → ℝ := signedCircleValue side center radius
  have hg : DifferentiableAt ℝ g p :=
    (contDiff_signedCircleValue side center radius).differentiable
      (by simp) p
  have hline :
      HasDerivAt (fun y : ℝ => ((p.1, y) : PlanePoint)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt p.2 hline
  have heq : deriv (fun y : ℝ => g (p.1, y)) p.2 =
      fderiv ℝ g p (0, 1) := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [← heq]
  have hconst :
      HasDerivAt (fun _y : ℝ => (p.1 - center.1) ^ 2) 0 p.2 :=
    hasDerivAt_const p.2 _
  have hy : HasDerivAt (fun y : ℝ => y - center.2) 1 p.2 :=
    (hasDerivAt_id p.2).sub_const center.2
  have hraw :=
    (hconst.add (hy.pow 2)).sub_const (radius ^ 2) |>.const_mul side.sign
  have hcalc : HasDerivAt (fun y : ℝ => g (p.1, y))
      (side.sign * (2 * (p.2 - center.2))) p.2 := by
    convert hraw using 1 <;> first | rfl | simp
  exact hcalc.deriv

/-- The signed circle gradient in the first coordinate. -/
theorem fderiv_signedCircleValue_fst
    (side : CircleSide) (center p : PlanePoint) (radius : ℝ) :
    fderiv ℝ (signedCircleValue side center radius) p (1, 0) =
      side.sign * (2 * (p.1 - center.1)) := by
  let g : PlanePoint → ℝ := signedCircleValue side center radius
  have hg : DifferentiableAt ℝ g p :=
    (contDiff_signedCircleValue side center radius).differentiable
      (by simp) p
  have hline :
      HasDerivAt (fun x : ℝ => ((x, p.2) : PlanePoint)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt p.1 hline
  have heq : deriv (fun x : ℝ => g (x, p.2)) p.1 =
      fderiv ℝ g p (1, 0) := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [← heq]
  have hx : HasDerivAt (fun x : ℝ => x - center.1) 1 p.1 :=
    (hasDerivAt_id p.1).sub_const center.1
  have hconst :
      HasDerivAt (fun _x : ℝ => (p.2 - center.2) ^ 2) 0 p.1 :=
    hasDerivAt_const p.1 _
  have hraw :=
    ((hx.pow 2).add hconst).sub_const (radius ^ 2) |>.const_mul side.sign
  have hcalc : HasDerivAt (fun x : ℝ => g (x, p.2))
      (side.sign * (2 * (p.1 - center.1))) p.1 := by
    convert hraw using 1 <;> first | rfl | simp
  exact hcalc.deriv

private theorem circleSide_sign_ne_zero (side : CircleSide) :
    side.sign ≠ 0 := by
  cases side <;> norm_num [CircleSide.sign]

/-- A source-local circle side exposes the genuine oriented smooth vertical
graph germ used internally by the continuous-chart API. -/
theorem exists_verticalOrientedSmoothGraphGerm_of_locallyOneSided_circle
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (hy : p.2 ≠ center.2)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide .vertical graphSide U p := by
  rcases hlocal with ⟨circleSide, V, hVopen, hpV, hUV⟩
  let g : PlanePoint → ℝ :=
    signedCircleValue circleSide center radius
  have hg : ContDiff ℝ ∞ g := contDiff_signedCircleValue _ _ _
  have hgp : g p = 0 := by
    simp [g, signedCircleValue, hcircle]
  have htrans : fderiv ℝ g p (0, 1) ≠ 0 := by
    rw [fderiv_signedCircleValue_snd]
    exact mul_ne_zero (circleSide_sign_ne_zero circleSide)
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hy))
  obtain ⟨phi, hphi, hphip, hzero⟩ :=
    exists_contDiff_infty_implicitGraph_of_contDiffOn
      hVopen hpV hg.contDiffOn htrans
  have hmodel : ∀ᶠ q in 𝓝 p,
      (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ phi q.1 = q.2) := by
    filter_upwards [hVopen.mem_nhds hpV, hzero] with q hqV hqzero
    constructor
    · simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, hqV,
        and_true, true_and, g, signedCircleValue] using Set.ext_iff.mp hUV q
    · simpa only [hgp] using hqzero
  have hgat : ContDiffAt ℝ ∞ g p := hg.contDiffAt
  rcases lt_or_gt_of_ne htrans with hneg | hpos
  · exact ⟨.positive, g, phi, hgat, htrans, hphi, hphip, hmodel, hneg⟩
  · exact ⟨.negative, g, phi, hgat, htrans, hphi, hphip, hmodel, hpos⟩

/-- A source-local circle side is a genuine graph over the first coordinate
when the second gradient component is nonzero.  Both occupied sides are kept:
the derivative sign selects the existing graph-side label. -/
theorem exists_verticalGraphGerm_of_locallyOneSided_circle
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (hy : p.2 ≠ center.2)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical graphSide U p := by
  obtain ⟨graphSide, germ⟩ :=
    exists_verticalOrientedSmoothGraphGerm_of_locallyOneSided_circle
      hcircle hy hlocal
  exact ⟨graphSide, continuousGraphGerm_of_orientedSmooth germ⟩

/-- A source-local circle side exposes the genuine oriented smooth horizontal
graph germ used internally at vertical circle tangencies. -/
theorem exists_horizontalOrientedSmoothGraphGerm_of_locallyOneSided_circle
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (hx : p.1 ≠ center.1)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide .horizontal graphSide U p := by
  rcases hlocal with ⟨circleSide, V, hVopen, hpV, hUV⟩
  let g : PlanePoint → ℝ :=
    signedCircleValue circleSide center radius
  have hg : ContDiff ℝ ∞ g := contDiff_signedCircleValue _ _ _
  have hgp : g p = 0 := by
    simp [g, signedCircleValue, hcircle]
  have htrans : fderiv ℝ g p (1, 0) ≠ 0 := by
    rw [fderiv_signedCircleValue_fst]
    exact mul_ne_zero (circleSide_sign_ne_zero circleSide)
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx))
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  let u : PlanePoint := (p.2, p.1)
  let gs : PlanePoint → ℝ := g ∘ e
  have hgs : ContDiff ℝ ∞ gs := hg.comp e.contDiff
  have hgsderiv :
      HasFDerivAt gs
        (fderiv ℝ g p ∘L (e : PlanePoint →L[ℝ] PlanePoint)) u := by
    have heup : e u = p := by
      apply Prod.ext <;> rfl
    simpa only [gs, heup] using
      hg.differentiable (by simp) p |>.hasFDerivAt.comp u e.hasFDerivAt
  have hgsTrans : fderiv ℝ gs u (0, 1) ≠ 0 := by
    simpa [hgsderiv.fderiv, e, u,
      ContinuousLinearMap.comp_apply] using htrans
  obtain ⟨phi, hphi, hphiu, hzeroSwap⟩ :=
    exists_contDiff_infty_implicitGraph_of_contDiffOn
      isOpen_univ (mem_univ u) hgs.contDiffOn hgsTrans
  have hzero :
      ∀ᶠ q in 𝓝 p, g q = g p ↔ phi q.2 = q.1 := by
    have hs := e.continuousAt.tendsto.eventually hzeroSwap
    simpa [gs, e, u] using hs
  have hmodel : ∀ᶠ q in 𝓝 p,
      (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ phi q.2 = q.1) := by
    filter_upwards [hVopen.mem_nhds hpV, hzero] with q hqV hqzero
    constructor
    · simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, hqV,
        and_true, true_and, g, signedCircleValue] using Set.ext_iff.mp hUV q
    · simpa only [hgp] using hqzero
  have hgat : ContDiffAt ℝ ∞ g p := hg.contDiffAt
  rcases lt_or_gt_of_ne htrans with hneg | hpos
  · exact ⟨.positive, g, phi, hgat, htrans, hphi,
      by simpa only [u] using hphiu, hmodel, hneg⟩
  · exact ⟨.negative, g, phi, hgat, htrans, hphi,
      by simpa only [u] using hphiu, hmodel, hpos⟩

/-- A source-local circle side is a genuine graph over the second coordinate
when the first gradient component is nonzero.  This is the valid orientation
at a vertical circle tangency. -/
theorem exists_horizontalGraphGerm_of_locallyOneSided_circle
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hcircle : circleValue center radius p = 0)
    (hx : p.1 ≠ center.1)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .horizontal graphSide U p := by
  obtain ⟨graphSide, germ⟩ :=
    exists_horizontalOrientedSmoothGraphGerm_of_locallyOneSided_circle
      hcircle hx hlocal
  exact ⟨graphSide, continuousGraphGerm_of_orientedSmooth germ⟩

/-- Every positive-radius regular circle point admits at least one valid graph
orientation.  The conclusion does not claim a chart at a source junction where
`LocallyOneSided` is unavailable. -/
theorem exists_graphGerm_of_locallyOneSided_circle
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius)
    (hcircle : circleValue center radius p = 0)
    (hlocal : LocallyOneSided U center radius p) :
    (∃ graphSide : SpliceGraphOccupiedSide,
        HasContinuousGraphGermOnSide .vertical graphSide U p) ∨
      ∃ graphSide : SpliceGraphOccupiedSide,
        HasContinuousGraphGermOnSide .horizontal graphSide U p := by
  by_cases hy : p.2 ≠ center.2
  · exact Or.inl
      (exists_verticalGraphGerm_of_locallyOneSided_circle hcircle hy hlocal)
  · have hyEq : p.2 = center.2 := not_ne_iff.mp hy
    have hx : p.1 ≠ center.1 := by
      intro hxEq
      have hsq : radius ^ 2 = 0 := by
        unfold circleValue at hcircle
        rw [hxEq, hyEq] at hcircle
        simpa using hcircle.symm
      exact (sq_pos_of_pos hradius).ne' hsq
    exact Or.inr
      (exists_horizontalGraphGerm_of_locallyOneSided_circle hcircle hx hlocal)

/-- At a horizontal circle tangency, nonzero radius forces the second gradient
component to be nonzero, so the graph over the first coordinate is valid. -/
theorem exists_verticalGraphGerm_at_horizontal_circle_tangency
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius)
    (hcircle : circleValue center radius p = 0)
    (hxEq : p.1 = center.1)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical graphSide U p := by
  have hy : p.2 ≠ center.2 := by
    intro hyEq
    have hsq : radius ^ 2 = 0 := by
      unfold circleValue at hcircle
      rw [hxEq, hyEq] at hcircle
      simpa using hcircle.symm
    exact (sq_pos_of_pos hradius).ne' hsq
  exact exists_verticalGraphGerm_of_locallyOneSided_circle hcircle hy hlocal

/-- At a vertical circle tangency, nonzero radius forces the first gradient
component to be nonzero, so the graph over the second coordinate is valid. -/
theorem exists_horizontalGraphGerm_at_vertical_circle_tangency
    {U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hradius : 0 < radius)
    (hcircle : circleValue center radius p = 0)
    (hyEq : p.2 = center.2)
    (hlocal : LocallyOneSided U center radius p) :
    ∃ graphSide : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .horizontal graphSide U p := by
  have hx : p.1 ≠ center.1 := by
    intro hxEq
    have hsq : radius ^ 2 = 0 := by
      unfold circleValue at hcircle
      rw [hxEq, hyEq] at hcircle
      simpa using hcircle.symm
    exact (sq_pos_of_pos hradius).ne' hsq
  exact exists_horizontalGraphGerm_of_locallyOneSided_circle hcircle hx hlocal

/-! ## Conditional source-facing integration -/

/-- Selection simultaneously preserves the supplied source semantics, upgrades
the explicitly premised AE interval fibers at every height, and transports only
the local continuous charts supplied by the caller.  No atlas coverage,
frontier equality, contact finiteness, symmetry, or minimizer regularity is
concluded. -/
theorem selectedSource_localChart_contract
    (lam : ℝ) {E U : Set PlanePoint}
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hEU : E =ᵐ[volume] U)
    (hsections : HasAEIntervalHorizontalSections E)
    {ι : Type*}
    (axis : ι → SpliceCutAxis)
    (side : ι → SpliceGraphOccupiedSide)
    (point : ι → PlanePoint)
    (charts : ∀ i, HasContinuousGraphGermOnSide
      (axis i) (side i) U (point i)) :
    let O := aeOpenRepresentative E
    IsOpen O ∧
      O =ᵐ[volume] E ∧
      _root_.WeightedArea lam O = _root_.WeightedArea lam E ∧
      relaxedPerimeter lam O = relaxedPerimeter lam E ∧
      ((relaxedSourceSemantics lam).IsAdmissible O ↔
        (relaxedSourceSemantics lam).IsAdmissible E) ∧
      ((relaxedSourceSemantics lam).IsMinimizer O ↔
        (relaxedSourceSemantics lam).IsMinimizer E) ∧
      (∀ y : ℝ,
        CMVSourceClassification.horizontalSection O y = ∅ ∨
          ∃ a b : ℝ, a < b ∧
            CMVSourceClassification.horizontalSection O y = Ioo a b) ∧
      ∀ i, HasContinuousGraphGermOnSide
        (axis i) (side i) O (point i) := by
  dsimp only
  refine ⟨isOpen_aeOpenRepresentative E,
    aeOpenRepresentative_ae_eq hUopen hEU,
    weightedArea_aeOpenRepresentative lam hUopen hEU,
    relaxedPerimeter_aeOpenRepresentative lam hUopen hEU,
    relaxedSourceSemantics_isAdmissible_aeOpenRepresentative_iff
      lam hUopen hEU,
    relaxedSourceSemantics_isMinimizer_aeOpenRepresentative_iff
      lam hUopen hEU, ?_, ?_⟩
  · intro y
    exact horizontalSection_empty_or_Ioo_aeOpenRepresentative
      hUopen hEU hUbounded hsections y
  · intro i
    exact (charts i).selected hEU
end LocalChartPreservation
end CMVRelaxation
