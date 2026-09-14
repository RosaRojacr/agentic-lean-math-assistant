/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSmoothAmbientTransport
import CMVTwoPatchStationarity

/-!
# Smooth ambient realization of graph variations

Smooth compactly supported scalar graph tests are extended to compactly
supported smooth vertical vector fields inside the protected constant-density
tubes.  Small perturbations of the identity then give actual global smooth
ambient equivalences and map each active graph literally to its prescribed
vertical variation.
-/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVTwoPatchGraphVariation

open CMVRelaxation

namespace GraphPatch

/-- Open version of the protected graph tube.  The existing replacement tube
is half-open horizontally and therefore cannot support a smooth cutoff. -/
def openGraphTube (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.1 ∈ Ioo P.a P.b ∧ |p.2 - P.graph p.1| < T.radius}

lemma isOpen_openGraphTube (P : GraphPatch) (T : P.Tube) :
    IsOpen (P.openGraphTube T) := by
  change IsOpen
    (Prod.fst ⁻¹' Ioo P.a P.b ∩
      (fun p : PlanePoint => |p.2 - P.graph p.1|) ⁻¹' Iio T.radius)
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Iio.preimage
      ((continuous_snd.sub
        (P.graph_contDiff.continuous.comp continuous_fst)).abs))

lemma openGraphTube_subset_closedGraphTube (P : GraphPatch) (T : P.Tube) :
    P.openGraphTube T ⊆ P.closedGraphTube T := by
  rintro p ⟨hx, hy⟩
  exact ⟨⟨hx.1.le, hx.2.le⟩, hy.le⟩

/-- The compact portion of the reference graph on which a scalar test can be
nonzero. -/
def activeGraph (P : GraphPatch) (v : ℝ → ℝ) : Set PlanePoint :=
  (fun x => (x, P.graph x)) '' tsupport v

lemma isCompact_activeGraph (P : GraphPatch) {v : ℝ → ℝ}
    (hv : HasCompactSupport v) : IsCompact (P.activeGraph v) :=
  hv.image (continuous_id.prodMk P.graph_contDiff.continuous)

lemma activeGraph_subset_openGraphTube (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} (hsupport : tsupport v ⊆ Ioo P.a P.b) :
    P.activeGraph v ⊆ P.openGraphTube T := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hsupport hx, by simpa using T.radius_pos⟩

/-- A smooth compactly supported vertical vector field realizing one scalar
velocity on the active reference graph. -/
structure AmbientField (P : GraphPatch) (T : P.Tube) (v : ℝ → ℝ) where
  field : PlanePoint → PlanePoint
  contDiff : ContDiff ℝ ∞ field
  hasCompactSupport : HasCompactSupport field
  tsupport_subset : tsupport field ⊆ P.openGraphTube T
  fst_eq_zero : ∀ p, (field p).1 = 0
  on_graph : ∀ x, field (x, P.graph x) = (0, v x)

namespace AmbientField

/-- A field vanishes pointwise outside its certified open graph tube. -/
lemma eq_zero_of_not_mem {P : GraphPatch} {T : P.Tube} {v : ℝ → ℝ}
    (X : P.AmbientField T v) {p : PlanePoint}
    (hp : p ∉ P.openGraphTube T) : X.field p = 0 := by
  by_contra hne
  exact hp (X.tsupport_subset (subset_tsupport X.field hne))

/-- The field vanishes along the fixed graph-ribbon baseline. -/
lemma on_base {P : GraphPatch} {T : P.Tube} {v : ℝ → ℝ}
    (X : P.AmbientField T v) (x : ℝ) : X.field (x, P.base) = 0 := by
  apply X.eq_zero_of_not_mem
  intro hx
  rcases hx with ⟨hxIoo, hxRadius⟩
  have hclear := T.order_clearance x ⟨hxIoo.1, hxIoo.2.le⟩
  cases hside : P.side with
  | below =>
      simp only [hside] at hclear
      have hneg : P.base - P.graph x < 0 := by
        have hr := T.radius_pos
        linarith
      have hfar : T.radius < |P.base - P.graph x| := by
        rw [abs_of_neg hneg]
        linarith
      exact (not_lt_of_ge hfar.le) hxRadius
  | above =>
      simp only [hside] at hclear
      have hpos : 0 < P.base - P.graph x := by
        have hr := T.radius_pos
        linarith
      have hfar : T.radius < |P.base - P.graph x| := by
        rw [abs_of_pos hpos]
        linarith
      exact (not_lt_of_ge hfar.le) hxRadius

end AmbientField

private def verticalField (beta : PlanePoint → ℝ) (v : ℝ → ℝ) :
    PlanePoint → PlanePoint :=
  fun p => (0, beta p * v p.1)

/-- Every `C∞` compact scalar test supported in the patch interval has a
compactly supported `C∞` ambient vertical extension inside the protected tube. -/
theorem exists_ambientField (P : GraphPatch) (T : P.Tube)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hsupport : tsupport v ⊆ Ioo P.a P.b) :
    Nonempty (P.AmbientField T v) := by
  have hvCompact : HasCompactSupport v :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport v)
      (hsupport.trans Ioo_subset_Icc_self)
  obtain ⟨beta, hbeta, hbetaCompact, hbetaSupport, hbetaOne⟩ :=
    CMVRelaxation.exists_smoothCompactCutoff
      (P.isCompact_activeGraph hvCompact) (P.isOpen_openGraphTube T)
      (P.activeGraph_subset_openGraphTube T hsupport)
  let X : PlanePoint → PlanePoint := verticalField beta v
  have hXsmooth : ContDiff ℝ ∞ X := by
    unfold X verticalField
    exact contDiff_const.prodMk
      (hbeta.mul (hv.comp contDiff_fst))
  have hXsupport : tsupport X ⊆ tsupport beta := by
    apply closure_mono
    intro p hp hzero
    apply hp
    simp [X, verticalField, hzero]
  have hXcompact : HasCompactSupport X :=
    IsCompact.of_isClosed_subset hbetaCompact (isClosed_tsupport X)
      hXsupport
  refine ⟨{
    field := X
    contDiff := hXsmooth
    hasCompactSupport := hXcompact
    tsupport_subset := hXsupport.trans hbetaSupport
    fst_eq_zero := fun _ => rfl
    on_graph := ?_ }⟩
  intro x
  by_cases hvx : v x = 0
  · simp [X, verticalField, hvx]
  · have hx : x ∈ tsupport v := subset_tsupport v hvx
    have hbone : beta (x, P.graph x) = 1 :=
      hbetaOne ⟨x, hx, rfl⟩
    simp [X, verticalField, hbone]

/-- A chosen ambient field for a smooth compactly supported scalar test. -/
noncomputable def ambientField (P : GraphPatch) (T : P.Tube)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    (hsupport : tsupport v ⊆ Ioo P.a P.b) : P.AmbientField T v :=
  (P.exists_ambientField T v hv hsupport).some

/-- The reference graph trace over a horizontal set. -/
def graphTrace (P : GraphPatch) (s : Set ℝ) : Set PlanePoint :=
  (fun x => (x, P.graph x)) '' s

/-- The vertically varied graph trace over a horizontal set. -/
def variedGraphTrace (P : GraphPatch) (v : ℝ → ℝ) (t : ℝ)
    (s : Set ℝ) : Set PlanePoint :=
  (fun x => (x, P.variedGraph v t x)) '' s

namespace AmbientField

/-- A compact smooth ambient field is globally Lipschitz. -/
theorem exists_lipschitzWith {P : GraphPatch} {T : P.Tube} {v : ℝ → ℝ}
    (X : P.AmbientField T v) :
    ∃ L : ℝ≥0, LipschitzWith L X.field :=
  X.contDiff.lipschitzWith_of_hasCompactSupport X.hasCompactSupport (by simp)

/-- The genuine global smooth ambient equivalence generated by a graph field. -/
noncomputable def deformation {P : GraphPatch} {T : P.Tube} {v : ℝ → ℝ}
    (X : P.AmbientField T v) {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    CMVRelaxation.SmoothAmbientEquiv :=
  CMVRelaxation.SmoothAmbientEquiv.ofSmallPerturbation
    hL X.contDiff X.hasCompactSupport hsmall

@[simp] theorem deformation_apply {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (p : PlanePoint) :
    X.deformation hL hsmall p = p + t • X.field p :=
  rfl

/-- The ambient map fixes the first coordinate everywhere. -/
theorem deformation_fst {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (p : PlanePoint) :
    (X.deformation hL hsmall p).1 = p.1 := by
  rw [deformation_apply]
  simp [X.fst_eq_zero]

/-- Pointwise literal realization of the prescribed graph variation. -/
theorem deformation_on_graph {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) :
    X.deformation hL hsmall (x, P.graph x) =
      (x, P.variedGraph v t x) := by
  rw [deformation_apply, X.on_graph]
  simp [GraphPatch.variedGraph]

/-- The whole varied graph trace is the literal image of the reference trace. -/
theorem image_graphTrace {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (s : Set ℝ) :
    X.deformation hL hsmall '' P.graphTrace s =
      P.variedGraphTrace v t s := by
  apply Set.Subset.antisymm
  · rintro p ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (X.deformation_on_graph hL hsmall x).symm⟩
  · rintro p ⟨x, hx, rfl⟩
    exact ⟨(x, P.graph x), ⟨x, hx, rfl⟩,
      X.deformation_on_graph hL hsmall x⟩

/-- The compact moved set stays inside the protected open graph tube. -/
theorem deformation_movedSet_subset {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    (X.deformation hL hsmall).movedSet ⊆ P.openGraphTube T :=
  (CMVRelaxation.SmoothAmbientEquiv.movedSet_ofSmallPerturbation_subset
    hL X.contDiff X.hasCompactSupport hsmall).trans X.tsupport_subset

/-- Every vertical fiber is strictly ordered by the ambient map. -/
theorem deformation_fiber_strictMono {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) :
    StrictMono (fun y : ℝ => (X.deformation hL hsmall (x, y)).2) :=
  CMVRelaxation.SmoothAmbientEquiv.ofSmallPerturbation_fiber_strictMono
    hL X.contDiff X.hasCompactSupport hsmall x

theorem image_regionBetween
    (Φ : CMVRelaxation.SmoothAmbientEquiv)
    {f g f' g' : ℝ → ℝ} {s : Set ℝ}
    (hfst : ∀ p, (Φ p).1 = p.1)
    (hmono : ∀ x, StrictMono (fun y : ℝ => (Φ (x, y)).2))
    (hf : ∀ x ∈ s, Φ (x, f x) = (x, f' x))
    (hg : ∀ x ∈ s, Φ (x, g x) = (x, g' x)) :
    Φ '' regionBetween f g s = regionBetween f' g' s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hfy, hyg⟩, rfl⟩
    change x ∈ s at hx
    change f x < y at hfy
    change y < g x at hyg
    change (Φ (x, y)).1 ∈ s ∧
      f' (Φ (x, y)).1 < (Φ (x, y)).2 ∧
      (Φ (x, y)).2 < g' (Φ (x, y)).1
    rw [hfst]
    simp only
    refine ⟨hx, ?_, ?_⟩
    · have h := hmono x hfy
      change (Φ (x, f x)).2 < (Φ (x, y)).2 at h
      rw [hf x hx] at h
      exact h
    · have h := hmono x hyg
      change (Φ (x, y)).2 < (Φ (x, g x)).2 at h
      rw [hg x hx] at h
      exact h
  · rintro ⟨x, y⟩ ⟨hx, hf'y, hyg'⟩
    let q : PlanePoint := Φ.toHomeomorph.symm (x, y)
    have hqmap : Φ q = (x, y) :=
      Φ.toHomeomorph.apply_symm_apply (x, y)
    have hqx : q.1 = x := by
      have h := congrArg Prod.fst hqmap
      rw [hfst q] at h
      exact h
    have hqeta : (x, q.2) = q := by
      apply Prod.ext
      · exact hqx.symm
      · rfl
    have hqfiber : Φ (x, q.2) = (x, y) := by
      rw [hqeta]
      exact hqmap
    have hfq : f x < q.2 := by
      rw [← (hmono x).lt_iff_lt]
      rw [hf x hx, hqfiber]
      exact hf'y
    have hqg : q.2 < g x := by
      rw [← (hmono x).lt_iff_lt]
      rw [hqfiber, hg x hx]
      exact hyg'
    refine ⟨q, ?_, hqmap⟩
    change q.1 ∈ s ∧ f q.1 < q.2 ∧ q.2 < g q.1
    rw [hqx]
    exact ⟨hx, hfq, hqg⟩

/-- The ambient equivalence maps the entire occupied-side graph ribbon
literally to the existing vertically varied carrier. -/
theorem image_carrier {P : GraphPatch} {T : P.Tube}
    {v : ℝ → ℝ} (X : P.AmbientField T v) {L : ℝ≥0}
    (hL : LipschitzWith L X.field) {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall '' P.carrier = P.variedCarrier v t := by
  have hfst : ∀ p, (X.deformation hL hsmall p).1 = p.1 :=
    X.deformation_fst hL hsmall
  have hmono : ∀ x,
      StrictMono (fun y : ℝ => (X.deformation hL hsmall (x, y)).2) :=
    X.deformation_fiber_strictMono hL hsmall
  have hbase : ∀ x, X.deformation hL hsmall (x, P.base) = (x, P.base) := by
    intro x
    rw [deformation_apply, X.on_base]
    simp
  have hgraph : ∀ x,
      X.deformation hL hsmall (x, P.graph x) =
        (x, P.variedGraph v t x) :=
    X.deformation_on_graph hL hsmall
  cases hside : P.side with
  | below =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact image_regionBetween _ hfst hmono
        (fun x _ => hbase x) (fun x _ => hgraph x)
  | above =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact image_regionBetween _ hfst hmono
        (fun x _ => hgraph x) (fun x _ => hbase x)

end AmbientField

end GraphPatch

/-- The compensating velocity is in fact `C∞`; the earlier graph-variation
API only records the `C²` regularity needed by its length calculation. -/
lemma velocityTwo_contDiff_top (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) :
    ContDiff ℝ ∞ (velocityTwo lam P₁ P₂ V) := by
  change ContDiff ℝ ∞ (fun x =>
    compensationCoefficient lam P₁ P₂ V * P₂.compensationBump x)
  exact contDiff_const.mul P₂.compensationBump_contDiff

namespace TwoPatchData

/-- One compact smooth vertical field realizing two velocities in disjoint
protected graph tubes. -/
structure AmbientField (D : TwoPatchData)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube)
    (v₁ v₂ : ℝ → ℝ) where
  field : PlanePoint → PlanePoint
  contDiff : ContDiff ℝ ∞ field
  hasCompactSupport : HasCompactSupport field
  tsupport_subset :
    tsupport field ⊆
      D.first.openGraphTube T₁ ∪ D.second.openGraphTube T₂
  fst_eq_zero : ∀ p, (field p).1 = 0
  first_on_base :
    ∀ x ∈ Ioc D.first.a D.first.b, field (x, D.first.base) = 0
  first_on_graph :
    ∀ x ∈ Ioc D.first.a D.first.b,
      field (x, D.first.graph x) = (0, v₁ x)
  second_on_base :
    ∀ x ∈ Ioc D.second.a D.second.b, field (x, D.second.base) = 0
  second_on_graph :
    ∀ x ∈ Ioc D.second.a D.second.b,
      field (x, D.second.graph x) = (0, v₂ x)

/-- Smooth compact scalar tests on the two disjoint patches have one ambient
field with no cross-talk between the horizontal windows. -/
theorem exists_ambientField (D : TwoPatchData)
    (T₁ : D.first.Tube) (T₂ : D.second.Tube)
    (v₁ v₂ : ℝ → ℝ)
    (hv₁ : ContDiff ℝ ∞ v₁) (hv₂ : ContDiff ℝ ∞ v₂)
    (hsupport₁ : tsupport v₁ ⊆ Ioo D.first.a D.first.b)
    (hsupport₂ : tsupport v₂ ⊆ Ioo D.second.a D.second.b) :
    Nonempty (D.AmbientField T₁ T₂ v₁ v₂) := by
  let X₁ := D.first.ambientField T₁ v₁ hv₁ hsupport₁
  let X₂ := D.second.ambientField T₂ v₂ hv₂ hsupport₂
  let F : PlanePoint → PlanePoint := fun p => X₁.field p + X₂.field p
  have hnotSecond : ∀ x ∈ Ioc D.first.a D.first.b,
      x ∉ Ioo D.second.a D.second.b := by
    intro x hx₁ hx₂
    exact Set.disjoint_left.1 D.horizontal_disjoint
      ⟨hx₁.1.le, hx₁.2⟩ ⟨hx₂.1.le, hx₂.2.le⟩
  have hnotFirst : ∀ x ∈ Ioc D.second.a D.second.b,
      x ∉ Ioo D.first.a D.first.b := by
    intro x hx₂ hx₁
    exact Set.disjoint_left.1 D.horizontal_disjoint
      ⟨hx₁.1.le, hx₁.2.le⟩ ⟨hx₂.1.le, hx₂.2⟩
  have hX₂zero : ∀ p, p.1 ∈ Ioc D.first.a D.first.b →
      X₂.field p = 0 := by
    intro p hp
    apply X₂.eq_zero_of_not_mem
    intro hpTube
    exact hnotSecond p.1 hp hpTube.1
  have hX₁zero : ∀ p, p.1 ∈ Ioc D.second.a D.second.b →
      X₁.field p = 0 := by
    intro p hp
    apply X₁.eq_zero_of_not_mem
    intro hpTube
    exact hnotFirst p.1 hp hpTube.1
  refine ⟨{
    field := F
    contDiff := X₁.contDiff.add X₂.contDiff
    hasCompactSupport := X₁.hasCompactSupport.add X₂.hasCompactSupport
    tsupport_subset :=
      (tsupport_add X₁.field X₂.field).trans
        (union_subset_union X₁.tsupport_subset X₂.tsupport_subset)
    fst_eq_zero := ?_
    first_on_base := ?_
    first_on_graph := ?_
    second_on_base := ?_
    second_on_graph := ?_ }⟩
  · intro p
    simp [F, X₁.fst_eq_zero, X₂.fst_eq_zero]
  · intro x hx
    rw [show F (x, D.first.base) =
        X₁.field (x, D.first.base) + X₂.field (x, D.first.base) by rfl,
      X₁.on_base, hX₂zero (x, D.first.base) hx]
    simp
  · intro x hx
    rw [show F (x, D.first.graph x) =
        X₁.field (x, D.first.graph x) + X₂.field (x, D.first.graph x) by rfl,
      X₁.on_graph, hX₂zero (x, D.first.graph x) hx]
    simp
  · intro x hx
    rw [show F (x, D.second.base) =
        X₁.field (x, D.second.base) + X₂.field (x, D.second.base) by rfl,
      hX₁zero (x, D.second.base) hx, X₂.on_base]
    simp
  · intro x hx
    rw [show F (x, D.second.graph x) =
        X₁.field (x, D.second.graph x) + X₂.field (x, D.second.graph x) by rfl,
      hX₁zero (x, D.second.graph x) hx, X₂.on_graph]
    simp

namespace AmbientField

theorem exists_lipschitzWith {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂) :
    ∃ L : ℝ≥0, LipschitzWith L X.field :=
  X.contDiff.lipschitzWith_of_hasCompactSupport X.hasCompactSupport (by simp)

/-- The genuine global smooth ambient equivalence generated by both fields. -/
noncomputable def deformation {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    CMVRelaxation.SmoothAmbientEquiv :=
  CMVRelaxation.SmoothAmbientEquiv.ofSmallPerturbation
    hL X.contDiff X.hasCompactSupport hsmall

@[simp] theorem deformation_apply {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) (p : PlanePoint) :
    X.deformation hL hsmall p = p + t • X.field p :=
  rfl

theorem deformation_fst {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) (p : PlanePoint) :
    (X.deformation hL hsmall p).1 = p.1 := by
  rw [deformation_apply]
  simp [X.fst_eq_zero]

theorem deformation_fiber_strictMono {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) (x : ℝ) :
    StrictMono (fun y : ℝ => (X.deformation hL hsmall (x, y)).2) :=
  CMVRelaxation.SmoothAmbientEquiv.ofSmallPerturbation_fiber_strictMono
    hL X.contDiff X.hasCompactSupport hsmall x

theorem deformation_first_base {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) (hx : x ∈ Ioc D.first.a D.first.b) :
    X.deformation hL hsmall (x, D.first.base) = (x, D.first.base) := by
  rw [deformation_apply, X.first_on_base x hx]
  simp

theorem deformation_first_graph {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) (hx : x ∈ Ioc D.first.a D.first.b) :
    X.deformation hL hsmall (x, D.first.graph x) =
      (x, D.first.variedGraph v₁ t x) := by
  rw [deformation_apply, X.first_on_graph x hx]
  simp [GraphPatch.variedGraph]

theorem deformation_second_base {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) (hx : x ∈ Ioc D.second.a D.second.b) :
    X.deformation hL hsmall (x, D.second.base) = (x, D.second.base) := by
  rw [deformation_apply, X.second_on_base x hx]
  simp

theorem deformation_second_graph {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    (x : ℝ) (hx : x ∈ Ioc D.second.a D.second.b) :
    X.deformation hL hsmall (x, D.second.graph x) =
      (x, D.second.variedGraph v₂ t x) := by
  rw [deformation_apply, X.second_on_graph x hx]
  simp [GraphPatch.variedGraph]

/-- Literal image agreement for the first occupied-side graph ribbon. -/
theorem image_first_carrier {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall '' D.first.carrier =
      D.first.variedCarrier v₁ t := by
  have hfst := X.deformation_fst hL hsmall
  have hmono := X.deformation_fiber_strictMono hL hsmall
  cases hside : D.first.side with
  | below =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact GraphPatch.AmbientField.image_regionBetween _ hfst hmono
        (X.deformation_first_base hL hsmall)
        (X.deformation_first_graph hL hsmall)
  | above =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact GraphPatch.AmbientField.image_regionBetween _ hfst hmono
        (X.deformation_first_graph hL hsmall)
        (X.deformation_first_base hL hsmall)

/-- Literal image agreement for the second occupied-side graph ribbon. -/
theorem image_second_carrier {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall '' D.second.carrier =
      D.second.variedCarrier v₂ t := by
  have hfst := X.deformation_fst hL hsmall
  have hmono := X.deformation_fiber_strictMono hL hsmall
  cases hside : D.second.side with
  | below =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact GraphPatch.AmbientField.image_regionBetween _ hfst hmono
        (X.deformation_second_base hL hsmall)
        (X.deformation_second_graph hL hsmall)
  | above =>
      simp only [GraphPatch.carrier, GraphPatch.variedCarrier, hside]
      exact GraphPatch.AmbientField.image_regionBetween _ hfst hmono
        (X.deformation_second_graph hL hsmall)
        (X.deformation_second_base hL hsmall)

theorem image_patchCarriers {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall ''
        (D.first.carrier ∪ D.second.carrier) =
      D.variedCarrier v₁ v₂ t := by
  unfold TwoPatchData.variedCarrier
  rw [image_union, X.image_first_carrier hL hsmall,
    X.image_second_carrier hL hsmall]

theorem deformation_movedSet_subset {D : TwoPatchData}
    {T₁ : D.first.Tube} {T₂ : D.second.Tube} {v₁ v₂ : ℝ → ℝ}
    (X : D.AmbientField T₁ T₂ v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    (X.deformation hL hsmall).movedSet ⊆
      D.first.openGraphTube T₁ ∪ D.second.openGraphTube T₂ :=
  (CMVRelaxation.SmoothAmbientEquiv.movedSet_ofSmallPerturbation_subset
    hL X.contDiff X.hasCompactSupport hsmall).trans X.tsupport_subset

end AmbientField

end TwoPatchData

namespace ActualTwoPatchData

lemma ambientField_eq_zero_on_fixed
    (A : ActualTwoPatchData) {v₁ v₂ : ℝ → ℝ}
    (X : A.patches.AmbientField A.firstTube A.secondTube v₁ v₂)
    {p : PlanePoint} (hp : p ∈ A.fixedCarrier) :
    X.field p = 0 := by
  by_contra hne
  have hpOpen := X.tsupport_subset (subset_tsupport X.field hne)
  have hpClosed :
      p ∈ A.patches.first.closedGraphTube A.firstTube ∪
        A.patches.second.closedGraphTube A.secondTube :=
    hpOpen.elim
      (fun h => Or.inl
        (A.patches.first.openGraphTube_subset_closedGraphTube A.firstTube h))
      (fun h => Or.inr
        (A.patches.second.openGraphTube_subset_closedGraphTube A.secondTube h))
  exact Set.disjoint_left.1 A.fixed_disjoint_closedGraphTubes hp hpClosed

theorem ambientDeformation_fixed
    (A : ActualTwoPatchData) {v₁ v₂ : ℝ → ℝ}
    (X : A.patches.AmbientField A.firstTube A.secondTube v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    {p : PlanePoint} (hp : p ∈ A.fixedCarrier) :
    X.deformation hL hsmall p = p := by
  rw [TwoPatchData.AmbientField.deformation_apply,
    A.ambientField_eq_zero_on_fixed X hp]
  simp

theorem image_fixedCarrier
    (A : ActualTwoPatchData) {v₁ v₂ : ℝ → ℝ}
    (X : A.patches.AmbientField A.firstTube A.secondTube v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall '' A.fixedCarrier = A.fixedCarrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [A.ambientDeformation_fixed X hL hsmall hp]
    exact hp
  · intro p hp
    exact ⟨p, hp, A.ambientDeformation_fixed X hL hsmall hp⟩

/-- Literal ambient-image agreement for the complete actual carrier: the
arbitrary fixed remainder stays pointwise fixed while both graph ribbons move. -/
theorem image_actualCarrier
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first)
    (X : A.patches.AmbientField A.firstTube A.secondTube V
      (velocityTwo lam A.patches.first A.patches.second V))
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1) :
    X.deformation hL hsmall '' A.actualCarrier =
      A.variedCarrier lam V t := by
  unfold ActualTwoPatchData.variedCarrier TwoPatchData.compensatedCarrier
  rw [A.actualCarrier_eq_fixed_union, image_union,
    A.image_fixedCarrier X hL hsmall,
    X.image_patchCarriers hL hsmall]

/-- The ambient deformation is pointwise the identity on the certified
exterior of the two protected closed graph tubes. -/
theorem ambientDeformation_eq_self_of_not_mem_closedGraphTubes
    (A : ActualTwoPatchData) {v₁ v₂ : ℝ → ℝ}
    (X : A.patches.AmbientField A.firstTube A.secondTube v₁ v₂)
    {L : ℝ≥0} (hL : LipschitzWith L X.field)
    {t : ℝ} (hsmall : ‖t‖₊ * L < 1)
    {p : PlanePoint}
    (hp : p ∉ A.patches.first.closedGraphTube A.firstTube ∪
      A.patches.second.closedGraphTube A.secondTube) :
    X.deformation hL hsmall p = p := by
  rw [TwoPatchData.AmbientField.deformation_apply]
  have hfield : X.field p = 0 := by
    by_contra hne
    have hpOpen := X.tsupport_subset (subset_tsupport X.field hne)
    apply hp
    exact hpOpen.elim
      (fun h => Or.inl
        (A.patches.first.openGraphTube_subset_closedGraphTube A.firstTube h))
      (fun h => Or.inr
        (A.patches.second.openGraphTube_subset_closedGraphTube A.secondTube h))
  rw [hfield]
  simp

/-- End-to-end construction for every smooth compactly supported primary test:
one compact smooth field, a global Lipschitz bound, literal actual-carrier
transport, fixed-remainder preservation, and unchanged exterior membership. -/
theorem exists_compensatedSmoothAmbientRealization
    (A : ActualTwoPatchData) (lam : ℝ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsupport : tsupport g ⊆
      Ioo A.patches.first.a A.patches.first.b) :
    ∃ V : PrimaryVariation A.patches.first,
      (V : ℝ → ℝ) = g ∧
      ∃ X : A.patches.AmbientField A.firstTube A.secondTube V
          (velocityTwo lam A.patches.first A.patches.second V),
        ∃ L : ℝ≥0, ∃ hL : LipschitzWith L X.field,
          ∀ {t : ℝ}, ∀ hsmall : ‖t‖₊ * L < 1,
            X.deformation hL hsmall ''
                A.actualCarrier = A.variedCarrier lam V t ∧
            (∀ p ∈ A.fixedCarrier,
              X.deformation hL hsmall p = p) ∧
            (∀ p ∉ A.patches.first.closedGraphTube A.firstTube ∪
                A.patches.second.closedGraphTube A.secondTube,
              X.deformation hL hsmall p = p) := by
  let V : PrimaryVariation A.patches.first :=
    PrimaryVariation.ofSmoothCompact g hg hsupport
  have hVsmooth : ContDiff ℝ ∞ (V : ℝ → ℝ) := by
    change ContDiff ℝ ∞ g
    exact hg
  have hVsupport :
      tsupport (V : ℝ → ℝ) ⊆
        Ioo A.patches.first.a A.patches.first.b := by
    change tsupport g ⊆ Ioo A.patches.first.a A.patches.first.b
    exact hsupport
  obtain ⟨X⟩ := A.patches.exists_ambientField
    A.firstTube A.secondTube V
    (velocityTwo lam A.patches.first A.patches.second V)
    hVsmooth
    (velocityTwo_contDiff_top lam A.patches.first A.patches.second V)
    hVsupport
    (tsupport_velocityTwo_subset lam A.patches.first A.patches.second V)
  obtain ⟨L, hL⟩ := X.exists_lipschitzWith
  refine ⟨V, rfl, X, L, hL, ?_⟩
  intro t hsmall
  exact ⟨A.image_actualCarrier lam V X hL hsmall,
    fun p hp => A.ambientDeformation_fixed X hL hsmall hp,
    fun p hp =>
      A.ambientDeformation_eq_self_of_not_mem_closedGraphTubes
        X hL hsmall hp⟩

/-- The ambient realization and the existing exact-area two-patch family hold
on one common parameter neighborhood. -/
theorem actualTwoPatch_smoothAmbient_checkpoint
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsupport : tsupport g ⊆
      Ioo A.patches.first.a A.patches.first.b) :
    ∃ V : PrimaryVariation A.patches.first,
      (V : ℝ → ℝ) = g ∧
      ∃ X : A.patches.AmbientField A.firstTube A.secondTube V
          (velocityTwo lam A.patches.first A.patches.second V),
        ∃ L : ℝ≥0, ∃ hL : LipschitzWith L X.field,
          ∃ ε > 0, ∀ t, |t| < ε →
            ∃ hsmall : ‖t‖₊ * L < 1,
              X.deformation hL hsmall '' A.actualCarrier =
                  A.variedCarrier lam V t ∧
              WeightedArea lam
                  (X.deformation hL hsmall '' A.actualCarrier) =
                WeightedArea lam A.actualCarrier ∧
              (∀ p ∈ A.fixedCarrier,
                X.deformation hL hsmall p = p) ∧
              (∀ p ∉ A.patches.first.closedGraphTube A.firstTube ∪
                  A.patches.second.closedGraphTube A.secondTube,
                X.deformation hL hsmall p = p) := by
  obtain ⟨V, hVg, X, L, hL, hambient⟩ :=
    A.exists_compensatedSmoothAmbientRealization lam g hg hsupport
  obtain ⟨⟨ε₀, hε₀, hlocal⟩, _hderiv⟩ :=
    actualTwoPatch_checkpoint_with_firstVariation hlam A V
  let δ : ℝ := 1 / ((L : ℝ) + 1)
  have hLplus : 0 < (L : ℝ) + 1 := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hLplus
  refine ⟨V, hVg, X, L, hL, min ε₀ δ, lt_min hε₀ hδ, ?_⟩
  intro t ht
  have ht₀ : |t| < ε₀ := lt_of_lt_of_le ht (min_le_left _ _)
  have htδ : |t| < δ := lt_of_lt_of_le ht (min_le_right _ _)
  have hsmallReal : |t| * (L : ℝ) < 1 := by
    calc
      |t| * (L : ℝ) ≤ |t| * ((L : ℝ) + 1) := by
        gcongr
        linarith
      _ < δ * ((L : ℝ) + 1) :=
        mul_lt_mul_of_pos_right htδ hLplus
      _ = 1 := by
        simp [δ, ne_of_gt hLplus]
  have hsmall : ‖t‖₊ * L < 1 := by
    exact_mod_cast hsmallReal
  rcases hambient hsmall with ⟨himage, hfixed, hexterior⟩
  rcases hlocal t ht₀ with
    ⟨_, _, _, _, _, _, _, _, _, harea, _⟩
  refine ⟨hsmall, himage, ?_, hfixed, hexterior⟩
  rw [himage]
  exact harea

end ActualTwoPatchData

end CMVTwoPatchGraphVariation
