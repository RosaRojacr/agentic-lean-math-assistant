import CMVRegularGermExtension
import CMVFiniteBandCostAssembly

/-!
# A literal interface-extension specimen

This module gives a bounded finite-band realization of the interface-extending
move at `lambda = 2`.  The replacement is geometric data only: its cost and
comparison properties are proved afterwards.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation.InterfaceExtensionSpecimen

open FiniteBandRearrangement
open RegularTraceCornerComparison

structure Scale where
  r : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1

namespace Scale

lemma r_nonneg (s : Scale) : 0 ≤ s.r := s.r_pos.le
lemma cut_lt_top (s : Scale) : 1 + 4 * s.r / 5 < (9 : ℝ) / 5 := by
  nlinarith [s.r_lt_one]

end Scale

def oldLeft (y : ℝ) : ℝ := -3 / 4 * (y - 1)
def oldRight (y : ℝ) : ℝ := 1 - 3 / 4 * (y - 1)
def connectorLeft (s : Scale) (y : ℝ) : ℝ := -5 / 8 * (y - 1) - s.r / 10

def oldRegion : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := ![1, (9 : ℝ) / 5]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    norm_num
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ => oldLeft
  right := fun _ _ => oldRight
  left_continuous := by intro i j; unfold oldLeft; fun_prop
  right_continuous := by intro i j; unfold oldRight; fun_prop
  left_contDiffOn := by intro i j; unfold oldLeft; fun_prop
  right_contDiffOn := by intro i j; unfold oldRight; fun_prop
  left_speed_integrable := by
    intro i j
    have h : ContDiff ℝ 1 oldLeft := by unfold oldLeft; fun_prop
    exact ((continuous_const.add ((h.continuous_deriv (by norm_num)).pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  right_speed_integrable := by
    intro i j
    have h : ContDiff ℝ 1 oldRight := by unfold oldRight; fun_prop
    exact ((continuous_const.add ((h.continuous_deriv (by norm_num)).pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  width_nonneg := by intro i j y hy; unfold oldLeft oldRight; linarith
  width_pos := by intro i j y hy; unfold oldLeft oldRight; linarith
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

def replacementRegion (s : Scale) : Region where
  bandCount := 2
  bandCount_pos := by norm_num
  cuts := ![1, 1 + 4 * s.r / 5, (9 : ℝ) / 5]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    · nlinarith [s.r_pos]
    · norm_num
    · exact s.cut_lt_top
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun i _ => if i.val = 0 then connectorLeft s else oldLeft
  right := fun _ _ => oldRight
  left_continuous := by
    intro i j
    fin_cases i
    · simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      unfold connectorLeft
      fun_prop
    · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
      unfold oldLeft
      fun_prop
  right_continuous := by intro i j; unfold oldRight; fun_prop
  left_contDiffOn := by
    intro i j
    fin_cases i
    · simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      unfold connectorLeft
      fun_prop
    · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
      unfold oldLeft
      fun_prop
  right_contDiffOn := by intro i j; unfold oldRight; fun_prop
  left_speed_integrable := by
    intro i j
    fin_cases i
    · simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      have h : ContDiff ℝ 1 (connectorLeft s) := by unfold connectorLeft; fun_prop
      exact ((continuous_const.add ((h.continuous_deriv (by norm_num)).pow 2)).sqrt.integrableOn_Icc
        (μ := volume)).mono_set Ioo_subset_Icc_self
    · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
      have h : ContDiff ℝ 1 oldLeft := by unfold oldLeft; fun_prop
      exact ((continuous_const.add ((h.continuous_deriv (by norm_num)).pow 2)).sqrt.integrableOn_Icc
        (μ := volume)).mono_set Ioo_subset_Icc_self
  right_speed_integrable := by
    intro i j
    have h : ContDiff ℝ 1 oldRight := by unfold oldRight; fun_prop
    exact ((continuous_const.add ((h.continuous_deriv (by norm_num)).pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  width_nonneg := by
    intro i j y hy
    fin_cases i
    · simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      change 1 ≤ y ∧ y ≤ 1 + 4 * s.r / 5 at hy
      unfold connectorLeft oldRight
      nlinarith [s.r_pos]
    · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
      unfold oldLeft oldRight
      linarith
  width_pos := by
    intro i j y hy
    fin_cases i
    · simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      change 1 < y ∧ y < 1 + 4 * s.r / 5 at hy
      unfold connectorLeft oldRight
      nlinarith [s.r_pos]
    · simp only [Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
      unfold oldLeft oldRight
      linarith
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

abbrev junction : PlanePoint := (0, 1)

def incidentCurve (t : ℝ) : PlanePoint := (-3 * t / 5, 1 + 4 * t / 5)
def interfaceCurve (t : ℝ) : PlanePoint := (t, 1)

private def affineEndpointTrace (j v : PlanePoint) (hv : v ≠ (0, 0)) :
    RegularEndpointTrace j where
  curve t := (j.1 + t * v.1, j.2 + t * v.2)
  velocity := v
  curve_zero := by simp
  complex_contDiff := by
    have heq :
        (fun t : ℝ => complexVector (j.1 + t * v.1, j.2 + t * v.2)) =
          fun t : ℝ => complexVector j + t • complexVector v := by
      funext t
      apply Complex.ext <;> simp [complexVector]
    rw [heq]
    fun_prop
  hasDerivAt_zero := by
    have hx : HasDerivAt (fun t : ℝ => j.1 + t * v.1) v.1 0 := by
      have h := (hasDerivAt_const (x := 0) (c := j.1)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const v.1)
      change HasDerivAt (fun t : ℝ => j.1 + t * v.1) (0 + 1 * v.1) 0 at h
      simpa using h
    have hy : HasDerivAt (fun t : ℝ => j.2 + t * v.2) v.2 0 := by
      have h := (hasDerivAt_const (x := 0) (c := j.2)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).mul_const v.2)
      change HasDerivAt (fun t : ℝ => j.2 + t * v.2) (0 + 1 * v.2) 0 at h
      simpa using h
    have h := FiniteJunctionRepair.hasDerivAt_planeComplexParam
      (x := fun t : ℝ => j.2 + t * v.2)
      (y := fun t : ℝ => j.1 + t * v.1)
      hy.differentiableAt hx.differentiableAt
    rw [hy.deriv, hx.deriv] at h
    simpa [complexVector, Complex.real_smul] using h
  velocity_ne := hv

def incidentTrace : RegularEndpointTrace junction :=
  affineEndpointTrace junction (-3 / 5, 4 / 5) (by norm_num)

def interfaceTrace : RegularEndpointTrace junction :=
  affineEndpointTrace junction (1, 0) (by norm_num)

@[simp] theorem incident_curve (t : ℝ) : incidentTrace.curve t = incidentCurve t := by
  apply Prod.ext <;> simp [incidentTrace, affineEndpointTrace, incidentCurve, junction] <;> ring

@[simp] theorem interface_curve (t : ℝ) : interfaceTrace.curve t = interfaceCurve t := by
  apply Prod.ext <;> simp [interfaceTrace, affineEndpointTrace, interfaceCurve, junction]

@[simp] theorem incident_velocity : incidentTrace.velocity = (-3 / 5, 4 / 5) := rfl
@[simp] theorem interface_velocity : interfaceTrace.velocity = (1, 0) := rfl

lemma incident_speed_one : euclideanSpeed incidentTrace.velocity = 1 := by
  rw [euclideanSpeed, complexVector, Complex.norm_def, Complex.normSq_apply]
  norm_num

lemma interface_speed_one : euclideanSpeed interfaceTrace.velocity = 1 := by
  rw [euclideanSpeed, complexVector, Complex.norm_def, Complex.normSq_apply]
  norm_num

lemma incident_conormal : endpointConormal .initial incidentTrace.velocity = (3 / 5, -4 / 5) := by
  rw [endpointConormal, unitTangent, incident_speed_one]
  norm_num

lemma interface_conormal : endpointConormal .initial interfaceTrace.velocity = (-1, 0) := by
  rw [endpointConormal, unitTangent, interface_speed_one]
  norm_num

lemma actual_conormal_product :
    planeInner (endpointConormal .initial incidentTrace.velocity)
      (endpointConormal .initial interfaceTrace.velocity) = -3 / 5 := by
  rw [incident_conormal, interface_conormal]
  norm_num [planeInner]


private theorem convex_old_component
    (i : Fin oldRegion.bandCount) (j : Fin (oldRegion.componentCount i)) :
    Convex ℝ (oldRegion.componentCarrier i j) := by
  intro p hp q hq a b ha hb hab
  rw [oldRegion.mem_componentCarrier_iff] at hp hq ⊢
  fin_cases i
  change (1 ≤ p.2 ∧ p.2 ≤ (9 : ℝ) / 5) ∧
    oldLeft p.2 ≤ p.1 ∧ p.1 ≤ oldRight p.2 at hp
  change (1 ≤ q.2 ∧ q.2 ≤ (9 : ℝ) / 5) ∧
    oldLeft q.2 ≤ q.1 ∧ q.1 ≤ oldRight q.2 at hq
  change (1 ≤ (a • p + b • q).2 ∧ (a • p + b • q).2 ≤ (9 : ℝ) / 5) ∧
    oldLeft (a • p + b • q).2 ≤ (a • p + b • q).1 ∧
      (a • p + b • q).1 ≤ oldRight (a • p + b • q).2
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  unfold oldLeft oldRight at hp hq ⊢
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem convex_replacement_component (s : Scale)
    (i : Fin (replacementRegion s).bandCount)
    (j : Fin ((replacementRegion s).componentCount i)) :
    Convex ℝ ((replacementRegion s).componentCarrier i j) := by
  intro p hp q hq a b ha hb hab
  rw [(replacementRegion s).mem_componentCarrier_iff] at hp hq ⊢
  fin_cases i
  · change (1 ≤ p.2 ∧ p.2 ≤ 1 + 4 * s.r / 5) ∧
      connectorLeft s p.2 ≤ p.1 ∧ p.1 ≤ oldRight p.2 at hp
    change (1 ≤ q.2 ∧ q.2 ≤ 1 + 4 * s.r / 5) ∧
      connectorLeft s q.2 ≤ q.1 ∧ q.1 ≤ oldRight q.2 at hq
    change (1 ≤ (a • p + b • q).2 ∧
        (a • p + b • q).2 ≤ 1 + 4 * s.r / 5) ∧
      connectorLeft s (a • p + b • q).2 ≤ (a • p + b • q).1 ∧
        (a • p + b • q).1 ≤ oldRight (a • p + b • q).2
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    unfold connectorLeft oldRight at hp hq ⊢
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  · change (1 + 4 * s.r / 5 ≤ p.2 ∧ p.2 ≤ (9 : ℝ) / 5) ∧
      oldLeft p.2 ≤ p.1 ∧ p.1 ≤ oldRight p.2 at hp
    change (1 + 4 * s.r / 5 ≤ q.2 ∧ q.2 ≤ (9 : ℝ) / 5) ∧
      oldLeft q.2 ≤ q.1 ∧ q.1 ≤ oldRight q.2 at hq
    change (1 + 4 * s.r / 5 ≤ (a • p + b • q).2 ∧
        (a • p + b • q).2 ≤ (9 : ℝ) / 5) ∧
      oldLeft (a • p + b • q).2 ≤ (a • p + b • q).1 ∧
        (a • p + b • q).1 ≤ oldRight (a • p + b • q).2
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    unfold oldLeft oldRight at hp hq ⊢
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith

private lemma component_interior_nonempty (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    (interior (R.componentCarrier i j)).Nonempty := by
  let y := (R.cuts i.castSucc + R.cuts i.succ) / 2
  let x := (R.left i j y + R.right i j y) / 2
  have hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) := by
    dsimp [y]
    constructor <;> linarith [@R.cuts_strict i.castSucc i.succ Fin.castSucc_lt_succ]
  have hw := R.width_pos i j y hy
  refine ⟨(x, y), R.mem_interior_componentCarrier_of_strict i j (x, y) hy ?_⟩
  dsimp [x]
  constructor <;> linarith

theorem old_closure_interior_carrier :
    closure (interior oldRegion.carrier) = oldRegion.carrier := by
  apply Subset.antisymm
  · exact oldRegion.isClosed_carrier.closure_interior_subset
  · intro p hp
    rw [Region.carrier, mem_iUnion] at hp
    rcases hp with ⟨i, hp⟩
    rw [Region.bandCarrier, mem_iUnion] at hp
    rcases hp with ⟨j, hp⟩
    have hc := (convex_old_component i j).closure_interior_eq_closure_of_nonempty_interior
      (component_interior_nonempty oldRegion i j)
    have hpClosure : p ∈ closure (interior (oldRegion.componentCarrier i j)) := by
      rw [hc, (oldRegion.isClosed_componentCarrier i j).closure_eq]
      exact hp
    exact closure_mono (interior_mono (by
      intro q hq
      rw [Region.carrier, mem_iUnion]
      exact ⟨i, by rw [Region.bandCarrier, mem_iUnion]; exact ⟨j, hq⟩⟩)) hpClosure

theorem replacement_closure_interior_carrier (s : Scale) :
    closure (interior (replacementRegion s).carrier) =
      (replacementRegion s).carrier := by
  apply Subset.antisymm
  · exact (replacementRegion s).isClosed_carrier.closure_interior_subset
  · intro p hp
    rw [Region.carrier, mem_iUnion] at hp
    rcases hp with ⟨i, hp⟩
    rw [Region.bandCarrier, mem_iUnion] at hp
    rcases hp with ⟨j, hp⟩
    have hc := (convex_replacement_component s i j)
      |>.closure_interior_eq_closure_of_nonempty_interior
        (component_interior_nonempty (replacementRegion s) i j)
    have hpClosure :
        p ∈ closure (interior ((replacementRegion s).componentCarrier i j)) := by
      rw [hc, ((replacementRegion s).isClosed_componentCarrier i j).closure_eq]
      exact hp
    exact closure_mono (interior_mono (by
      intro q hq
      rw [Region.carrier, mem_iUnion]
      exact ⟨i, by rw [Region.bandCarrier, mem_iUnion]; exact ⟨j, hq⟩⟩)) hpClosure

def oldOpen : Set PlanePoint := interior oldRegion.carrier
def replacementOpen (s : Scale) : Set PlanePoint :=
  interior (replacementRegion s).carrier

theorem oldOpen_isOpen : IsOpen oldOpen := isOpen_interior
theorem replacementOpen_isOpen (s : Scale) : IsOpen (replacementOpen s) := isOpen_interior

theorem oldOpen_isBounded : Bornology.IsBounded oldOpen :=
  oldRegion.isBounded_carrier.subset interior_subset

theorem replacementOpen_isBounded (s : Scale) :
    Bornology.IsBounded (replacementOpen s) :=
  (replacementRegion s).isBounded_carrier.subset interior_subset

theorem frontier_oldOpen :
    frontier oldOpen = frontier oldRegion.carrier := by
  rw [oldOpen, isOpen_interior.frontier_eq, old_closure_interior_carrier,
    ← oldRegion.isClosed_carrier.frontier_eq]

theorem frontier_replacementOpen (s : Scale) :
    frontier (replacementOpen s) = frontier (replacementRegion s).carrier := by
  rw [replacementOpen, isOpen_interior.frontier_eq,
    replacement_closure_interior_carrier,
    ← (replacementRegion s).isClosed_carrier.frontier_eq]

lemma incident_image_subset_frontier :
    incidentTrace.curve '' Icc 0 1 ⊆ frontier oldOpen := by
  rw [frontier_oldOpen]
  intro p hp
  apply oldRegion.leftGraphTrace_subset_frontier_carrier (0 : Fin 1) (0 : Fin 1)
  rcases hp with ⟨t, ht, rfl⟩
  refine ⟨1 + 4 * t / 5, ?_, ?_⟩
  · change 1 + 4 * t / 5 ∈ Icc 1 ((9 : ℝ) / 5)
    constructor <;> nlinarith [ht.1, ht.2]
  · rw [incident_curve]
    apply Prod.ext
    · change oldLeft (1 + 4 * t / 5) = -3 * t / 5
      unfold oldLeft
      ring
    · rfl

lemma interface_image_subset_frontier :
    interfaceTrace.curve '' Icc 0 1 ⊆ frontier oldOpen := by
  rw [frontier_oldOpen]
  intro p hp
  apply oldRegion.lowerOuterTrace_subset_frontier_carrier
  rcases hp with ⟨t, ht, rfl⟩
  rw [interface_curve]
  constructor
  · rfl
  · change t ∈ ⋃ _j : Fin 1, Icc (oldLeft 1) (oldRight 1)
    simp [oldLeft, oldRight, ht]

def actualCorner : ActualRegularTraceCorner .upper where
  representative := oldOpen
  representative_isOpen := oldOpen_isOpen
  representative_isBounded := oldOpen_isBounded
  junction := junction
  junction_on_interface := rfl
  radius := 1
  radius_pos := by norm_num
  incident := incidentTrace
  interface := interfaceTrace
  incident_on_frontier := incident_image_subset_frontier
  interface_on_frontier := interface_image_subset_frontier
  interface_on_strip := by
    intro t ht
    rw [interface_curve]
    rfl
  traces_meet_only_at_junction := by
    ext p
    constructor
    · rintro ⟨⟨t, ht, htp⟩, ⟨u, hu, hup⟩⟩
      rw [incident_curve] at htp
      rw [interface_curve] at hup
      have hcoord := congrArg Prod.snd (htp.trans hup.symm)
      have ht0 : t = 0 := by
        change 1 + 4 * t / 5 = 1 at hcoord
        linarith
      subst t
      simpa [incidentCurve, junction] using htp.symm
    · intro hp
      rw [mem_singleton_iff] at hp
      subst p
      constructor
      · exact ⟨0, by norm_num, by simp [incidentCurve, junction]⟩
      · exact ⟨0, by norm_num, by simp [interfaceCurve, junction]⟩

theorem actualCorner_conormal_product :
    planeInner actualCorner.incidentConormal actualCorner.interfaceConormal =
      -3 / 5 := by
  exact actual_conormal_product

lemma exterior_inside_zone_empty {a b : ℝ} (ha : 1 ≤ a) :
    Ioo a b ∩ {y : ℝ | |y| ≤ 1} = ∅ := by
  ext y
  simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_empty_iff_false,
    iff_false]
  rintro ⟨hy, habs⟩
  rw [abs_of_pos (zero_lt_one.trans (ha.trans_lt hy.1))] at habs
  linarith

lemma exterior_outside_zone_eq {a b : ℝ} (ha : 1 ≤ a) :
    Ioo a b \ {y : ℝ | |y| ≤ 1} = Ioo a b := by
  rw [sdiff_eq_left]
  exact Set.disjoint_left.mpr fun y hy habs => by
    change |y| ≤ 1 at habs
    rw [abs_of_pos (zero_lt_one.trans (ha.trans_lt hy.1))] at habs
    exact (not_lt_of_ge habs) (ha.trans_lt hy.1)

lemma weightedTraceCost_affine_exterior
    (m c a b : ℝ) (ha : 1 ≤ a) (hab : a < b) :
    weightedTraceCost 2
        ((fun y : ℝ => (m * y + c, y)) '' Icc a b) =
      ENNReal.ofReal (2 * Real.sqrt (1 + m ^ 2) * (b - a)) := by
  rw [weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun y : ℝ => m * y + c) hab (by fun_prop) (by fun_prop)
      (by
        have hC1 : ContDiff ℝ 1 (fun y : ℝ => m * y + c) := by fun_prop
        have hd : Continuous (deriv (fun y : ℝ => m * y + c)) :=
          hC1.continuous_deriv (by norm_num)
        exact ((continuous_const.add (hd.pow 2)).sqrt.integrableOn_Icc
          (μ := volume)).mono_set Ioo_subset_Icc_self),
    exterior_inside_zone_empty ha, exterior_outside_zone_eq ha,
    setLIntegral_empty, zero_add]
  have hderiv : deriv (fun y : ℝ => m * y + c) = fun _ => m := by
    funext y
    have h := (((hasDerivAt_id y).const_mul m).add_const c).deriv
    change deriv (fun y : ℝ => m * y + c) y = m * 1 at h
    simpa using h
  rw [hderiv, setLIntegral_const, Real.volume_Ioo]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (1 + m ^ 2))]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

lemma sqrt_one_add_three_quarters_sq :
    Real.sqrt (1 + ((-3 : ℝ) / 4) ^ 2) = 5 / 4 := by
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + ((-3 : ℝ) / 4) ^ 2)
  have hn := Real.sqrt_nonneg (1 + ((-3 : ℝ) / 4) ^ 2)
  nlinarith

lemma sqrt_one_add_five_eighths_sq :
    Real.sqrt (1 + ((-5 : ℝ) / 8) ^ 2) = Real.sqrt 89 / 8 := by
  rw [show (1 : ℝ) + ((-5 : ℝ) / 8) ^ 2 = 89 / 64 by norm_num,
    show (89 / 64 : ℝ) = 89 / 8 ^ 2 by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 89)]
  norm_num

def oldIncidentSegment : Set PlanePoint :=
  (fun y : ℝ => (oldLeft y, y)) '' Icc 1 ((9 : ℝ) / 5)

def retainedIncidentSegment (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (oldLeft y, y)) ''
    Icc (1 + 4 * s.r / 5) ((9 : ℝ) / 5)

def connectorSegment (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (connectorLeft s y, y)) '' Icc 1 (1 + 4 * s.r / 5)

def farSegment : Set PlanePoint :=
  (fun y : ℝ => (oldRight y, y)) '' Icc 1 ((9 : ℝ) / 5)

def topSegment : Set PlanePoint :=
  (fun x : ℝ => (x, (9 : ℝ) / 5)) '' Icc (-3 / 5) (2 / 5)

def oldInterfaceSegment : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc 0 1

def extendedInterfaceSegment (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc (-s.r / 10) 1

theorem old_incident_cost :
    weightedTraceCost 2 oldIncidentSegment = ENNReal.ofReal 2 := by
  rw [oldIncidentSegment]
  convert weightedTraceCost_affine_exterior (-3 / 4) (3 / 4) 1 (9 / 5)
    (by norm_num) (by norm_num) using 1
  · congr 2
    funext y
    apply Prod.ext
    · unfold oldLeft
      ring
    · rfl
  · rw [sqrt_one_add_three_quarters_sq]
    norm_num

theorem retained_incident_cost (s : Scale) :
    weightedTraceCost 2 (retainedIncidentSegment s) =
      ENNReal.ofReal (2 * (1 - s.r)) := by
  rw [retainedIncidentSegment]
  convert weightedTraceCost_affine_exterior (-3 / 4) (3 / 4)
    (1 + 4 * s.r / 5) (9 / 5) (by nlinarith [s.r_nonneg])
      s.cut_lt_top using 1
  · congr 2
    funext y
    apply Prod.ext
    · unfold oldLeft
      ring
    · rfl
  · rw [sqrt_one_add_three_quarters_sq]
    congr 1
    ring

theorem connector_cost (s : Scale) :
    weightedTraceCost 2 (connectorSegment s) =
      ENNReal.ofReal (Real.sqrt 89 * s.r / 5) := by
  rw [connectorSegment]
  convert weightedTraceCost_affine_exterior (-5 / 8) (5 / 8 - s.r / 10)
    1 (1 + 4 * s.r / 5) (by norm_num) (by nlinarith [s.r_pos]) using 1
  · congr 2
    funext y
    apply Prod.ext
    · unfold connectorLeft
      ring
    · rfl
  · rw [sqrt_one_add_five_eighths_sq]
    congr 1
    ring

theorem far_cost : weightedTraceCost 2 farSegment = ENNReal.ofReal 2 := by
  rw [farSegment]
  convert weightedTraceCost_affine_exterior (-3 / 4) (7 / 4) 1 (9 / 5)
    (by norm_num) (by norm_num) using 1
  · congr 2
    funext y
    apply Prod.ext
    · unfold oldRight
      ring
    · rfl
  · rw [sqrt_one_add_three_quarters_sq]
    norm_num

theorem top_cost : weightedTraceCost 2 topSegment = ENNReal.ofReal 2 := by
  rw [topSegment, weightedTraceCost_horizontal_image 2 (9 / 5) measurableSet_Icc,
    Real.volume_Icc]
  have hdensity : StripDensity 2 (0, (9 : ℝ) / 5) = 2 := by
    norm_num [StripDensity]
  rw [hdensity]
  norm_num

theorem old_interface_cost :
    weightedTraceCost 2 oldInterfaceSegment = ENNReal.ofReal 1 := by
  rw [oldInterfaceSegment, weightedTraceCost_horizontal_image 2 1 measurableSet_Icc,
    stripDensity_upper_interface, Real.volume_Icc]
  norm_num

theorem extended_interface_cost (s : Scale) :
    weightedTraceCost 2 (extendedInterfaceSegment s) =
      ENNReal.ofReal (1 + s.r / 10) := by
  rw [extendedInterfaceSegment,
    weightedTraceCost_horizontal_image 2 1 measurableSet_Icc,
    stripDensity_upper_interface, Real.volume_Icc]
  rw [show 1 - -s.r / 10 = 1 + s.r / 10 by ring]
  norm_num


lemma oldRegion_graphTrace :
    oldRegion.graphTrace = oldIncidentSegment ∪ farSegment := by
  ext p
  simp [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    oldRegion, oldIncidentSegment, farSegment]

lemma replacementRegion_graphTrace (s : Scale) :
    (replacementRegion s).graphTrace =
      (connectorSegment s ∪ retainedIncidentSegment s) ∪ farSegment := by
  ext p
  simp only [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    replacementRegion, connectorSegment, retainedIncidentSegment, farSegment,
    mem_iUnion, mem_union, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.val_zero, Fin.val_one, zero_ne_one, one_ne_zero,
    ↓reduceIte]
  constructor
  · rintro ⟨i, j, hp | hp⟩
    · fin_cases i
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr hp)
    · rcases hp with ⟨y, hy, rfl⟩
      right
      refine ⟨y, ?_, rfl⟩
      fin_cases i
      · change y ∈ Icc 1 (1 + 4 * s.r / 5) at hy
        exact ⟨hy.1, hy.2.trans s.cut_lt_top.le⟩
      · change y ∈ Icc (1 + 4 * s.r / 5) ((9 : ℝ) / 5) at hy
        exact ⟨(show 1 ≤ 1 + 4 * s.r / 5 by nlinarith [s.r_nonneg]).trans hy.1,
          hy.2⟩
  · rintro ((hp | hp) | hp)
    · exact ⟨(0 : Fin 2), (0 : Fin 1), Or.inl hp⟩
    · exact ⟨(1 : Fin 2), (0 : Fin 1), Or.inl hp⟩
    · rcases hp with ⟨y, hy, rfl⟩
      by_cases hcut : y ≤ 1 + 4 * s.r / 5
      · exact ⟨(0 : Fin 2), (0 : Fin 1), Or.inr ⟨y, ⟨hy.1, hcut⟩, rfl⟩⟩
      · exact ⟨(1 : Fin 2), (0 : Fin 1),
          Or.inr ⟨y, ⟨le_of_not_ge hcut, hy.2⟩, rfl⟩⟩

lemma oldRegion_fiber (i : Fin oldRegion.bandCount) (y : ℝ) :
    oldRegion.fiber i y = Icc (oldLeft y) (oldRight y) := by
  ext x
  simp [Region.fiber, oldRegion]

lemma replacementRegion_fiber (s : Scale)
    (i : Fin (replacementRegion s).bandCount) (y : ℝ) :
    (replacementRegion s).fiber i y =
      if i.val = 0 then Icc (connectorLeft s y) (oldRight y)
      else Icc (oldLeft y) (oldRight y) := by
  by_cases hi : i.val = 0
  · ext x
    simp only [Region.fiber, mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      simpa [replacementRegion, hi] using hj
    · intro hx
      exact ⟨(0 : Fin 1), by simpa [replacementRegion, hi] using hx⟩
  · ext x
    simp only [Region.fiber, mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      simpa [replacementRegion, hi] using hj
    · intro hx
      exact ⟨(0 : Fin 1), by simpa [replacementRegion, hi] using hx⟩

lemma replacement_seam_fibers_eq (s : Scale)
    (i : Fin ((replacementRegion s).bandCount - 1)) :
    (replacementRegion s).fiber ((replacementRegion s).seamLowerBand i)
        ((replacementRegion s).seamHeight i) =
      (replacementRegion s).fiber ((replacementRegion s).seamUpperBand i)
        ((replacementRegion s).seamHeight i) := by
  let seam0 : Fin ((replacementRegion s).bandCount - 1) :=
    ⟨0, by simp [replacementRegion]⟩
  have hval : i.val = 0 := by
    have hlt : i.val < 1 := by
      simpa [replacementRegion] using i.isLt
    omega
  have hi : i = seam0 := Fin.ext hval
  subst i
  dsimp [seam0]
  rw [replacementRegion_fiber, replacementRegion_fiber]
  change Icc (connectorLeft s (1 + 4 * s.r / 5))
      (oldRight (1 + 4 * s.r / 5)) =
    Icc (oldLeft (1 + 4 * s.r / 5)) (oldRight (1 + 4 * s.r / 5))
  congr 1
  unfold connectorLeft oldLeft
  ring

private lemma oldRegion_lowerOuterTrace :
    oldRegion.lowerOuterTrace = oldInterfaceSegment := by
  rw [oldRegion.lowerOuterTrace_eq_horizontal_image]
  have hheight : oldRegion.cuts oldRegion.firstBand.castSucc = 1 := rfl
  rw [hheight, oldRegion_fiber]
  simp [oldLeft, oldRight, oldInterfaceSegment]

private lemma oldRegion_upperOuterTrace :
    oldRegion.upperOuterTrace = topSegment := by
  rw [oldRegion.upperOuterTrace_eq_horizontal_image]
  have hheight : oldRegion.cuts oldRegion.lastBand.succ = (9 : ℝ) / 5 := rfl
  rw [hheight, oldRegion_fiber]
  norm_num [oldLeft, oldRight, topSegment]
  congr 2 <;> norm_num [oldLeft, oldRight]
lemma oldRegion_horizontalFrontierTrace :
    oldRegion.horizontalFrontierTrace = oldInterfaceSegment ∪ topSegment := by
  rw [Region.horizontalFrontierTrace, oldRegion_lowerOuterTrace,
    oldRegion_upperOuterTrace]
  simp [oldRegion]

private lemma replacementRegion_lowerOuterTrace (s : Scale) :
    (replacementRegion s).lowerOuterTrace = extendedInterfaceSegment s := by
  rw [(replacementRegion s).lowerOuterTrace_eq_horizontal_image]
  have hheight :
      (replacementRegion s).cuts (replacementRegion s).firstBand.castSucc = 1 := rfl
  rw [hheight, replacementRegion_fiber]
  simp [replacementRegion, connectorLeft, oldRight, extendedInterfaceSegment]
  congr 2
  ring
private lemma replacementRegion_upperOuterTrace (s : Scale) :
    (replacementRegion s).upperOuterTrace = topSegment := by
  rw [(replacementRegion s).upperOuterTrace_eq_horizontal_image]
  have hheight :
      (replacementRegion s).cuts (replacementRegion s).lastBand.succ = (9 : ℝ) / 5 := rfl
  rw [hheight, replacementRegion_fiber]
  have hlast : (replacementRegion s).lastBand.val = 1 := by
    simp [Region.lastBand, replacementRegion]
  rw [if_neg (by omega : (replacementRegion s).lastBand.val ≠ 0)]
  congr 2 <;> norm_num [oldLeft, oldRight]
lemma replacementRegion_horizontalFrontierTrace (s : Scale) :
    (replacementRegion s).horizontalFrontierTrace =
      extendedInterfaceSegment s ∪ topSegment := by
  rw [Region.horizontalFrontierTrace, replacementRegion_lowerOuterTrace,
    replacementRegion_upperOuterTrace]
  have hseam :
      (⋃ i : Fin ((replacementRegion s).bandCount - 1),
        (replacementRegion s).seamSymmDiff i) = ∅ := by
    ext p
    constructor
    · intro hp
      rw [mem_iUnion] at hp
      rcases hp with ⟨i, hi⟩
      rcases hi with ⟨hy, hx⟩
      rw [replacement_seam_fibers_eq s i] at hx
      simpa using hx
    · simp
  rw [hseam, union_empty]

private lemma measurableSet_oldIncidentSegment : MeasurableSet oldIncidentSegment :=
  measurableSet_verticalGraph_image (by unfold oldLeft; fun_prop) measurableSet_Icc

private lemma measurableSet_retainedIncidentSegment (s : Scale) :
    MeasurableSet (retainedIncidentSegment s) :=
  measurableSet_verticalGraph_image (by unfold oldLeft; fun_prop) measurableSet_Icc

private lemma measurableSet_connectorSegment (s : Scale) :
    MeasurableSet (connectorSegment s) :=
  measurableSet_verticalGraph_image (by unfold connectorLeft; fun_prop) measurableSet_Icc

private lemma measurableSet_farSegment : MeasurableSet farSegment :=
  measurableSet_verticalGraph_image (by unfold oldRight; fun_prop) measurableSet_Icc

private lemma measurableSet_topSegment : MeasurableSet topSegment :=
  measurableSet_horizontal_image (9 / 5) measurableSet_Icc

private lemma measurableSet_oldInterfaceSegment : MeasurableSet oldInterfaceSegment :=
  measurableSet_horizontal_image 1 measurableSet_Icc

private lemma measurableSet_extendedInterfaceSegment (s : Scale) :
    MeasurableSet (extendedInterfaceSegment s) :=
  measurableSet_horizontal_image 1 measurableSet_Icc

private lemma oldIncident_disjoint_far :
    Disjoint oldIncidentSegment farSegment := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy, hpy⟩ ⟨z, hz, hpz⟩
  have hyz : y = z := by simpa using congrArg Prod.snd (hpy.trans hpz.symm)
  subst z
  have hx : oldLeft y = oldRight y := by
    simpa using congrArg Prod.fst (hpy.trans hpz.symm)
  unfold oldLeft oldRight at hx
  linarith

private lemma connector_inter_retained_finite (s : Scale) :
    (connectorSegment s ∩ retainedIncidentSegment s).Finite := by
  apply (Set.finite_singleton
    (oldLeft (1 + 4 * s.r / 5), 1 + 4 * s.r / 5)).subset
  rintro p ⟨⟨y, hy, hpy⟩, ⟨z, hz, hpz⟩⟩
  have hyz : y = z := by simpa using congrArg Prod.snd (hpy.trans hpz.symm)
  subst z
  have hcut : y = 1 + 4 * s.r / 5 := le_antisymm hy.2 hz.1
  subst y
  rw [mem_singleton_iff]
  exact hpz.symm

private lemma connector_disjoint_far (s : Scale) :
    Disjoint (connectorSegment s) farSegment := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy, hpy⟩ ⟨z, hz, hpz⟩
  have hyz : y = z := by simpa using congrArg Prod.snd (hpy.trans hpz.symm)
  subst z
  have hx : connectorLeft s y = oldRight y := by
    simpa using congrArg Prod.fst (hpy.trans hpz.symm)
  unfold connectorLeft oldRight at hx
  nlinarith [hy.1, hy.2, s.r_pos]

private lemma retainedIncident_disjoint_far (s : Scale) :
    Disjoint (retainedIncidentSegment s) farSegment := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy, hpy⟩ ⟨z, hz, hpz⟩
  have hyz : y = z := by simpa using congrArg Prod.snd (hpy.trans hpz.symm)
  subst z
  have hx : oldLeft y = oldRight y := by
    simpa using congrArg Prod.fst (hpy.trans hpz.symm)
  unfold oldLeft oldRight at hx
  linarith

private lemma replacement_left_disjoint_far (s : Scale) :
    Disjoint (connectorSegment s ∪ retainedIncidentSegment s) farSegment :=
  disjoint_union_left.2 ⟨connector_disjoint_far s, retainedIncident_disjoint_far s⟩

private lemma old_horizontal_disjoint :
    Disjoint oldInterfaceSegment topSegment := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, hpx⟩ ⟨z, hz, hpz⟩
  have h := congrArg Prod.snd (hpx.trans hpz.symm)
  norm_num at h

private lemma replacement_horizontal_disjoint (s : Scale) :
    Disjoint (extendedInterfaceSegment s) topSegment := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, hpx⟩ ⟨z, hz, hpz⟩
  have h := congrArg Prod.snd (hpx.trans hpz.symm)
  norm_num at h

theorem old_graph_cost :
    weightedTraceCost 2 oldRegion.graphTrace = ENNReal.ofReal 4 := by
  rw [oldRegion_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      measurableSet_oldIncidentSegment measurableSet_farSegment
      (by rw [oldIncident_disjoint_far.inter_eq]; exact Set.finite_empty),
    old_incident_cost, far_cost]
  norm_num

theorem replacement_graph_cost (s : Scale) :
    weightedTraceCost 2 (replacementRegion s).graphTrace =
      ENNReal.ofReal (Real.sqrt 89 * s.r / 5 + 4 - 2 * s.r) := by
  rw [replacementRegion_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_connectorSegment s |>.union
        (measurableSet_retainedIncidentSegment s))
      measurableSet_farSegment
      (by rw [(replacement_left_disjoint_far s).inter_eq]; exact Set.finite_empty),
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_connectorSegment s) (measurableSet_retainedIncidentSegment s)
      (connector_inter_retained_finite s),
    connector_cost, retained_incident_cost, far_cost,
    ← ENNReal.ofReal_add
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg 89) s.r_nonneg) (by norm_num))
      (by nlinarith [s.r_lt_one] : 0 ≤ 2 * (1 - s.r)),
    ← ENNReal.ofReal_add
      (add_nonneg
        (div_nonneg (mul_nonneg (Real.sqrt_nonneg 89) s.r_nonneg) (by norm_num))
        (by nlinarith [s.r_lt_one] : 0 ≤ 2 * (1 - s.r)))
      (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem old_horizontal_cost :
    weightedTraceCost 2 oldRegion.horizontalFrontierTrace = ENNReal.ofReal 3 := by
  rw [oldRegion_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      measurableSet_oldInterfaceSegment measurableSet_topSegment
      (by rw [old_horizontal_disjoint.inter_eq]; exact Set.finite_empty),
    old_interface_cost, top_cost]
  norm_num

theorem replacement_horizontal_cost (s : Scale) :
    weightedTraceCost 2 (replacementRegion s).horizontalFrontierTrace =
      ENNReal.ofReal (3 + s.r / 10) := by
  rw [replacementRegion_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_extendedInterfaceSegment s) measurableSet_topSegment
      (by rw [(replacement_horizontal_disjoint s).inter_eq]; exact Set.finite_empty),
    extended_interface_cost, top_cost,
    ← ENNReal.ofReal_add (by nlinarith [s.r_nonneg] : 0 ≤ 1 + s.r / 10)
      (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem old_complete_frontier_cost :
    weightedTraceCost 2 (frontier oldRegion.carrier) = ENNReal.ofReal 7 := by
  rw [oldRegion.weightedTraceCost_frontier_carrier,
    oldRegion.weightedTraceCost_completeFrontierTrace,
    ← oldRegion.weightedTraceCost_graphTrace,
    ← oldRegion.weightedTraceCost_horizontalFrontierTrace,
    old_graph_cost, old_horizontal_cost]
  norm_num

theorem replacement_complete_frontier_cost (s : Scale) :
    weightedTraceCost 2 (frontier (replacementRegion s).carrier) =
      ENNReal.ofReal
        (7 - 19 * s.r / 10 + Real.sqrt 89 * s.r / 5) := by
  rw [(replacementRegion s).weightedTraceCost_frontier_carrier,
    (replacementRegion s).weightedTraceCost_completeFrontierTrace,
    ← (replacementRegion s).weightedTraceCost_graphTrace,
    ← (replacementRegion s).weightedTraceCost_horizontalFrontierTrace,
    replacement_graph_cost, replacement_horizontal_cost,
    ← ENNReal.ofReal_add
      (by
        have hsqrt := Real.sqrt_nonneg 89
        nlinarith [s.r_nonneg, s.r_lt_one] :
        0 ≤ Real.sqrt 89 * s.r / 5 + 4 - 2 * s.r)
      (by nlinarith [s.r_nonneg] : 0 ≤ 3 + s.r / 10)]
  congr 1
  ring

lemma two_sqrt_eightyNine_lt_nineteen :
    2 * Real.sqrt 89 < 19 := by
  have hs0 := Real.sqrt_nonneg 89
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 89)
  nlinarith

theorem strict_frontier_cost_descent (s : Scale) :
    weightedTraceCost 2 (frontier (replacementRegion s).carrier) <
      weightedTraceCost 2 (frontier oldRegion.carrier) := by
  rw [replacement_complete_frontier_cost, old_complete_frontier_cost]
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 7)).2
  have hcoef : Real.sqrt 89 / 5 < 19 / 10 := by
    linarith [two_sqrt_eightyNine_lt_nineteen]
  nlinarith [mul_lt_mul_of_pos_right hcoef s.r_pos]

theorem strict_open_frontier_cost_descent (s : Scale) :
    weightedTraceCost 2 (frontier (replacementOpen s)) <
      weightedTraceCost 2 (frontier oldOpen) := by
  rw [frontier_replacementOpen, frontier_oldOpen]
  exact strict_frontier_cost_descent s

private lemma volume_real_Icc_of_le {a b : ℝ} (hab : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  rw [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

private lemma volume_real_Ioo_of_le {a b : ℝ} (hab : a ≤ b) :
    volume.real (Ioo a b) = b - a := by
  rw [measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma oldRegion_horizontalSection (y : ℝ) :
    horizontalSection oldRegion.carrier y =
      if y ∈ Icc 1 (9 / 5 : ℝ) then Icc (oldLeft y) (oldRight y) else ∅ := by
  rw [oldRegion.horizontalSection_carrier]
  ext x
  simp [oldRegion, Region.fiber]

lemma replacementRegion_horizontalSection (s : Scale) (y : ℝ) :
    horizontalSection (replacementRegion s).carrier y =
      if y ∈ Icc 1 (1 + 4 * s.r / 5) then
        Icc (connectorLeft s y) (oldRight y)
      else if y ∈ Icc (1 + 4 * s.r / 5) (9 / 5 : ℝ) then
        Icc (oldLeft y) (oldRight y)
      else ∅ := by
  rw [(replacementRegion s).horizontalSection_carrier]
  ext x
  simp only [replacementRegion, Region.fiber, mem_iUnion, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
    zero_ne_one, one_ne_zero, mem_Icc, mem_empty_iff_false, ite_eq_right_iff,
    mem_union]
  by_cases hlo : 1 ≤ y ∧ y ≤ 1 + 4 * s.r / 5
  · simp [hlo]
    rintro hcut hyTop hxLeft hxRight
    constructor
    · unfold connectorLeft oldLeft at *
      nlinarith
    · exact hxRight
  · by_cases hhi : 1 + 4 * s.r / 5 ≤ y ∧ y ≤ 9 / 5
    · simp [hlo, hhi]
    · simp [hlo, hhi]

theorem old_weightedArea :
    WeightedArea 2 oldRegion.carrier = 8 / 5 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    oldRegion.isClosed_carrier.measurableSet
    oldRegion.isBounded_carrier.measure_lt_top.ne]
  have hintegrand :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real (horizontalSection oldRegion.carrier y)) =
      (Icc 1 (9 / 5 : ℝ)).indicator
        (fun y : ℝ => StripDensity 2 (0, y)) := by
    funext y
    rw [oldRegion_horizontalSection]
    by_cases hy : y ∈ Icc 1 (9 / 5 : ℝ)
    · rw [if_pos hy, Set.indicator_of_mem hy,
        volume_real_Icc_of_le (by
          unfold oldLeft oldRight
          linarith)]
      unfold oldLeft oldRight
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  rw [hintegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioo]
  have hdensity :
      (∫ y in Ioo 1 (9 / 5 : ℝ), StripDensity 2 (0, y)) =
        ∫ _y in Ioo 1 (9 / 5 : ℝ), 2 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    rintro y ⟨hy₁, hy₂⟩
    have hout : ¬|y| ≤ 1 := by
      rw [abs_of_pos (lt_trans zero_lt_one hy₁)]
      linarith
    simp [StripDensity, hout]
  rw [hdensity, setIntegral_const]
  simp only [smul_eq_mul]
  rw [volume_real_Ioo_of_le (by norm_num)]
  norm_num


theorem replacement_weightedArea (s : Scale) :
    WeightedArea 2 (replacementRegion s).carrier =
      8 / 5 + 2 * s.r ^ 2 / 25 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    (replacementRegion s).isClosed_carrier.measurableSet
    (replacementRegion s).isBounded_carrier.measure_lt_top.ne]
  let cut : ℝ := 1 + 4 * s.r / 5
  let lowIntegrand : ℝ → ℝ :=
    fun y => 2 * (oldRight y - connectorLeft s y)
  let highIntegrand : ℝ → ℝ := fun _ => 2
  have haeeq :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real
          (horizontalSection (replacementRegion s).carrier y)) =ᵐ[volume]
      (Ioo 1 cut).indicator lowIntegrand +
        (Ioo cut (9 / 5 : ℝ)).indicator highIntegrand := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null
      (t := ({1, cut, (9 / 5 : ℝ)} : Set ℝ))
    · intro y hy
      simp only [mem_insert_iff, mem_singleton_iff]
      by_contra hnot
      push Not at hnot
      apply hy
      rw [replacementRegion_horizontalSection]
      change StripDensity 2 (0, y) *
          volume.real
            (if y ∈ Icc 1 (1 + 4 * s.r / 5) then
              Icc (connectorLeft s y) (oldRight y)
            else if y ∈ Icc (1 + 4 * s.r / 5) (9 / 5 : ℝ) then
              Icc (oldLeft y) (oldRight y) else ∅) =
        (Ioo 1 cut).indicator lowIntegrand y +
          (Ioo cut (9 / 5 : ℝ)).indicator highIntegrand y
      by_cases hlo : y ∈ Icc 1 cut
      · have hlo' : y ∈ Ioo 1 cut := ⟨lt_of_le_of_ne hlo.1 hnot.1.symm,
          lt_of_le_of_ne hlo.2 hnot.2.1⟩
        rw [if_pos hlo, Set.indicator_of_mem hlo',
          Set.indicator_of_notMem (by
            intro hhi
            exact lt_asymm hlo'.2 hhi.1),
          volume_real_Icc_of_le (by
            have hytop : y ≤ 1 + 4 * s.r / 5 := by
              simpa only [cut] using hlo.2
            unfold connectorLeft oldRight
            nlinarith [hlo.1, hytop, s.r_pos])]
        have hout : ¬|y| ≤ 1 := by
          rw [abs_of_pos (lt_trans zero_lt_one hlo'.1)]
          exact not_le_of_gt hlo'.1
        simp only [StripDensity, hout, if_false]
        dsimp [lowIntegrand]
        ring
      · by_cases hhi : y ∈ Icc cut (9 / 5 : ℝ)
        · have hhi' : y ∈ Ioo cut (9 / 5 : ℝ) :=
            ⟨lt_of_le_of_ne hhi.1 hnot.2.1.symm,
              lt_of_le_of_ne hhi.2 hnot.2.2⟩
          rw [if_neg hlo, if_pos hhi, Set.indicator_of_notMem (by
              intro hlow
              exact hlo ⟨hlow.1.le, hlow.2.le⟩),
            Set.indicator_of_mem hhi',
            volume_real_Icc_of_le (by
              unfold oldLeft oldRight
              linarith)]
          have hout : ¬|y| ≤ 1 := by
            have hcutOne : 1 < cut := by
              dsimp [cut]
              nlinarith [s.r_pos]
            have hyOne : 1 < y := hcutOne.trans hhi'.1
            rw [abs_of_pos (lt_trans zero_lt_one hyOne)]
            exact not_le_of_gt hyOne
          simp [StripDensity, hout, highIntegrand]
          unfold oldLeft oldRight
          ring
        · rw [if_neg hlo, if_neg hhi,
            Set.indicator_of_notMem (by
              intro hlow
              exact hlo ⟨hlow.1.le, hlow.2.le⟩),
            Set.indicator_of_notMem (by
              intro hhigh
              exact hhi ⟨hhigh.1.le, hhigh.2.le⟩)]
          simp
    · exact (Set.toFinite ({1, cut, (9 / 5 : ℝ)} : Set ℝ)).measure_zero volume
  rw [integral_congr_ae haeeq]
  have hlowInt : Integrable ((Ioo 1 cut).indicator lowIntegrand) := by
    apply IntegrableOn.integrable_indicator
    · have hc :
          Continuous (fun y : ℝ => 2 * (oldRight y - connectorLeft s y)) := by
        unfold oldRight connectorLeft
        fun_prop
      simpa only [lowIntegrand] using
        hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact measurableSet_Ioo
  have hhighInt : Integrable
      ((Ioo cut (9 / 5 : ℝ)).indicator highIntegrand) := by
    apply IntegrableOn.integrable_indicator
    · have hc : Continuous (fun _y : ℝ => (2 : ℝ)) := continuous_const
      simpa only [highIntegrand] using
        hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact measurableSet_Ioo
  change (∫ y : ℝ,
      (Ioo 1 cut).indicator lowIntegrand y +
        (Ioo cut (9 / 5 : ℝ)).indicator highIntegrand y) =
    8 / 5 + 2 * s.r ^ 2 / 25
  rw [integral_add hlowInt hhighInt,
    integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ioo]
  have hlowSet :
      (∫ y in Ioo 1 cut, lowIntegrand y) =
        ∫ y : ℝ in 1..cut, lowIntegrand y := by
    rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le]
    dsimp [cut]
    nlinarith [s.r_pos]
  have hhighSet :
      (∫ y in Ioo cut (9 / 5 : ℝ), highIntegrand y) =
        ∫ y : ℝ in cut..(9 / 5 : ℝ), highIntegrand y := by
    rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le]
    dsimp [cut]
    nlinarith [s.r_lt_one]
  have hlow :
      (∫ y : ℝ in 1..cut, lowIntegrand y) =
        8 * s.r / 5 + 2 * s.r ^ 2 / 25 := by
    dsimp [lowIntegrand, cut]
    calc
      (∫ y : ℝ in 1..1 + 4 * s.r / 5,
          2 * (oldRight y - connectorLeft s y)) =
          (((9 : ℝ) / 4 + s.r / 5) * (1 + 4 * s.r / 5) -
            (1 + 4 * s.r / 5) ^ 2 / 8) -
          (((9 : ℝ) / 4 + s.r / 5) * 1 - 1 ^ 2 / 8) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun y : ℝ => ((9 : ℝ) / 4 + s.r / 5) * y - y ^ 2 / 8) ?_ ?_
        · intro y hy
          unfold oldRight connectorLeft
          convert ((hasDerivAt_const y ((9 : ℝ) / 4 + s.r / 5)).mul
              (hasDerivAt_id y)).sub
            (((hasDerivAt_id y).pow 2).div_const 8) using 1
          · rfl
          · norm_num [id_eq]
            ring
        · exact (by
            unfold oldRight connectorLeft
            fun_prop :
            Continuous (fun y : ℝ => 2 * (oldRight y - connectorLeft s y)))
            |>.intervalIntegrable 1 (1 + 4 * s.r / 5)
      _ = 8 * s.r / 5 + 2 * s.r ^ 2 / 25 := by ring
  have hhigh :
      (∫ y : ℝ in cut..(9 / 5 : ℝ), highIntegrand y) =
        8 / 5 - 8 * s.r / 5 := by
    dsimp [highIntegrand, cut]
    rw [intervalIntegral.integral_const]
    ring
  rw [hlowSet, hhighSet, hlow, hhigh]
  ring

theorem weightedArea_defect_exact (s : Scale) :
    |WeightedArea 2 (replacementRegion s).carrier -
      WeightedArea 2 oldRegion.carrier| = 2 * s.r ^ 2 / 25 := by
  rw [replacement_weightedArea, old_weightedArea]
  have hsquare : 0 ≤ s.r ^ 2 := sq_nonneg s.r
  rw [abs_of_nonneg (by nlinarith)]
  ring

theorem weightedArea_defect_le_r_sq (s : Scale) :
    |WeightedArea 2 (replacementRegion s).carrier -
      WeightedArea 2 oldRegion.carrier| ≤ s.r ^ 2 := by
  rw [weightedArea_defect_exact]
  nlinarith [sq_nonneg s.r]

/-! ## Explicit move accounting -/

/-- The initial incident piece removed by the extension move. -/
def removedIncidentSegment (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (oldLeft y, y)) '' Icc 1 (1 + 4 * s.r / 5)

/-- The newly exposed negative part of the upper interface. -/
def addedNegativeInterfaceSegment (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc (-s.r / 10) 0

theorem oldIncidentSegment_eq_removed_union_retained (s : Scale) :
    oldIncidentSegment =
      removedIncidentSegment s ∪ retainedIncidentSegment s := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hcut : y ≤ 1 + 4 * s.r / 5
    · exact Or.inl ⟨y, ⟨hy.1, hcut⟩, rfl⟩
    · exact Or.inr ⟨y, ⟨le_of_not_ge hcut, hy.2⟩, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, ⟨hy.1, hy.2.trans s.cut_lt_top.le⟩, rfl⟩
    · exact ⟨y, ⟨(by
        have hcut_lower : 1 ≤ 1 + 4 * s.r / 5 := by
          nlinarith [s.r_nonneg]
        exact hcut_lower.trans hy.1), hy.2⟩, rfl⟩

theorem extendedInterfaceSegment_eq_added_union_old (s : Scale) :
    extendedInterfaceSegment s =
      addedNegativeInterfaceSegment s ∪ oldInterfaceSegment := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x ≤ 0
    · exact Or.inl ⟨x, ⟨hx.1, hx0⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨le_of_not_ge hx0, hx.2⟩, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, ⟨hx.1, hx.2.trans (by norm_num)⟩, rfl⟩
    · exact ⟨x, ⟨(by
        have hnew_lower : -s.r / 10 ≤ 0 := by
          nlinarith [s.r_nonneg]
        exact hnew_lower.trans hx.1), hx.2⟩, rfl⟩

theorem frontier_oldOpen_eq_namedPieces :
    frontier oldOpen =
      (oldIncidentSegment ∪ farSegment) ∪
        (oldInterfaceSegment ∪ topSegment) := by
  rw [frontier_oldOpen, oldRegion.frontier_carrier,
    oldRegion.completeFrontierTrace_eq_graph_union_horizontal,
    oldRegion_graphTrace, oldRegion_horizontalFrontierTrace]

theorem frontier_replacementOpen_eq_namedPieces (s : Scale) :
    frontier (replacementOpen s) =
      ((connectorSegment s ∪ retainedIncidentSegment s) ∪ farSegment) ∪
        (extendedInterfaceSegment s ∪ topSegment) := by
  rw [frontier_replacementOpen, (replacementRegion s).frontier_carrier,
    (replacementRegion s).completeFrontierTrace_eq_graph_union_horizontal,
    replacementRegion_graphTrace, replacementRegion_horizontalFrontierTrace]

theorem actualCorner_extension_gain_pos :
    0 < extensionTangentGain 2 1 (1 / 10)
      (planeInner actualCorner.incidentConormal actualCorner.interfaceConormal) := by
  rw [actualCorner_conormal_product]
  exact LambdaTwoExtension.extension_gain_pos

theorem weightedArea_signed_defect_exact (s : Scale) :
    WeightedArea 2 (replacementRegion s).carrier -
      WeightedArea 2 oldRegion.carrier = 2 * s.r ^ 2 / 25 := by
  rw [replacement_weightedArea, old_weightedArea]
  ring

end CMVRelaxation.InterfaceExtensionSpecimen
