import CMVFiniteBandCostAssembly

/-!
# Literal nontransverse corner shortening

Two independent `lambda = 2` specimens isolate the local operation behind the
nontransverse contact law.  Every specimen and competitor is an actual bounded
planar carrier represented by one finite graph band.  The complete frontier is
therefore the literal topological frontier supplied by the finite-band theory;
no perimeter formula, contact inequality, source-minimality transfer, or global
CMV configuration is assumed.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation.LiteralCornerShortening

open FiniteBandRearrangement

/-- Positive shortening scale.  The upper bound keeps the density-one specimen
inside the closed strip. -/
structure Scale where
  r : ℝ
  r_pos : 0 < r
  r_le_one : r ≤ 1

namespace Scale

lemma r_nonneg (s : Scale) : 0 ≤ s.r := s.r_pos.le

end Scale

/-- The exterior/interface corner before shortening: the closed rectangle
`[0,r] × [1,1+r]`. -/
def exteriorInterfaceSpecimen (s : Scale) : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := ![1, 1 + s.r]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact s.r_pos
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ _ => 0
  right := fun _ _ _ => s.r
  left_continuous := by intro i j; fun_prop
  right_continuous := by intro i j; fun_prop
  left_contDiffOn := by intro i j; fun_prop
  right_contDiffOn := by intro i j; fun_prop
  left_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  right_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  width_nonneg := by intro i j y hy; exact s.r_nonneg
  width_pos := by intro i j y hy; exact s.r_pos
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

/-- The actual triangular exterior competitor.  Its diagonal joins `(r,1)` to
`(0,1+r)`, replacing the density-one interface edge and one exterior edge. -/
def exteriorInterfaceCompetitor (s : Scale) : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := ![1, 1 + s.r]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact s.r_pos
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ y => 1 + s.r - y
  right := fun _ _ _ => s.r
  left_continuous := by intro i j; fun_prop
  right_continuous := by intro i j; fun_prop
  left_contDiffOn := by intro i j; fun_prop
  right_contDiffOn := by intro i j; fun_prop
  left_speed_integrable := by
    intro i j
    have hC1 : ContDiff ℝ 1 (fun y : ℝ => 1 + s.r - y) := by fun_prop
    have hd : Continuous (deriv (fun y : ℝ => 1 + s.r - y)) :=
      hC1.continuous_deriv (by norm_num)
    exact ((continuous_const.add (hd.pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  right_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  width_nonneg := by
    intro i j y hy
    fin_cases i
    change 1 ≤ y ∧ y ≤ 1 + s.r at hy
    linarith
  width_pos := by
    intro i j y hy
    fin_cases i
    change 1 < y ∧ y < 1 + s.r at hy
    linarith
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

/-- A wholly density-one nontangential corner before shortening: the closed
rectangle `[0,r] × [1-r,1]`. -/
def densityOneNontangentialSpecimen (s : Scale) : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := ![1 - s.r, 1]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact s.r_pos
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ _ => 0
  right := fun _ _ _ => s.r
  left_continuous := by intro i j; fun_prop
  right_continuous := by intro i j; fun_prop
  left_contDiffOn := by intro i j; fun_prop
  right_contDiffOn := by intro i j; fun_prop
  left_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  right_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  width_nonneg := by intro i j y hy; exact s.r_nonneg
  width_pos := by intro i j y hy; exact s.r_pos
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

/-- The actual density-one triangular competitor.  Its diagonal joins
`(0,1-r)` to `(r,1)`. -/
def densityOneNontangentialCompetitor (s : Scale) : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := ![1 - s.r, 1]
  cuts_strict := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    exact s.r_pos
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ y => y - (1 - s.r)
  right := fun _ _ _ => s.r
  left_continuous := by intro i j; fun_prop
  right_continuous := by intro i j; fun_prop
  left_contDiffOn := by intro i j; fun_prop
  right_contDiffOn := by intro i j; fun_prop
  left_speed_integrable := by
    intro i j
    have hC1 : ContDiff ℝ 1 (fun y : ℝ => y - (1 - s.r)) := by fun_prop
    have hd : Continuous (deriv (fun y : ℝ => y - (1 - s.r))) :=
      hC1.continuous_deriv (by norm_num)
    exact ((continuous_const.add (hd.pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  right_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  width_nonneg := by
    intro i j y hy
    fin_cases i
    change 1 - s.r ≤ y ∧ y ≤ 1 at hy
    linarith
  width_pos := by
    intro i j y hy
    fin_cases i
    change 1 - s.r < y ∧ y < 1 at hy
    linarith
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

/-- Literal occupied-side identification for the exterior rectangle. -/
theorem exteriorInterfaceSpecimen_carrier (s : Scale) :
    (exteriorInterfaceSpecimen s).carrier =
      {p : PlanePoint | 0 ≤ p.1 ∧ p.1 ≤ s.r ∧ 1 ≤ p.2 ∧ p.2 ≤ 1 + s.r} := by
  ext p
  simp [Region.carrier, Region.bandCarrier, Region.componentCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand, exteriorInterfaceSpecimen,
    min_eq_left s.r_nonneg, max_eq_right s.r_nonneg]
  tauto

/-- Literal occupied-side identification for the exterior triangle. -/
theorem exteriorInterfaceCompetitor_carrier (s : Scale) :
    (exteriorInterfaceCompetitor s).carrier =
      {p : PlanePoint | 1 ≤ p.2 ∧ p.2 ≤ 1 + s.r ∧
        1 + s.r - p.2 ≤ p.1 ∧ p.1 ≤ s.r} := by
  ext p
  simp [Region.carrier, Region.bandCarrier, Region.componentCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand,
    exteriorInterfaceCompetitor]
  constructor
  · rintro ⟨hy, hlo, hhi⟩
    have hL : 1 + s.r - p.2 ≤ s.r := by linarith [hy.1]
    have hlo' : 1 + s.r ≤ p.1 + p.2 := by
      rcases hlo with h | h <;> linarith
    have hhi' : p.1 ≤ s.r := by
      rcases hhi with h | h <;> linarith
    exact ⟨hy.1, hy.2, hlo', hhi'⟩
  · rintro ⟨hy₁, hy₂, hlo, hhi⟩
    exact ⟨⟨hy₁, hy₂⟩, Or.inl (by linarith), Or.inr hhi⟩

/-- Literal occupied-side identification for the density-one rectangle. -/
theorem densityOneNontangentialSpecimen_carrier (s : Scale) :
    (densityOneNontangentialSpecimen s).carrier =
      {p : PlanePoint | 0 ≤ p.1 ∧ p.1 ≤ s.r ∧
        1 - s.r ≤ p.2 ∧ p.2 ≤ 1} := by
  ext p
  simp [Region.carrier, Region.bandCarrier, Region.componentCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand,
    densityOneNontangentialSpecimen, min_eq_left s.r_nonneg,
    max_eq_right s.r_nonneg]
  tauto

/-- Literal occupied-side identification for the density-one triangle. -/
theorem densityOneNontangentialCompetitor_carrier (s : Scale) :
    (densityOneNontangentialCompetitor s).carrier =
      {p : PlanePoint | 1 - s.r ≤ p.2 ∧ p.2 ≤ 1 ∧
        p.2 - (1 - s.r) ≤ p.1 ∧ p.1 ≤ s.r} := by
  ext p
  simp [Region.carrier, Region.bandCarrier, Region.componentCarrier,
    FiniteJunctionRepair.closedHorizontalGraphBand,
    densityOneNontangentialCompetitor]
  constructor
  · rintro ⟨hy, hlo, hhi⟩
    have hL : p.2 - (1 - s.r) ≤ s.r := by linarith [hy.2]
    have hlo' : p.2 ≤ p.1 + (1 - s.r) := by
      rcases hlo with h | h <;> linarith
    have hhi' : p.1 ≤ s.r := by
      rcases hhi with h | h <;> linarith
    exact ⟨hy.1, hy.2, hlo', hhi'⟩
  · rintro ⟨hy₁, hy₂, hlo, hhi⟩
    exact ⟨⟨hy₁, hy₂⟩, Or.inl (by linarith), Or.inr hhi⟩

/-- Complete topological-frontier accounting for the actual exterior specimen. -/
theorem exteriorInterfaceSpecimen_frontier (s : Scale) :
    frontier (exteriorInterfaceSpecimen s).carrier =
      (exteriorInterfaceSpecimen s).completeFrontierTrace :=
  (exteriorInterfaceSpecimen s).frontier_carrier

/-- Complete topological-frontier accounting for its actual competitor. -/
theorem exteriorInterfaceCompetitor_frontier (s : Scale) :
    frontier (exteriorInterfaceCompetitor s).carrier =
      (exteriorInterfaceCompetitor s).completeFrontierTrace :=
  (exteriorInterfaceCompetitor s).frontier_carrier

/-- Complete topological-frontier accounting for the density-one specimen. -/
theorem densityOneNontangentialSpecimen_frontier (s : Scale) :
    frontier (densityOneNontangentialSpecimen s).carrier =
      (densityOneNontangentialSpecimen s).completeFrontierTrace :=
  (densityOneNontangentialSpecimen s).frontier_carrier

/-- Complete topological-frontier accounting for its actual competitor. -/
theorem densityOneNontangentialCompetitor_frontier (s : Scale) :
    frontier (densityOneNontangentialCompetitor s).carrier =
      (densityOneNontangentialCompetitor s).completeFrontierTrace :=
  (densityOneNontangentialCompetitor s).frontier_carrier


/-- The positive-height interval of the exterior specimen has no density-one
interior.  The endpoint at height one is deliberately absent here and is
handled by the endpoint-null graph theorem. -/
lemma exterior_inside_zone_empty (s : Scale) :
    Ioo 1 (1 + s.r) ∩ {y : ℝ | |y| ≤ 1} = ∅ := by
  ext y
  simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_empty_iff_false,
    iff_false]
  rintro ⟨hy, habs⟩
  rw [abs_of_pos (lt_trans zero_lt_one hy.1)] at habs
  linarith

lemma exterior_outside_zone_eq (s : Scale) :
    Ioo 1 (1 + s.r) \ {y : ℝ | |y| ≤ 1} = Ioo 1 (1 + s.r) := by
  rw [sdiff_eq_left]
  exact Set.disjoint_left.mpr fun y hy habs =>
    (by
      rcases hy with ⟨hy₁, hy₂⟩
      change |y| ≤ 1 at habs
      rw [abs_of_pos (lt_trans zero_lt_one hy₁)] at habs
      linarith)

/-- The lower specimen remains in the density-one strip, including its upper
interface endpoint. -/
lemma densityOne_interval_subset (s : Scale) :
    Ioo (1 - s.r) 1 ⊆ {y : ℝ | |y| ≤ 1} := by
  intro y hy
  have hlower : 0 ≤ 1 - s.r := by linarith [s.r_le_one]
  have hy0 : 0 < y := lt_of_le_of_lt hlower hy.1
  change |y| ≤ 1
  rw [abs_of_pos hy0]
  exact hy.2.le

lemma densityOne_inside_zone_eq (s : Scale) :
    Ioo (1 - s.r) 1 ∩ {y : ℝ | |y| ≤ 1} = Ioo (1 - s.r) 1 :=
  inter_eq_left.mpr (densityOne_interval_subset s)

lemma densityOne_outside_zone_empty (s : Scale) :
    Ioo (1 - s.r) 1 \ {y : ℝ | |y| ≤ 1} = ∅ :=
  sdiff_eq_empty.2 (densityOne_interval_subset s)

def interfaceTrace (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc 0 s.r

def exteriorIncidentTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (0, y)) '' Icc 1 (1 + s.r)

def exteriorShortcutTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (1 + s.r - y, y)) '' Icc 1 (1 + s.r)

def densityOneIncidentTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (0, y)) '' Icc (1 - s.r) 1

def densityOneShortcutTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (y - (1 - s.r), y)) '' Icc (1 - s.r) 1

/-- A whole positive-length interface segment is charged at density one. -/
theorem weightedTraceCost_interfaceTrace (s : Scale) :
    weightedTraceCost 2 (interfaceTrace s) = ENNReal.ofReal s.r := by
  rw [interfaceTrace, weightedTraceCost_horizontal_image 2 1 measurableSet_Icc,
    stripDensity_upper_interface, Real.volume_Icc]
  norm_num [s.r_nonneg]

/-- Exact price of a regular exterior vertical ray.  Its interface endpoint is
retained literally but has zero one-dimensional measure. -/
theorem weightedTraceCost_exteriorIncidentTrace (s : Scale) :
    weightedTraceCost 2 (exteriorIncidentTrace s) =
      ENNReal.ofReal (2 * s.r) := by
  rw [exteriorIncidentTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun _ : ℝ => 0) (by linarith [s.r_pos]) (by fun_prop) (by fun_prop)
      (by
        simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero, Real.sqrt_one]
        exact integrableOn_const measure_Ioo_lt_top.ne),
    exterior_inside_zone_empty s, exterior_outside_zone_eq s,
    setLIntegral_empty, zero_add]
  simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one]
  rw [setLIntegral_const, Real.volume_Ioo]
  norm_num

theorem weightedTraceCost_exteriorShortcutTrace (s : Scale) :
    weightedTraceCost 2 (exteriorShortcutTrace s) =
      ENNReal.ofReal (2 * Real.sqrt 2 * s.r) := by
  rw [exteriorShortcutTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun y : ℝ => 1 + s.r - y) (by linarith [s.r_pos])
      (by fun_prop) (by fun_prop)
      (by
        have hC1 : ContDiff ℝ 1 (fun y : ℝ => 1 + s.r - y) := by fun_prop
        have hd : Continuous (deriv (fun y : ℝ => 1 + s.r - y)) :=
          hC1.continuous_deriv (by norm_num)
        exact ((continuous_const.add (hd.pow 2)).sqrt.integrableOn_Icc
          (μ := volume)).mono_set Ioo_subset_Icc_self),
    exterior_inside_zone_empty s, exterior_outside_zone_eq s,
    setLIntegral_empty, zero_add]
  have hderiv : deriv (fun y : ℝ => 1 + s.r - y) = fun _ => -1 := by
    funext y
    change deriv ((fun _ : ℝ => 1 + s.r) - id) y = -1
    rw [HasDerivAt.deriv
      ((hasDerivAt_const y (1 + s.r)).sub (hasDerivAt_id y))]
    norm_num
  rw [hderiv]
  simp only [neg_one_sq, one_add_one_eq_two]
  rw [setLIntegral_const, Real.volume_Ioo]
  rw [show 1 + s.r - 1 = s.r by ring]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2)]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring
theorem weightedTraceCost_densityOneIncidentTrace (s : Scale) :
    weightedTraceCost 2 (densityOneIncidentTrace s) = ENNReal.ofReal s.r := by
  rw [densityOneIncidentTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun _ : ℝ => 0) (by linarith [s.r_pos]) (by fun_prop) (by fun_prop)
      (by
        simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero, Real.sqrt_one]
        exact integrableOn_const measure_Ioo_lt_top.ne),
    densityOne_inside_zone_eq s, densityOne_outside_zone_empty s,
    setLIntegral_empty, mul_zero, add_zero]
  simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one]
  rw [setLIntegral_const, Real.volume_Ioo]
  norm_num
theorem weightedTraceCost_densityOneShortcutTrace (s : Scale) :
    weightedTraceCost 2 (densityOneShortcutTrace s) =
      ENNReal.ofReal (Real.sqrt 2 * s.r) := by
  rw [densityOneShortcutTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun y : ℝ => y - (1 - s.r)) (by linarith [s.r_pos])
      (by fun_prop) (by fun_prop)
      (by
        have hC1 : ContDiff ℝ 1 (fun y : ℝ => y - (1 - s.r)) := by fun_prop
        have hd : Continuous (deriv (fun y : ℝ => y - (1 - s.r))) :=
          hC1.continuous_deriv (by norm_num)
        exact ((continuous_const.add (hd.pow 2)).sqrt.integrableOn_Icc
          (μ := volume)).mono_set Ioo_subset_Icc_self),
    densityOne_inside_zone_eq s, densityOne_outside_zone_empty s,
    setLIntegral_empty, mul_zero, add_zero]
  have hderiv : deriv (fun y : ℝ => y - (1 - s.r)) = fun _ => 1 := by
    funext y
    change deriv (id - (fun _ : ℝ => 1 - s.r)) y = 1
    rw [HasDerivAt.deriv
      ((hasDerivAt_id y).sub (hasDerivAt_const y (1 - s.r)))]
    norm_num
  rw [hderiv]
  simp only [one_pow, one_add_one_eq_two]
  rw [setLIntegral_const, Real.volume_Ioo]
  rw [show 1 - (1 - s.r) = s.r by ring,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]



def exteriorFarTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (s.r, y)) '' Icc 1 (1 + s.r)

def exteriorTopTrace (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1 + s.r)) '' Icc 0 s.r

lemma exteriorInterfaceSpecimen_graphTrace (s : Scale) :
    (exteriorInterfaceSpecimen s).graphTrace =
      exteriorIncidentTrace s ∪ exteriorFarTrace s := by
  ext p
  simp [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    exteriorInterfaceSpecimen, exteriorIncidentTrace, exteriorFarTrace]
lemma exteriorInterfaceSpecimen_fiber (s : Scale)
    (i : Fin (exteriorInterfaceSpecimen s).bandCount) (y : ℝ) :
    (exteriorInterfaceSpecimen s).fiber i y = Icc 0 s.r := by
  ext x
  simp [Region.fiber, exteriorInterfaceSpecimen]

lemma exteriorInterfaceSpecimen_lowerOuterTrace (s : Scale) :
    (exteriorInterfaceSpecimen s).lowerOuterTrace = interfaceTrace s := by
  rw [(exteriorInterfaceSpecimen s).lowerOuterTrace_eq_horizontal_image]
  have hheight :
      (exteriorInterfaceSpecimen s).cuts
        (exteriorInterfaceSpecimen s).firstBand.castSucc = 1 := by
    rfl
  rw [hheight, exteriorInterfaceSpecimen_fiber]
  rfl

lemma exteriorInterfaceSpecimen_upperOuterTrace (s : Scale) :
    (exteriorInterfaceSpecimen s).upperOuterTrace = exteriorTopTrace s := by
  rw [(exteriorInterfaceSpecimen s).upperOuterTrace_eq_horizontal_image]
  have hheight :
      (exteriorInterfaceSpecimen s).cuts
        (exteriorInterfaceSpecimen s).lastBand.succ = 1 + s.r := by
    rfl
  rw [hheight, exteriorInterfaceSpecimen_fiber]
  rfl

lemma exteriorInterfaceSpecimen_horizontalFrontierTrace (s : Scale) :
    (exteriorInterfaceSpecimen s).horizontalFrontierTrace =
      interfaceTrace s ∪ exteriorTopTrace s := by
  rw [Region.horizontalFrontierTrace,
    exteriorInterfaceSpecimen_lowerOuterTrace,
    exteriorInterfaceSpecimen_upperOuterTrace]
  simp [exteriorInterfaceSpecimen]


lemma measurableSet_exteriorIncidentTrace (s : Scale) :
    MeasurableSet (exteriorIncidentTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_exteriorFarTrace (s : Scale) :
    MeasurableSet (exteriorFarTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_interfaceTrace (s : Scale) :
    MeasurableSet (interfaceTrace s) :=
  measurableSet_horizontal_image 1 measurableSet_Icc

lemma measurableSet_exteriorTopTrace (s : Scale) :
    MeasurableSet (exteriorTopTrace s) :=
  measurableSet_horizontal_image (1 + s.r) measurableSet_Icc

lemma exterior_vertical_traces_disjoint (s : Scale) :
    Disjoint (exteriorIncidentTrace s) (exteriorFarTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy, rfl⟩ ⟨z, hz, hp⟩
  have hx : (0 : ℝ) = s.r := by simpa using (congrArg Prod.fst hp).symm
  linarith [s.r_pos]

lemma exterior_horizontal_traces_disjoint (s : Scale) :
    Disjoint (interfaceTrace s) (exteriorTopTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, rfl⟩ ⟨z, hz, hp⟩
  have hy : (1 : ℝ) = 1 + s.r := by simpa using (congrArg Prod.snd hp).symm
  linarith [s.r_pos]

theorem weightedTraceCost_exteriorFarTrace (s : Scale) :
    weightedTraceCost 2 (exteriorFarTrace s) =
      ENNReal.ofReal (2 * s.r) := by
  rw [exteriorFarTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun _ : ℝ => s.r) (by linarith [s.r_pos])
      (by fun_prop) (by fun_prop)
      (by
        simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero, Real.sqrt_one]
        exact integrableOn_const measure_Ioo_lt_top.ne),
    exterior_inside_zone_empty s, exterior_outside_zone_eq s,
    setLIntegral_empty, zero_add]
  simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one]
  rw [setLIntegral_const, Real.volume_Ioo]
  norm_num

theorem weightedTraceCost_exteriorTopTrace (s : Scale) :
    weightedTraceCost 2 (exteriorTopTrace s) =
      ENNReal.ofReal (2 * s.r) := by
  rw [exteriorTopTrace,
    weightedTraceCost_horizontal_image 2 (1 + s.r) measurableSet_Icc,
    Real.volume_Icc]
  have hdensity : StripDensity 2 (0, 1 + s.r) = 2 := by
    simp only [StripDensity]
    rw [if_neg]
    rw [abs_of_pos (by linarith [s.r_pos])]
    linarith [s.r_pos]
  rw [hdensity]
  norm_num [s.r_nonneg]

lemma exteriorInterfaceSpecimen_graph_cost (s : Scale) :
    weightedTraceCost 2 (exteriorInterfaceSpecimen s).graphTrace =
      ENNReal.ofReal (4 * s.r) := by
  rw [exteriorInterfaceSpecimen_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_exteriorIncidentTrace s)
      (measurableSet_exteriorFarTrace s)
      (by
        rw [(exterior_vertical_traces_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_exteriorIncidentTrace,
    weightedTraceCost_exteriorFarTrace,
    ← ENNReal.ofReal_add (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)]
  congr 1
  ring

lemma exteriorInterfaceSpecimen_horizontal_cost (s : Scale) :
    weightedTraceCost 2 (exteriorInterfaceSpecimen s).horizontalFrontierTrace =
      ENNReal.ofReal (3 * s.r) := by
  rw [exteriorInterfaceSpecimen_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_interfaceTrace s) (measurableSet_exteriorTopTrace s)
      (by
        rw [(exterior_horizontal_traces_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_interfaceTrace, weightedTraceCost_exteriorTopTrace,
    ← ENNReal.ofReal_add s.r_nonneg
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)]
  congr 1
  ring

theorem exteriorInterfaceSpecimen_complete_frontier_cost (s : Scale) :
    weightedTraceCost 2 (frontier (exteriorInterfaceSpecimen s).carrier) =
      ENNReal.ofReal (7 * s.r) := by
  rw [(exteriorInterfaceSpecimen s).weightedTraceCost_frontier_carrier,
    (exteriorInterfaceSpecimen s).weightedTraceCost_completeFrontierTrace,
    ← (exteriorInterfaceSpecimen s).weightedTraceCost_graphTrace,
    ← (exteriorInterfaceSpecimen s).weightedTraceCost_horizontalFrontierTrace]
  rw [exteriorInterfaceSpecimen_graph_cost,
    exteriorInterfaceSpecimen_horizontal_cost,
    ← ENNReal.ofReal_add (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 4 * s.r)
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 3 * s.r)]
  congr 1
  ring


def exteriorBottomPointTrace (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc s.r s.r

lemma exteriorInterfaceCompetitor_graphTrace (s : Scale) :
    (exteriorInterfaceCompetitor s).graphTrace =
      exteriorShortcutTrace s ∪ exteriorFarTrace s := by
  ext p
  simp [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    exteriorInterfaceCompetitor, exteriorShortcutTrace, exteriorFarTrace]

lemma exteriorInterfaceCompetitor_fiber (s : Scale)
    (i : Fin (exteriorInterfaceCompetitor s).bandCount) (y : ℝ) :
    (exteriorInterfaceCompetitor s).fiber i y =
      Icc (1 + s.r - y) s.r := by
  ext x
  simp [Region.fiber, exteriorInterfaceCompetitor]

lemma exteriorInterfaceCompetitor_lowerOuterTrace (s : Scale) :
    (exteriorInterfaceCompetitor s).lowerOuterTrace =
      exteriorBottomPointTrace s := by
  rw [(exteriorInterfaceCompetitor s).lowerOuterTrace_eq_horizontal_image]
  have hheight :
      (exteriorInterfaceCompetitor s).cuts
        (exteriorInterfaceCompetitor s).firstBand.castSucc = 1 := by
    rfl
  rw [hheight, exteriorInterfaceCompetitor_fiber]
  simp only [add_sub_cancel_left]
  rfl

lemma exteriorInterfaceCompetitor_upperOuterTrace (s : Scale) :
    (exteriorInterfaceCompetitor s).upperOuterTrace = exteriorTopTrace s := by
  rw [(exteriorInterfaceCompetitor s).upperOuterTrace_eq_horizontal_image]
  have hheight :
      (exteriorInterfaceCompetitor s).cuts
        (exteriorInterfaceCompetitor s).lastBand.succ = 1 + s.r := by
    rfl
  rw [hheight, exteriorInterfaceCompetitor_fiber]
  rw [show 1 + s.r - (1 + s.r) = 0 by ring]
  rfl

lemma exteriorInterfaceCompetitor_horizontalFrontierTrace (s : Scale) :
    (exteriorInterfaceCompetitor s).horizontalFrontierTrace =
      exteriorBottomPointTrace s ∪ exteriorTopTrace s := by
  rw [Region.horizontalFrontierTrace,
    exteriorInterfaceCompetitor_lowerOuterTrace,
    exteriorInterfaceCompetitor_upperOuterTrace]
  simp [exteriorInterfaceCompetitor]

lemma measurableSet_exteriorShortcutTrace (s : Scale) :
    MeasurableSet (exteriorShortcutTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_exteriorBottomPointTrace (s : Scale) :
    MeasurableSet (exteriorBottomPointTrace s) :=
  measurableSet_horizontal_image 1 measurableSet_Icc

lemma exterior_shortcut_inter_far_finite (s : Scale) :
    (exteriorShortcutTrace s ∩ exteriorFarTrace s).Finite := by
  refine (Set.finite_singleton (s.r, 1)).subset ?_
  rintro p ⟨⟨y, hy, rfl⟩, ⟨z, hz, hp⟩⟩
  have hyz : y = z := by simpa using (congrArg Prod.snd hp).symm
  have hx : s.r = 1 + s.r - y := by simpa using congrArg Prod.fst hp
  have hyone : y = 1 := by linarith
  subst y
  simp [hyone]

lemma exterior_bottom_top_disjoint (s : Scale) :
    Disjoint (exteriorBottomPointTrace s) (exteriorTopTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, rfl⟩ ⟨z, hz, hp⟩
  have hy : (1 : ℝ) = 1 + s.r := by simpa using (congrArg Prod.snd hp).symm
  linarith [s.r_pos]

theorem weightedTraceCost_exteriorBottomPointTrace (s : Scale) :
    weightedTraceCost 2 (exteriorBottomPointTrace s) = 0 := by
  rw [exteriorBottomPointTrace,
    weightedTraceCost_horizontal_image 2 1 measurableSet_Icc,
    Real.volume_Icc]
  norm_num

lemma exteriorInterfaceCompetitor_graph_cost (s : Scale) :
    weightedTraceCost 2 (exteriorInterfaceCompetitor s).graphTrace =
      ENNReal.ofReal ((2 + 2 * Real.sqrt 2) * s.r) := by
  rw [exteriorInterfaceCompetitor_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_exteriorShortcutTrace s)
      (measurableSet_exteriorFarTrace s)
      (exterior_shortcut_inter_far_finite s),
    weightedTraceCost_exteriorShortcutTrace,
    weightedTraceCost_exteriorFarTrace,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ 2 * Real.sqrt 2 * s.r)
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)]
  congr 1
  ring

lemma exteriorInterfaceCompetitor_horizontal_cost (s : Scale) :
    weightedTraceCost 2
        (exteriorInterfaceCompetitor s).horizontalFrontierTrace =
      ENNReal.ofReal (2 * s.r) := by
  rw [exteriorInterfaceCompetitor_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_exteriorBottomPointTrace s)
      (measurableSet_exteriorTopTrace s)
      (by
        rw [(exterior_bottom_top_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_exteriorBottomPointTrace, zero_add,
    weightedTraceCost_exteriorTopTrace]

theorem exteriorInterfaceCompetitor_complete_frontier_cost (s : Scale) :
    weightedTraceCost 2 (frontier (exteriorInterfaceCompetitor s).carrier) =
      ENNReal.ofReal ((4 + 2 * Real.sqrt 2) * s.r) := by
  rw [(exteriorInterfaceCompetitor s).weightedTraceCost_frontier_carrier,
    (exteriorInterfaceCompetitor s).weightedTraceCost_completeFrontierTrace,
    ← (exteriorInterfaceCompetitor s).weightedTraceCost_graphTrace,
    ← (exteriorInterfaceCompetitor s).weightedTraceCost_horizontalFrontierTrace,
    exteriorInterfaceCompetitor_graph_cost,
    exteriorInterfaceCompetitor_horizontal_cost,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ (2 + 2 * Real.sqrt 2) * s.r)
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)]
  congr 1
  ring


def densityOneFarTrace (s : Scale) : Set PlanePoint :=
  (fun y : ℝ => (s.r, y)) '' Icc (1 - s.r) 1

def densityOneBottomTrace (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1 - s.r)) '' Icc 0 s.r

def densityOneTopPointTrace (s : Scale) : Set PlanePoint :=
  (fun x : ℝ => (x, 1)) '' Icc s.r s.r

lemma densityOneNontangentialSpecimen_graphTrace (s : Scale) :
    (densityOneNontangentialSpecimen s).graphTrace =
      densityOneIncidentTrace s ∪ densityOneFarTrace s := by
  ext p
  simp [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    densityOneNontangentialSpecimen, densityOneIncidentTrace,
    densityOneFarTrace]

lemma densityOneNontangentialSpecimen_fiber (s : Scale)
    (i : Fin (densityOneNontangentialSpecimen s).bandCount) (y : ℝ) :
    (densityOneNontangentialSpecimen s).fiber i y = Icc 0 s.r := by
  ext x
  simp [Region.fiber, densityOneNontangentialSpecimen]

lemma densityOneNontangentialSpecimen_lowerOuterTrace (s : Scale) :
    (densityOneNontangentialSpecimen s).lowerOuterTrace =
      densityOneBottomTrace s := by
  rw [(densityOneNontangentialSpecimen s).lowerOuterTrace_eq_horizontal_image]
  have hheight :
      (densityOneNontangentialSpecimen s).cuts
        (densityOneNontangentialSpecimen s).firstBand.castSucc = 1 - s.r := by
    rfl
  rw [hheight, densityOneNontangentialSpecimen_fiber]
  rfl

lemma densityOneNontangentialSpecimen_upperOuterTrace (s : Scale) :
    (densityOneNontangentialSpecimen s).upperOuterTrace = interfaceTrace s := by
  rw [(densityOneNontangentialSpecimen s).upperOuterTrace_eq_horizontal_image]
  have hheight :
      (densityOneNontangentialSpecimen s).cuts
        (densityOneNontangentialSpecimen s).lastBand.succ = 1 := by
    rfl
  rw [hheight, densityOneNontangentialSpecimen_fiber]
  rfl

lemma densityOneNontangentialSpecimen_horizontalFrontierTrace (s : Scale) :
    (densityOneNontangentialSpecimen s).horizontalFrontierTrace =
      densityOneBottomTrace s ∪ interfaceTrace s := by
  rw [Region.horizontalFrontierTrace,
    densityOneNontangentialSpecimen_lowerOuterTrace,
    densityOneNontangentialSpecimen_upperOuterTrace]
  simp [densityOneNontangentialSpecimen]

lemma densityOneNontangentialCompetitor_graphTrace (s : Scale) :
    (densityOneNontangentialCompetitor s).graphTrace =
      densityOneShortcutTrace s ∪ densityOneFarTrace s := by
  ext p
  simp [Region.graphTrace, Region.leftGraphTrace, Region.rightGraphTrace,
    densityOneNontangentialCompetitor, densityOneShortcutTrace,
    densityOneFarTrace]

lemma densityOneNontangentialCompetitor_fiber (s : Scale)
    (i : Fin (densityOneNontangentialCompetitor s).bandCount) (y : ℝ) :
    (densityOneNontangentialCompetitor s).fiber i y =
      Icc (y - (1 - s.r)) s.r := by
  ext x
  simp [Region.fiber, densityOneNontangentialCompetitor]

lemma densityOneNontangentialCompetitor_lowerOuterTrace (s : Scale) :
    (densityOneNontangentialCompetitor s).lowerOuterTrace =
      densityOneBottomTrace s := by
  rw [(densityOneNontangentialCompetitor s).lowerOuterTrace_eq_horizontal_image]
  have hheight :
      (densityOneNontangentialCompetitor s).cuts
        (densityOneNontangentialCompetitor s).firstBand.castSucc = 1 - s.r := by
    rfl
  rw [hheight, densityOneNontangentialCompetitor_fiber]
  rw [show 1 - s.r - (1 - s.r) = 0 by ring]
  rfl

lemma densityOneNontangentialCompetitor_upperOuterTrace (s : Scale) :
    (densityOneNontangentialCompetitor s).upperOuterTrace =
      densityOneTopPointTrace s := by
  rw [(densityOneNontangentialCompetitor s).upperOuterTrace_eq_horizontal_image]
  have hheight :
      (densityOneNontangentialCompetitor s).cuts
        (densityOneNontangentialCompetitor s).lastBand.succ = 1 := by
    rfl
  rw [hheight, densityOneNontangentialCompetitor_fiber]
  rw [show 1 - (1 - s.r) = s.r by ring]
  rfl

lemma densityOneNontangentialCompetitor_horizontalFrontierTrace (s : Scale) :
    (densityOneNontangentialCompetitor s).horizontalFrontierTrace =
      densityOneBottomTrace s ∪ densityOneTopPointTrace s := by
  rw [Region.horizontalFrontierTrace,
    densityOneNontangentialCompetitor_lowerOuterTrace,
    densityOneNontangentialCompetitor_upperOuterTrace]
  simp [densityOneNontangentialCompetitor]

lemma measurableSet_densityOneIncidentTrace (s : Scale) :
    MeasurableSet (densityOneIncidentTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_densityOneShortcutTrace (s : Scale) :
    MeasurableSet (densityOneShortcutTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_densityOneFarTrace (s : Scale) :
    MeasurableSet (densityOneFarTrace s) := by
  exact measurableSet_verticalGraph_image (by fun_prop) measurableSet_Icc

lemma measurableSet_densityOneBottomTrace (s : Scale) :
    MeasurableSet (densityOneBottomTrace s) :=
  measurableSet_horizontal_image (1 - s.r) measurableSet_Icc

lemma measurableSet_densityOneTopPointTrace (s : Scale) :
    MeasurableSet (densityOneTopPointTrace s) :=
  measurableSet_horizontal_image 1 measurableSet_Icc

lemma densityOne_vertical_traces_disjoint (s : Scale) :
    Disjoint (densityOneIncidentTrace s) (densityOneFarTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨y, hy, rfl⟩ ⟨z, hz, hp⟩
  have hx : (0 : ℝ) = s.r := by simpa using (congrArg Prod.fst hp).symm
  linarith [s.r_pos]

lemma densityOne_bottom_interface_disjoint (s : Scale) :
    Disjoint (densityOneBottomTrace s) (interfaceTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, rfl⟩ ⟨z, hz, hp⟩
  have hy : 1 - s.r = (1 : ℝ) := by simpa using (congrArg Prod.snd hp).symm
  linarith [s.r_pos]

lemma densityOne_shortcut_inter_far_finite (s : Scale) :
    (densityOneShortcutTrace s ∩ densityOneFarTrace s).Finite := by
  refine (Set.finite_singleton (s.r, 1)).subset ?_
  rintro p ⟨⟨y, hy, rfl⟩, ⟨z, hz, hp⟩⟩
  have hyz : y = z := by simpa using (congrArg Prod.snd hp).symm
  have hx : s.r = y - (1 - s.r) := by simpa using congrArg Prod.fst hp
  have hyone : y = 1 := by linarith
  subst y
  simp [hyone]

lemma densityOne_bottom_topPoint_disjoint (s : Scale) :
    Disjoint (densityOneBottomTrace s) (densityOneTopPointTrace s) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, rfl⟩ ⟨z, hz, hp⟩
  have hy : 1 - s.r = (1 : ℝ) := by simpa using (congrArg Prod.snd hp).symm
  linarith [s.r_pos]

theorem weightedTraceCost_densityOneFarTrace (s : Scale) :
    weightedTraceCost 2 (densityOneFarTrace s) = ENNReal.ofReal s.r := by
  rw [densityOneFarTrace,
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals 2
      (g := fun _ : ℝ => s.r) (by linarith [s.r_pos])
      (by fun_prop) (by fun_prop)
      (by
        simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero, Real.sqrt_one]
        exact integrableOn_const measure_Ioo_lt_top.ne),
    densityOne_inside_zone_eq s, densityOne_outside_zone_empty s,
    setLIntegral_empty, mul_zero, add_zero]
  simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one]
  rw [setLIntegral_const, Real.volume_Ioo]
  norm_num

theorem weightedTraceCost_densityOneBottomTrace (s : Scale) :
    weightedTraceCost 2 (densityOneBottomTrace s) = ENNReal.ofReal s.r := by
  rw [densityOneBottomTrace,
    weightedTraceCost_horizontal_image 2 (1 - s.r) measurableSet_Icc,
    Real.volume_Icc]
  have hdensity : StripDensity 2 (0, 1 - s.r) = 1 := by
    simp only [StripDensity]
    rw [if_pos]
    have hnonneg : 0 ≤ 1 - s.r := by linarith [s.r_le_one]
    rw [abs_of_nonneg hnonneg]
    exact sub_le_self 1 s.r_nonneg
  rw [hdensity]
  norm_num [s.r_nonneg]

theorem weightedTraceCost_densityOneTopPointTrace (s : Scale) :
    weightedTraceCost 2 (densityOneTopPointTrace s) = 0 := by
  rw [densityOneTopPointTrace,
    weightedTraceCost_horizontal_image 2 1 measurableSet_Icc,
    Real.volume_Icc]
  norm_num

lemma densityOneNontangentialSpecimen_graph_cost (s : Scale) :
    weightedTraceCost 2 (densityOneNontangentialSpecimen s).graphTrace =
      ENNReal.ofReal (2 * s.r) := by
  rw [densityOneNontangentialSpecimen_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_densityOneIncidentTrace s)
      (measurableSet_densityOneFarTrace s)
      (by
        rw [(densityOne_vertical_traces_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_densityOneIncidentTrace,
    weightedTraceCost_densityOneFarTrace,
    ← ENNReal.ofReal_add s.r_nonneg s.r_nonneg]
  congr 1
  ring

lemma densityOneNontangentialSpecimen_horizontal_cost (s : Scale) :
    weightedTraceCost 2
        (densityOneNontangentialSpecimen s).horizontalFrontierTrace =
      ENNReal.ofReal (2 * s.r) := by
  rw [densityOneNontangentialSpecimen_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_densityOneBottomTrace s)
      (measurableSet_interfaceTrace s)
      (by
        rw [(densityOne_bottom_interface_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_densityOneBottomTrace, weightedTraceCost_interfaceTrace,
    ← ENNReal.ofReal_add s.r_nonneg s.r_nonneg]
  congr 1
  ring

lemma densityOneNontangentialCompetitor_graph_cost (s : Scale) :
    weightedTraceCost 2 (densityOneNontangentialCompetitor s).graphTrace =
      ENNReal.ofReal ((1 + Real.sqrt 2) * s.r) := by
  rw [densityOneNontangentialCompetitor_graphTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_densityOneShortcutTrace s)
      (measurableSet_densityOneFarTrace s)
      (densityOne_shortcut_inter_far_finite s),
    weightedTraceCost_densityOneShortcutTrace,
    weightedTraceCost_densityOneFarTrace,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ Real.sqrt 2 * s.r) s.r_nonneg]
  congr 1
  ring

lemma densityOneNontangentialCompetitor_horizontal_cost (s : Scale) :
    weightedTraceCost 2
        (densityOneNontangentialCompetitor s).horizontalFrontierTrace =
      ENNReal.ofReal s.r := by
  rw [densityOneNontangentialCompetitor_horizontalFrontierTrace,
    weightedTraceCost_union_eq_add_of_inter_finite 2
      (measurableSet_densityOneBottomTrace s)
      (measurableSet_densityOneTopPointTrace s)
      (by
        rw [(densityOne_bottom_topPoint_disjoint s).inter_eq]
        exact Set.finite_empty),
    weightedTraceCost_densityOneBottomTrace,
    weightedTraceCost_densityOneTopPointTrace, add_zero]

theorem densityOneNontangentialSpecimen_complete_frontier_cost (s : Scale) :
    weightedTraceCost 2
        (frontier (densityOneNontangentialSpecimen s).carrier) =
      ENNReal.ofReal (4 * s.r) := by
  rw [(densityOneNontangentialSpecimen s).weightedTraceCost_frontier_carrier,
    (densityOneNontangentialSpecimen s).weightedTraceCost_completeFrontierTrace,
    ← (densityOneNontangentialSpecimen s).weightedTraceCost_graphTrace,
    ← (densityOneNontangentialSpecimen s).weightedTraceCost_horizontalFrontierTrace,
    densityOneNontangentialSpecimen_graph_cost,
    densityOneNontangentialSpecimen_horizontal_cost,
    ← ENNReal.ofReal_add
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)
      (by nlinarith [s.r_nonneg] : (0 : ℝ) ≤ 2 * s.r)]
  congr 1
  ring

theorem densityOneNontangentialCompetitor_complete_frontier_cost (s : Scale) :
    weightedTraceCost 2
        (frontier (densityOneNontangentialCompetitor s).carrier) =
      ENNReal.ofReal ((2 + Real.sqrt 2) * s.r) := by
  rw [(densityOneNontangentialCompetitor s).weightedTraceCost_frontier_carrier,
    (densityOneNontangentialCompetitor s).weightedTraceCost_completeFrontierTrace,
    ← (densityOneNontangentialCompetitor s).weightedTraceCost_graphTrace,
    ← (densityOneNontangentialCompetitor s).weightedTraceCost_horizontalFrontierTrace,
    densityOneNontangentialCompetitor_graph_cost,
    densityOneNontangentialCompetitor_horizontal_cost,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ (1 + Real.sqrt 2) * s.r) s.r_nonneg]
  congr 1
  ring


/-- The regular vertical incident ray and horizontal interface segment meet
only at the exterior corner. -/
theorem exterior_incident_meets_interface_only_at_corner (s : Scale) :
    exteriorIncidentTrace s ∩ interfaceTrace s = {(0, 1)} := by
  ext p
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨x, hx, hp⟩⟩
    have hx0 : x = 0 := by simpa using congrArg Prod.fst hp
    have hy1 : y = 1 := by simpa using (congrArg Prod.snd hp).symm
    subst x
    subst y
    simp
  · intro hp
    have hpEq : p = (0, 1) := by simpa using hp
    subst p
    constructor
    · exact ⟨1, ⟨le_rfl, by linarith [s.r_pos]⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, s.r_nonneg⟩, rfl⟩

/-- Independent density-one specimen: its incident ray meets the interface
only at the named corner. -/
theorem densityOne_incident_meets_interface_only_at_corner (s : Scale) :
    densityOneIncidentTrace s ∩ interfaceTrace s = {(0, 1)} := by
  ext p
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨x, hx, hp⟩⟩
    have hx0 : x = 0 := by simpa using congrArg Prod.fst hp
    have hy1 : y = 1 := by simpa using (congrArg Prod.snd hp).symm
    subst x
    subst y
    simp
  · intro hp
    have hpEq : p = (0, 1) := by simpa using hp
    subst p
    constructor
    · exact ⟨1, ⟨by linarith [s.r_pos], le_rfl⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, s.r_nonneg⟩, rfl⟩

/-- The parameterized incident ray is regular and transverse to the
parameterized interface segment. -/
theorem incident_ray_is_regular_and_nontangential :
    HasDerivAt (fun y : ℝ => ((0, y) : PlanePoint)) (0, 1) 1 ∧
      HasDerivAt (fun x : ℝ => ((x, 1) : PlanePoint)) (1, 0) 0 ∧
      (0 : ℝ) * 0 - 1 * 1 ≠ 0 := by
  refine ⟨(hasDerivAt_const 1 (0 : ℝ)).prodMk (hasDerivAt_id 1), ?_, by norm_num⟩
  exact (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 (1 : ℝ))

/-- Both actual density-one frontiers remain entirely in the closed strip. -/
theorem densityOne_complete_frontiers_have_density_one (s : Scale) :
    ∀ p ∈ frontier (densityOneNontangentialSpecimen s).carrier ∪
        frontier (densityOneNontangentialCompetitor s).carrier,
      StripDensity 2 p = 1 := by
  intro p hp
  rcases hp with hp | hp
  · have hc :=
      (densityOneNontangentialSpecimen s).isClosed_carrier.frontier_subset hp
    rw [densityOneNontangentialSpecimen_carrier] at hc
    have hy0 : 0 ≤ p.2 := by
      linarith [s.r_le_one, hc.2.2.1]
    have habs : |p.2| ≤ 1 := by
      rw [abs_of_nonneg hy0]
      exact hc.2.2.2
    simp [StripDensity, habs]
  · have hc :=
      (densityOneNontangentialCompetitor s).isClosed_carrier.frontier_subset hp
    rw [densityOneNontangentialCompetitor_carrier] at hc
    have hy0 : 0 ≤ p.2 := by linarith [s.r_le_one, hc.1]
    have habs : |p.2| ≤ 1 := by
      rw [abs_of_nonneg hy0]
      exact hc.2.1
    simp [StripDensity, habs]

lemma two_mul_sqrt_two_lt_three : 2 * Real.sqrt 2 < 3 := by
  have hs0 := Real.sqrt_nonneg 2
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have hs0 := Real.sqrt_nonneg 2
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- Exact first-order weighted-frontier change for the literal exterior
corner cut.  Every retained side has already been included in the two complete
frontier costs. -/
theorem exteriorInterface_exact_frontier_change (s : Scale) :
    weightedTraceCost 2 (frontier (exteriorInterfaceCompetitor s).carrier) +
        ENNReal.ofReal ((3 - 2 * Real.sqrt 2) * s.r) =
      weightedTraceCost 2 (frontier (exteriorInterfaceSpecimen s).carrier) := by
  rw [exteriorInterfaceCompetitor_complete_frontier_cost,
    exteriorInterfaceSpecimen_complete_frontier_cost,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ (4 + 2 * Real.sqrt 2) * s.r)
      (by
        have hgain : 0 < 3 - 2 * Real.sqrt 2 := by
          linarith [two_mul_sqrt_two_lt_three]
        exact mul_nonneg hgain.le s.r_nonneg)]
  congr 1
  ring

theorem exteriorInterface_strict_frontier_gain (s : Scale) :
    weightedTraceCost 2 (frontier (exteriorInterfaceCompetitor s).carrier) <
      weightedTraceCost 2 (frontier (exteriorInterfaceSpecimen s).carrier) := by
  rw [exteriorInterfaceCompetitor_complete_frontier_cost,
    exteriorInterfaceSpecimen_complete_frontier_cost]
  apply (ENNReal.ofReal_lt_ofReal_iff
    (by nlinarith [s.r_pos] : (0 : ℝ) < 7 * s.r)).2
  have hcoef : 4 + 2 * Real.sqrt 2 < 7 := by
    linarith [two_mul_sqrt_two_lt_three]
  exact mul_lt_mul_of_pos_right hcoef s.r_pos

/-- Exact first-order change for the independently defined density-one
nontangential specimen. -/
theorem densityOne_exact_frontier_change (s : Scale) :
    weightedTraceCost 2
        (frontier (densityOneNontangentialCompetitor s).carrier) +
        ENNReal.ofReal ((2 - Real.sqrt 2) * s.r) =
      weightedTraceCost 2
        (frontier (densityOneNontangentialSpecimen s).carrier) := by
  rw [densityOneNontangentialCompetitor_complete_frontier_cost,
    densityOneNontangentialSpecimen_complete_frontier_cost,
    ← ENNReal.ofReal_add
      (by nlinarith [Real.sqrt_nonneg 2, s.r_nonneg] :
        (0 : ℝ) ≤ (2 + Real.sqrt 2) * s.r)
      (by
        have hgain : 0 < 2 - Real.sqrt 2 := by linarith [sqrt_two_lt_two]
        exact mul_nonneg hgain.le s.r_nonneg)]
  congr 1
  ring

theorem densityOne_strict_frontier_gain (s : Scale) :
    weightedTraceCost 2
        (frontier (densityOneNontangentialCompetitor s).carrier) <
      weightedTraceCost 2
        (frontier (densityOneNontangentialSpecimen s).carrier) := by
  rw [densityOneNontangentialCompetitor_complete_frontier_cost,
    densityOneNontangentialSpecimen_complete_frontier_cost]
  apply (ENNReal.ofReal_lt_ofReal_iff
    (by nlinarith [s.r_pos] : (0 : ℝ) < 4 * s.r)).2
  have hcoef : 2 + Real.sqrt 2 < 4 := by linarith [sqrt_two_lt_two]
  exact mul_lt_mul_of_pos_right hcoef s.r_pos


lemma volume_real_Icc_of_le {a b : ℝ} (hab : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  rw [measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma exteriorInterfaceSpecimen_horizontalSection (s : Scale) (y : ℝ) :
    horizontalSection (exteriorInterfaceSpecimen s).carrier y =
      if y ∈ Icc 1 (1 + s.r) then Icc 0 s.r else ∅ := by
  rw [exteriorInterfaceSpecimen_carrier]
  ext x
  change (0 ≤ x ∧ x ≤ s.r ∧ 1 ≤ y ∧ y ≤ 1 + s.r) ↔
    x ∈ if y ∈ Icc 1 (1 + s.r) then Icc 0 s.r else ∅
  by_cases hy : y ∈ Icc 1 (1 + s.r)
  · rw [if_pos hy]
    change _ ↔ 0 ≤ x ∧ x ≤ s.r
    rcases hy with ⟨hy₁, hy₂⟩
    tauto
  · rw [if_neg hy]
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hy ⟨h.2.2.1, h.2.2.2⟩
lemma exteriorInterfaceCompetitor_horizontalSection (s : Scale) (y : ℝ) :
    horizontalSection (exteriorInterfaceCompetitor s).carrier y =
      if y ∈ Icc 1 (1 + s.r) then Icc (1 + s.r - y) s.r else ∅ := by
  rw [exteriorInterfaceCompetitor_carrier]
  ext x
  change (1 ≤ y ∧ y ≤ 1 + s.r ∧
      1 + s.r - y ≤ x ∧ x ≤ s.r) ↔
    x ∈ if y ∈ Icc 1 (1 + s.r) then
      Icc (1 + s.r - y) s.r else ∅
  by_cases hy : y ∈ Icc 1 (1 + s.r)
  · rw [if_pos hy]
    change _ ↔ 1 + s.r - y ≤ x ∧ x ≤ s.r
    rcases hy with ⟨hy₁, hy₂⟩
    tauto
  · rw [if_neg hy]
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hy ⟨h.1, h.2.1⟩
lemma densityOneNontangentialSpecimen_horizontalSection (s : Scale) (y : ℝ) :
    horizontalSection (densityOneNontangentialSpecimen s).carrier y =
      if y ∈ Icc (1 - s.r) 1 then Icc 0 s.r else ∅ := by
  rw [densityOneNontangentialSpecimen_carrier]
  ext x
  change (0 ≤ x ∧ x ≤ s.r ∧ 1 - s.r ≤ y ∧ y ≤ 1) ↔
    x ∈ if y ∈ Icc (1 - s.r) 1 then Icc 0 s.r else ∅
  by_cases hy : y ∈ Icc (1 - s.r) 1
  · rw [if_pos hy]
    change _ ↔ 0 ≤ x ∧ x ≤ s.r
    rcases hy with ⟨hy₁, hy₂⟩
    tauto
  · rw [if_neg hy]
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hy ⟨h.2.2.1, h.2.2.2⟩
lemma densityOneNontangentialCompetitor_horizontalSection (s : Scale) (y : ℝ) :
    horizontalSection (densityOneNontangentialCompetitor s).carrier y =
      if y ∈ Icc (1 - s.r) 1 then
        Icc (y - (1 - s.r)) s.r else ∅ := by
  rw [densityOneNontangentialCompetitor_carrier]
  ext x
  change (1 - s.r ≤ y ∧ y ≤ 1 ∧
      y - (1 - s.r) ≤ x ∧ x ≤ s.r) ↔
    x ∈ if y ∈ Icc (1 - s.r) 1 then
      Icc (y - (1 - s.r)) s.r else ∅
  by_cases hy : y ∈ Icc (1 - s.r) 1
  · rw [if_pos hy]
    change _ ↔ y - (1 - s.r) ≤ x ∧ x ≤ s.r
    rcases hy with ⟨hy₁, hy₂⟩
    tauto
  · rw [if_neg hy]
    simp only [mem_empty_iff_false, iff_false]
    intro h
    exact hy ⟨h.1, h.2.1⟩

lemma volume_real_Ioo_of_le {a b : ℝ} (hab : a ≤ b) :
    volume.real (Ioo a b) = b - a := by
  rw [measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem exteriorInterfaceSpecimen_weightedArea (s : Scale) :
    WeightedArea 2 (exteriorInterfaceSpecimen s).carrier = 2 * s.r ^ 2 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    (exteriorInterfaceSpecimen s).isClosed_carrier.measurableSet
    (exteriorInterfaceSpecimen s).isBounded_carrier.measure_lt_top.ne]
  have hintegrand :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real
          (horizontalSection (exteriorInterfaceSpecimen s).carrier y)) =
      (Icc 1 (1 + s.r)).indicator
        (fun y : ℝ => StripDensity 2 (0, y) * s.r) := by
    funext y
    rw [exteriorInterfaceSpecimen_horizontalSection]
    by_cases hy : y ∈ Icc 1 (1 + s.r)
    · rw [if_pos hy, Set.indicator_of_mem hy,
        volume_real_Icc_of_le s.r_nonneg]
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  rw [hintegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioo]
  have hdensity :
      (∫ y in Ioo 1 (1 + s.r), StripDensity 2 (0, y) * s.r) =
        ∫ _y in Ioo 1 (1 + s.r), 2 * s.r := by
    apply setIntegral_congr_fun measurableSet_Ioo
    rintro y ⟨hy₁, hy₂⟩
    have hout : ¬|y| ≤ 1 := by
      rw [abs_of_pos (lt_trans zero_lt_one hy₁)]
      linarith
    simp [StripDensity, hout]
  rw [hdensity, setIntegral_const]
  simp only [smul_eq_mul]
  rw [volume_real_Ioo_of_le (by linarith [s.r_pos])]
  ring


theorem exteriorInterfaceCompetitor_weightedArea (s : Scale) :
    WeightedArea 2 (exteriorInterfaceCompetitor s).carrier = s.r ^ 2 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    (exteriorInterfaceCompetitor s).isClosed_carrier.measurableSet
    (exteriorInterfaceCompetitor s).isBounded_carrier.measure_lt_top.ne]
  have hintegrand :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real
          (horizontalSection (exteriorInterfaceCompetitor s).carrier y)) =
      (Icc 1 (1 + s.r)).indicator
        (fun y : ℝ => StripDensity 2 (0, y) * (y - 1)) := by
    funext y
    rw [exteriorInterfaceCompetitor_horizontalSection]
    by_cases hy : y ∈ Icc 1 (1 + s.r)
    · have hwidth : 1 + s.r - y ≤ s.r := by linarith [hy.1]
      rw [if_pos hy, Set.indicator_of_mem hy,
        volume_real_Icc_of_le hwidth]
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  rw [hintegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioo]
  have hdensity :
      (∫ y in Ioo 1 (1 + s.r),
          StripDensity 2 (0, y) * (y - 1)) =
        ∫ y in Ioo 1 (1 + s.r), 2 * (y - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    rintro y ⟨hy₁, hy₂⟩
    have hout : ¬|y| ≤ 1 := by
      rw [abs_of_pos (lt_trans zero_lt_one hy₁)]
      linarith
    simp [StripDensity, hout]
  rw [hdensity, ← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [s.r_pos])]
  calc
    (∫ y : ℝ in 1..1 + s.r, 2 * (y - 1)) =
        (1 + s.r - 1) ^ 2 - (1 - 1) ^ 2 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => (y - 1) ^ 2) ?_ ?_
      · intro y hy
        convert ((hasDerivAt_id y).sub_const 1).pow 2 using 1
        · rfl
        · funext z
          rfl
        · norm_num [id_eq]
      · exact (by fun_prop : Continuous (fun y : ℝ => 2 * (y - 1)))
          |>.intervalIntegrable 1 (1 + s.r)
    _ = s.r ^ 2 := by ring


theorem densityOneNontangentialSpecimen_weightedArea (s : Scale) :
    WeightedArea 2 (densityOneNontangentialSpecimen s).carrier = s.r ^ 2 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    (densityOneNontangentialSpecimen s).isClosed_carrier.measurableSet
    (densityOneNontangentialSpecimen s).isBounded_carrier.measure_lt_top.ne]
  have hintegrand :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real
          (horizontalSection (densityOneNontangentialSpecimen s).carrier y)) =
      (Icc (1 - s.r) 1).indicator
        (fun y : ℝ => StripDensity 2 (0, y) * s.r) := by
    funext y
    rw [densityOneNontangentialSpecimen_horizontalSection]
    by_cases hy : y ∈ Icc (1 - s.r) 1
    · rw [if_pos hy, Set.indicator_of_mem hy,
        volume_real_Icc_of_le s.r_nonneg]
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  rw [hintegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioo]
  have hdensity :
      (∫ y in Ioo (1 - s.r) 1, StripDensity 2 (0, y) * s.r) =
        ∫ _y in Ioo (1 - s.r) 1, s.r := by
    apply setIntegral_congr_fun measurableSet_Ioo
    rintro y ⟨hy₁, hy₂⟩
    have hy0 : 0 < y := by
      have hbase : 0 ≤ 1 - s.r := by linarith [s.r_le_one]
      linarith
    have hinside : |y| ≤ 1 := by
      rw [abs_of_pos hy0]
      exact hy₂.le
    simp [StripDensity, hinside]
  rw [hdensity, setIntegral_const]
  simp only [smul_eq_mul]
  rw [volume_real_Ioo_of_le (by linarith [s.r_pos])]
  ring

theorem densityOneNontangentialCompetitor_weightedArea (s : Scale) :
    WeightedArea 2 (densityOneNontangentialCompetitor s).carrier =
      s.r ^ 2 / 2 := by
  rw [weightedArea_eq_integral_horizontalSections 2
    (densityOneNontangentialCompetitor s).isClosed_carrier.measurableSet
    (densityOneNontangentialCompetitor s).isBounded_carrier.measure_lt_top.ne]
  have hintegrand :
      (fun y : ℝ => StripDensity 2 (0, y) *
        volume.real
          (horizontalSection (densityOneNontangentialCompetitor s).carrier y)) =
      (Icc (1 - s.r) 1).indicator
        (fun y : ℝ => StripDensity 2 (0, y) * (1 - y)) := by
    funext y
    rw [densityOneNontangentialCompetitor_horizontalSection]
    by_cases hy : y ∈ Icc (1 - s.r) 1
    · have hwidth : y - (1 - s.r) ≤ s.r := by linarith [hy.2]
      rw [if_pos hy, Set.indicator_of_mem hy,
        volume_real_Icc_of_le hwidth]
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  rw [hintegrand, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioo]
  have hdensity :
      (∫ y in Ioo (1 - s.r) 1,
          StripDensity 2 (0, y) * (1 - y)) =
        ∫ y in Ioo (1 - s.r) 1, 1 - y := by
    apply setIntegral_congr_fun measurableSet_Ioo
    rintro y ⟨hy₁, hy₂⟩
    have hy0 : 0 < y := by
      have hbase : 0 ≤ 1 - s.r := by linarith [s.r_le_one]
      linarith
    have hinside : |y| ≤ 1 := by
      rw [abs_of_pos hy0]
      exact hy₂.le
    simp [StripDensity, hinside]
  rw [hdensity, ← integral_Icc_eq_integral_Ioo,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [s.r_pos])]
  calc
    (∫ y : ℝ in 1 - s.r..1, 1 - y) =
        (1 - 1 ^ 2 / 2) -
          ((1 - s.r) - (1 - s.r) ^ 2 / 2) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => y - y ^ 2 / 2) ?_ ?_
      · intro y hy
        convert (hasDerivAt_id y).sub
          (((hasDerivAt_id y).pow 2).div_const 2) using 1
        · rfl
        · norm_num [id_eq]
      · exact (by fun_prop : Continuous (fun y : ℝ => 1 - y))
          |>.intervalIntegrable (1 - s.r) 1
    _ = s.r ^ 2 / 2 := by ring


/-- The triangular competitors are literal cuts of their corresponding
rectangles, not independently priced trace surrogates. -/
theorem exteriorInterfaceCompetitor_subset_specimen (s : Scale) :
    (exteriorInterfaceCompetitor s).carrier ⊆
      (exteriorInterfaceSpecimen s).carrier := by
  rw [exteriorInterfaceCompetitor_carrier, exteriorInterfaceSpecimen_carrier]
  intro p hp
  exact ⟨by linarith [hp.2.1, hp.2.2.1], hp.2.2.2, hp.1, hp.2.1⟩

theorem densityOneNontangentialCompetitor_subset_specimen (s : Scale) :
    (densityOneNontangentialCompetitor s).carrier ⊆
      (densityOneNontangentialSpecimen s).carrier := by
  rw [densityOneNontangentialCompetitor_carrier,
    densityOneNontangentialSpecimen_carrier]
  intro p hp
  exact ⟨by linarith [hp.1, hp.2.2.1], hp.2.2.2, hp.1, hp.2.1⟩

theorem interfaceTrace_subset_exterior_specimen_frontier (s : Scale) :
    interfaceTrace s ⊆ frontier (exteriorInterfaceSpecimen s).carrier := by
  rw [← exteriorInterfaceSpecimen_lowerOuterTrace]
  exact (exteriorInterfaceSpecimen s).lowerOuterTrace_subset_frontier_carrier

theorem exteriorIncidentTrace_subset_specimen_frontier (s : Scale) :
    exteriorIncidentTrace s ⊆
      frontier (exteriorInterfaceSpecimen s).carrier := by
  intro p hp
  apply (exteriorInterfaceSpecimen s).graphTrace_subset_frontier_carrier
  rw [exteriorInterfaceSpecimen_graphTrace]
  exact Or.inl hp

theorem exteriorShortcutTrace_subset_competitor_frontier (s : Scale) :
    exteriorShortcutTrace s ⊆
      frontier (exteriorInterfaceCompetitor s).carrier := by
  intro p hp
  apply (exteriorInterfaceCompetitor s).graphTrace_subset_frontier_carrier
  rw [exteriorInterfaceCompetitor_graphTrace]
  exact Or.inl hp

theorem densityOneIncidentTrace_subset_specimen_frontier (s : Scale) :
    densityOneIncidentTrace s ⊆
      frontier (densityOneNontangentialSpecimen s).carrier := by
  intro p hp
  apply (densityOneNontangentialSpecimen s).graphTrace_subset_frontier_carrier
  rw [densityOneNontangentialSpecimen_graphTrace]
  exact Or.inl hp

theorem densityOneShortcutTrace_subset_competitor_frontier (s : Scale) :
    densityOneShortcutTrace s ⊆
      frontier (densityOneNontangentialCompetitor s).carrier := by
  intro p hp
  apply (densityOneNontangentialCompetitor s).graphTrace_subset_frontier_carrier
  rw [densityOneNontangentialCompetitor_graphTrace]
  exact Or.inl hp

/-- Exact actual weighted-area loss for the exterior cut. -/
theorem exteriorInterface_weightedArea_defect_exact (s : Scale) :
    |WeightedArea 2 (exteriorInterfaceSpecimen s).carrier -
      WeightedArea 2 (exteriorInterfaceCompetitor s).carrier| = s.r ^ 2 := by
  rw [exteriorInterfaceSpecimen_weightedArea,
    exteriorInterfaceCompetitor_weightedArea]
  have hsquare : 0 ≤ s.r ^ 2 := sq_nonneg s.r
  rw [abs_of_nonneg (by linarith)]
  ring

/-- Exact actual weighted-area loss for the density-one cut. -/
theorem densityOne_weightedArea_defect_exact (s : Scale) :
    |WeightedArea 2 (densityOneNontangentialSpecimen s).carrier -
      WeightedArea 2 (densityOneNontangentialCompetitor s).carrier| =
        s.r ^ 2 / 2 := by
  rw [densityOneNontangentialSpecimen_weightedArea,
    densityOneNontangentialCompetitor_weightedArea]
  have hsquare : 0 ≤ s.r ^ 2 := sq_nonneg s.r
  rw [abs_of_nonneg (by linarith)]
  ring

/-- A common scale-independent constant `C = 1` controls both actual
weighted-area defects. -/
theorem weightedArea_defects_le_one_mul_r_sq (s : Scale) :
    |WeightedArea 2 (exteriorInterfaceSpecimen s).carrier -
        WeightedArea 2 (exteriorInterfaceCompetitor s).carrier| ≤
          1 * s.r ^ 2 ∧
      |WeightedArea 2 (densityOneNontangentialSpecimen s).carrier -
        WeightedArea 2 (densityOneNontangentialCompetitor s).carrier| ≤
          1 * s.r ^ 2 := by
  rw [exteriorInterface_weightedArea_defect_exact,
    densityOne_weightedArea_defect_exact]
  constructor
  · simp
  · have hsquare : 0 ≤ s.r ^ 2 := sq_nonneg s.r
    nlinarith

/-- Checkpoint-facing aggregate.  This is a conditional local comparison only;
it asserts neither source minimality nor global configuration classification. -/
theorem lambdaTwo_literal_corner_shortening_gate (s : Scale) :
    Bornology.IsBounded (exteriorInterfaceSpecimen s).carrier ∧
      Bornology.IsBounded (exteriorInterfaceCompetitor s).carrier ∧
      weightedTraceCost 2 (interfaceTrace s) = ENNReal.ofReal s.r ∧
      interfaceTrace s ⊆ frontier (exteriorInterfaceSpecimen s).carrier ∧
      exteriorIncidentTrace s ⊆
        frontier (exteriorInterfaceSpecimen s).carrier ∧
      exteriorShortcutTrace s ⊆
        frontier (exteriorInterfaceCompetitor s).carrier ∧
      weightedTraceCost 2
          (frontier (exteriorInterfaceCompetitor s).carrier) <
        weightedTraceCost 2
          (frontier (exteriorInterfaceSpecimen s).carrier) ∧
      |WeightedArea 2 (exteriorInterfaceSpecimen s).carrier -
        WeightedArea 2 (exteriorInterfaceCompetitor s).carrier| ≤ s.r ^ 2 ∧
      Bornology.IsBounded (densityOneNontangentialSpecimen s).carrier ∧
      Bornology.IsBounded (densityOneNontangentialCompetitor s).carrier ∧
      (∀ p ∈ frontier (densityOneNontangentialSpecimen s).carrier ∪
          frontier (densityOneNontangentialCompetitor s).carrier,
        StripDensity 2 p = 1) ∧
      weightedTraceCost 2
          (frontier (densityOneNontangentialCompetitor s).carrier) <
        weightedTraceCost 2
          (frontier (densityOneNontangentialSpecimen s).carrier) ∧
      |WeightedArea 2 (densityOneNontangentialSpecimen s).carrier -
        WeightedArea 2 (densityOneNontangentialCompetitor s).carrier| ≤
          s.r ^ 2 := by
  refine ⟨(exteriorInterfaceSpecimen s).isBounded_carrier,
    (exteriorInterfaceCompetitor s).isBounded_carrier,
    weightedTraceCost_interfaceTrace s,
    interfaceTrace_subset_exterior_specimen_frontier s,
    exteriorIncidentTrace_subset_specimen_frontier s,
    exteriorShortcutTrace_subset_competitor_frontier s,
    exteriorInterface_strict_frontier_gain s,
    ?_, (densityOneNontangentialSpecimen s).isBounded_carrier,
    (densityOneNontangentialCompetitor s).isBounded_carrier,
    densityOne_complete_frontiers_have_density_one s,
    densityOne_strict_frontier_gain s, ?_⟩
  · simpa using (weightedArea_defects_le_one_mul_r_sq s).1
  · simpa using (weightedArea_defects_le_one_mul_r_sq s).2

end CMVRelaxation.LiteralCornerShortening
