import CMVFiniteBandGraphProjection

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement
namespace CurvedGraphProjectionExample

open HeightGraphProjection.Region

/-- One actual finite band whose right endpoint is the curved graph
`x = 2 + y²`. -/
def region : Region where
  bandCount := 1
  bandCount_pos := by norm_num
  cuts := fun i => i.val
  cuts_strict := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ _ => 0
  right := fun _ _ y => 2 + y ^ 2
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
    have hC1 : ContDiff ℝ (0 + 1) (fun y : ℝ => 2 + y ^ 2) := by
      fun_prop
    have hderiv : Continuous (deriv (fun y : ℝ => 2 + y ^ 2)) :=
      ((contDiff_succ_iff_deriv (n := 0)).mp hC1).2.2.continuous
    exact ((continuous_const.add (hderiv.pow 2)).sqrt.integrableOn_Icc
      (μ := volume)).mono_set Ioo_subset_Icc_self
  width_nonneg := by intro i j y hy; positivity
  width_pos := by intro i j y hy; positivity
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

def band : Fin region.bandCount := ⟨0, by simp [region]⟩

def component : Fin (region.componentCount band) := ⟨0, by simp [region]⟩

/-- The selected genuinely curved right endpoint. -/
def curvedRightIndex : GraphIndex region := ⟨band, component, true⟩

@[simp] theorem curvedRightIndex_value (y : ℝ) :
    region.indexedGraphValue curvedRightIndex y = 2 + y ^ 2 := rfl

/-- A bounded open neighborhood prescribed around the compact curved trace. -/
def graphNeighborhood : Set PlanePoint :=
  Ioo (1 : ℝ) 4 ×ˢ Ioo (0 : ℝ) 1

@[simp] theorem isOpen_graphNeighborhood : IsOpen graphNeighborhood :=
  isOpen_Ioo.prod isOpen_Ioo

/-- The compact curved trace on heights `[1/4, 3/4]` produces a nonempty,
pairwise-disjoint finite tangent family on the literal `Region.carrier`, with
every window inside the prescribed bounded neighborhood. -/
theorem exists_nonempty_curved_tangent_family :
    ∃ (N : ℕ) (Q : Fin N → RigidProjectionPatch 2 region.carrier),
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      ∀ i, (Q i).window ⊆ graphNeighborhood := by
  have hsub : Icc (1 / 4 : ℝ) (3 / 4) ⊆
      Ioo (region.cuts curvedRightIndex.1.castSucc)
        (region.cuts curvedRightIndex.1.succ) := by
    intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hy.1, hy.2]
    simpa [region, curvedRightIndex, band] using hy'
  have hzone : ∀ y ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      HeightGraphProjection.Zone.insideStrip.Contains y := by
    intro y hy
    change -1 < y ∧ y < 1
    constructor <;> linarith [hy.1, hy.2]
  have hgraph :
      (fun y : ℝ => (region.indexedGraphValue curvedRightIndex y, y)) ''
          Icc (1 / 4 : ℝ) (3 / 4) ⊆ graphNeighborhood := by
    rintro _ ⟨y, hy, rfl⟩
    change (1 < 2 + y ^ 2 ∧ 2 + y ^ 2 < 4) ∧ 0 < y ∧ y < 1
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyupper : 0 ≤ 3 / 4 - y := by linarith [hy.2]
    have hmul := mul_nonneg hy0 hyupper
    constructor
    · constructor <;> nlinarith [sq_nonneg y]
    · constructor <;> linarith [hy.1, hy.2]
  obtain ⟨P, N, Q, _ha, _hb, _hside, _hPzone, _hEq,
      hN, hpair, hlocal, _hfinite, _hpay⟩ :=
    exists_pairwiseDisjoint_heightGraphPatches_payoff_ge_in_open
        region 2 (by norm_num) curvedRightIndex (by norm_num) hsub
        .insideStrip hzone isOpen_graphNeighborhood hgraph
        (by norm_num : (0 : ℝ) < 1)
  refine ⟨N, Q, hN, hpair, ?_⟩
  intro i
  exact (hlocal i).trans inter_subset_right

end CurvedGraphProjectionExample
end FiniteBandRearrangement
end CMVRelaxation
