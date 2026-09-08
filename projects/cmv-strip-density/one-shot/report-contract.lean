import RangeReduction

example : ∀ {lam x : ℝ},
    (1.2581840884 : ℝ) ≤ lam → 0 < x → 1 / lam < g x := by
  intro lam x hlam hx
  exact cmv_range_reduction hlam hx

example : ∀ {lam : ℝ} (candidate : FourArcCandidate lam),
    candidate.SatisfiesCMVTypeIVHypotheses →
    candidate.IsWeightedPerimeterMinimizer →
    1 < lam ∧ lam < (1.2581840884 : ℝ) := by
  intro lam candidate hcandidate hmin
  exact cmv_type_four_range_reduction candidate hcandidate hmin

example {lam : ℝ} (assembly : TypeThreeAssembly lam) :
    (assembly.h < 1 / 2 →
      assembly.branch = .major ∧
        Real.pi / 2 < assembly.outerAngle ∧ 0 < assembly.bottomChord) ∧
    (assembly.h = 1 / 2 →
      assembly.branch = .semicircular ∧
        assembly.outerAngle = Real.pi / 2 ∧ assembly.bottomChord = 0) ∧
    (1 / 2 < assembly.h →
      assembly.branch = .minor ∧
        assembly.outerAngle < Real.pi / 2 ∧ 0 < assembly.bottomChord) :=
  cmv_type_three_branch_contract assembly

example {lam : ℝ} (hlam : (1.2581840884 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) : False :=
  cmv_type_four_not_minimizing hlam candidate hcandidate hmin

#print axioms ell
#print axioms area
#print axioms area_strictMonoOn
#print axioms area_surjOn
#print axioms hasDerivAt_arc
#print axioms hasDerivAt_g
#print axioms g_deriv_neg
#print axioms g_deriv_pos
#print axioms θstar_spec
#print axioms θstar_unique
#print axioms min_g_eq_three_mul_cos_θstar
#print axioms cmv_comparison_bound_optimized
#print axioms FourArcCandidate.cap_replacement_preserves_area
#print axioms FourArcCandidate.cap_replacement_perimeter_difference
#print axioms FourArcCandidate.cap_replacement_strictly_improves
#print axioms fourArc_frontier_weightedPerimeter_eq
#print axioms replacement_frontier_weightedPerimeter_eq
#print axioms TypeThreeAssembly.isClosed_carrier
#print axioms TypeThreeAssembly.branch_complete
#print axioms cmv_type_three_branch_contract
#print axioms cmv_type_four_not_minimizing
#print axioms type_four_minimizer_open_range
#print axioms cmv_range_reduction
#print axioms cmv_type_four_range_reduction
