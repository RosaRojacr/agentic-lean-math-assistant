import CMVAnnularGapRecovery

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CMVRelaxation.AnnularGapRecovery

#print axioms frontier_domain
#print axioms domain_frontier_circles_pairwise_disjoint
#print axioms isSmoothDomain_domain
#print axioms hausdorffMeasure_radialCircle_eq
#print axioms smoothCost_domain
#print axioms characteristicDistance_domain
#print axioms sequence_converges
#print axioms sequence_cost
#print axioms unitDisk_relaxed_le_smoothCost_lt_sequenceCost
#print axioms sequence_cost_ne_relaxedPerimeter
#print axioms not_globalConvergenceForcesExactRecovery_unitDisk
#print axioms unitDisk_has_exactMinimizing_sequence
#print axioms dilationCutoff_contDiff
#print axioms dilationField_hasCompactSupport
#print axioms dilationField_lipschitz
#print axioms deformationRadius_pos
#print axioms deformation_zero_apply
#print axioms deformation_movedSet_subset
#print axioms deformation_compactlySupported_in_unitDisk
#print axioms deformation_on_core
#print axioms deformation_image_radialCircle
#print axioms deformation_image_unitDisk
#print axioms deformation_image_densityOneRegion
#print axioms mem_densityOneRegion_iff_stripDensity_two_eq_one
#print axioms frontier_deformation_image_domain
#print axioms smoothCost_deformation_image_domain
#print axioms transportedSequence_converges
#print axioms transportedSequence_termCost_eq_add
#print axioms transportedSequence_cost_eq_add
#print axioms transportedSequence_cost_lt_top
#print axioms sequence_cost_lt_top
#print axioms transportedSequence_termCost_lt_top
#print axioms positiveStep_tendsto_zero
#print axioms positiveAmbientImage_sequence_normalizedCost_tendsto
#print axioms not_globalConvergenceForcesZeroFixedTargetTransport

example {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    IsSmoothDomain (domain epsilon) :=
  isSmoothDomain_domain hepsilon hepsilon_le

example :
    relaxedPerimeter 2 unitDisk ≤ smoothCost 2 unitDisk ∧
      smoothCost 2 unitDisk < sequence.cost 2 :=
  unitDisk_relaxed_le_smoothCost_lt_sequenceCost

example : ¬ GlobalConvergenceForcesExactRecovery 2 unitDisk :=
  not_globalConvergenceForcesExactRecovery_unitDisk

/-- Compiled applicability contract for the literal globally invertible smooth
ambient family and unchanged target. -/
example (t : ℝ) (ht : |t| < deformationRadius) :
    (deformation t ht).movedSet ⊆ dilationSupportRegion ∧
      deformation t ht '' unitDisk = unitDisk ∧
      deformation t ht '' densityOneRegion = densityOneRegion :=
  ⟨deformation_movedSet_subset t ht, deformation_image_unitDisk t ht,
    deformation_image_densityOneRegion t ht⟩

/-- Compiled exact-frontier and pre-liminf increment contract. -/
example {t : ℝ} (ht : |t| < deformationRadius) (htPos : 0 < t)
    (n : ℕ) :
    frontier
        (deformation t ht '' domain (epsilon n)) =
          radialCircle ((1 + t) * innerRadius (epsilon n)) ∪
            radialCircle ((1 + t) * outerRadius (epsilon n)) ∪
              radialCircle 1 ∧
      smoothCost 2 ((transportedSequence t ht).carrier n) =
        smoothCost 2 (sequence.carrier n) +
          ENNReal.ofReal (Real.pi * t) :=
  ⟨frontier_deformation_image_domain ht (epsilon_pos n) (epsilon_le n),
    transportedSequence_termCost_eq_add ht htPos n⟩

/-- One named contract keeps the witness's quantifiers and order of limits
explicit.  The fixed-parameter termwise identities precede the sequence
liminf identities; the deformation parameter tends to zero only afterward.
The arbitrary recovery is strictly non-minimizing, while a separate exact
minimizing selector for the same target still exists. -/
theorem complete_counterexample_scope_contract :
    sequence.ConvergesTo unitDisk ∧
      (∀ n, smoothCost 2 (sequence.carrier n) < ⊤) ∧
      sequence.cost 2 < ⊤ ∧
      (relaxedPerimeter 2 unitDisk ≤ smoothCost 2 unitDisk ∧
        smoothCost 2 unitDisk < sequence.cost 2) ∧
      sequence.cost 2 ≠ relaxedPerimeter 2 unitDisk ∧
      (∀ (t : ℝ) (ht : |t| < deformationRadius), 0 < t →
        (transportedSequence t ht).ConvergesTo unitDisk ∧
          (∀ n,
            smoothCost 2 ((transportedSequence t ht).carrier n) =
                smoothCost 2 (sequence.carrier n) +
                  ENNReal.ofReal (Real.pi * t) ∧
            smoothCost 2 ((transportedSequence t ht).carrier n) < ⊤) ∧
          (transportedSequence t ht).cost 2 =
            sequence.cost 2 + ENNReal.ofReal (Real.pi * t) ∧
          (transportedSequence t ht).cost 2 < ⊤) ∧
      Tendsto positiveStep atTop (𝓝 0) ∧
      Tendsto
        (fun k => (((positiveAmbientImage sequence k).cost 2).toReal -
          (sequence.cost 2).toReal) / positiveStep k)
        atTop (𝓝 Real.pi) ∧
      Real.pi ≠ 0 ∧
      ¬ GlobalConvergenceForcesExactRecovery 2 unitDisk ∧
      ¬ GlobalConvergenceForcesZeroFixedTargetTransport ∧
      (∃ A : SmoothSequence,
        NullMeasurableSet unitDisk volume ∧
        A.ConvergesTo unitDisk ∧
        Tendsto (fun n => smoothCost 2 (A.carrier n))
          atTop (𝓝 (relaxedPerimeter 2 unitDisk)) ∧
        A.cost 2 = relaxedPerimeter 2 unitDisk ∧
        ∀ n, smoothCost 2 (A.carrier n) < ⊤) := by
  refine ⟨sequence_converges, ?_, sequence_cost_lt_top,
    unitDisk_relaxed_le_smoothCost_lt_sequenceCost,
    sequence_cost_ne_relaxedPerimeter, ?_,
    positiveStep_tendsto_zero,
    positiveAmbientImage_sequence_normalizedCost_tendsto, Real.pi_ne_zero,
    not_globalConvergenceForcesExactRecovery_unitDisk,
    not_globalConvergenceForcesZeroFixedTargetTransport,
    unitDisk_has_exactMinimizing_sequence⟩
  · intro n
    rw [sequence_termCost]
    exact ENNReal.ofReal_lt_top
  · intro t ht htPos
    refine ⟨transportedSequence_converges t ht, ?_,
      transportedSequence_cost_eq_add ht htPos,
      transportedSequence_cost_lt_top t ht⟩
    intro n
    exact ⟨transportedSequence_termCost_eq_add ht htPos n,
      transportedSequence_termCost_lt_top t ht n⟩

/-- The annular witness's radial generating field has a genuinely nonzero
horizontal component on its core. -/
theorem dilationField_not_fst_eq_zero :
    ¬ ∀ p : PlanePoint, (dilationField p).1 = 0 := by
  intro hzero
  have hp : ((1 / 4 : ℝ), (0 : ℝ)) ∈ dilationCore := by
    norm_num [dilationCore, radialClosedDisk, radiusSq]
  have hcore := dilationField_eq_self hp
  have h := hzero ((1 / 4 : ℝ), (0 : ℝ))
  rw [hcore] at h
  norm_num at h


#print axioms complete_counterexample_scope_contract
#print axioms dilationField_not_fst_eq_zero
end CMVRelaxation.AnnularGapRecovery
