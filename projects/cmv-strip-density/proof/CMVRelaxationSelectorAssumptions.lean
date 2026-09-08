import CMVRelaxationSelector

namespace CMVRelaxation

#check exists_ge_of_liminf_lt
#check exists_smoothDomain_of_relaxedPerimeter_lt
#check unitDisk_exists_selected_approximant

#print axioms exists_ge_of_liminf_lt
#print axioms exists_smoothDomain_of_relaxedPerimeter_lt
#print axioms unitDisk_exists_selected_approximant

/-- Compiled contract: the public selector specializes directly to the actual
unit disk and its literal relaxation. -/
example (lam q epsilon : ℝ) (hepsilon : 0 < epsilon)
    (h : relaxedPerimeter lam unitDisk < ENNReal.ofReal q) :
    ∃ U : Set PlanePoint,
      IsSmoothDomain U ∧
      characteristicDistance U unitDisk < ENNReal.ofReal epsilon ∧
      smoothCost lam U < ENNReal.ofReal q :=
  exists_smoothDomain_of_relaxedPerimeter_lt lam
    isOpen_unitDisk.measurableSet.nullMeasurableSet hepsilon h

end CMVRelaxation
