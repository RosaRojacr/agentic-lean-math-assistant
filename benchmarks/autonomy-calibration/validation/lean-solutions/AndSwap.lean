theorem and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.right, h.left⟩

#print axioms and_swap_calibration
