theorem append_nil_calibration {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x :: (xs ++ []) = x :: xs
    rw [ih]

#print axioms append_nil_calibration
