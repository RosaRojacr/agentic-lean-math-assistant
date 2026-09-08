theorem succ_add_calibration (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  exact Nat.succ_add m n

#print axioms succ_add_calibration
