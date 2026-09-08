/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Frozen scalar stress-gate grid

Exact rational definitions for strategy-00040's thirteen bands, 64 closed
subslabs per band, and compulsory stress inventory.  These declarations fix the
grid; they prove no analytic sign certificate.
-/

namespace NearOneScalarGrid

/-- The denominator inherited from the proved near-one seam. -/
def n : ℚ := 126334

/-- Left endpoint of scalar band `j`. -/
def bandLower (j : ℕ) : ℚ := 2 ^ (j + 1) / n

/-- Right endpoint of scalar band `j`, capped at `1/10`. -/
def bandUpper (j : ℕ) : ℚ := min (2 ^ (j + 2) / n) (1 / 10)

/-- Left endpoint of zero-based cell `k` in band `j`. -/
def cellLower (j k : ℕ) : ℚ :=
  bandLower j + k / 64 * (bandUpper j - bandLower j)

/-- Right endpoint of zero-based cell `k` in band `j`. -/
def cellUpper (j k : ℕ) : ℚ :=
  bandLower j + (k + 1) / 64 * (bandUpper j - bandLower j)

/-- Exactly the frozen target inventory: thirteen bands by 64 cells. -/
abbrev TargetCell := Fin 13 × Fin 64

/-- The remote stress slab is outside the target inventory. -/
def remoteLower : ℚ := 1 / 10

def remoteUpper : ℚ := 101 / 1000

/-- Retained weak-face density interval used only to select stress cells. -/
def weakDeltaLower : ℚ := (1024 / n) ^ 3 * (35391 / 1280)

def weakDeltaUpper : ℚ := (1024 / n) ^ 3 * (9287 / 320)

/-- The target inventory has exactly 832 distinct subslabs. -/
theorem targetCell_count : Fintype.card TargetCell = 832 := by
  norm_num

/-- Adjacent cells share their exact rational endpoint. -/
theorem cell_adjacency (j k : ℕ) : cellUpper j k = cellLower j (k + 1) := by
  unfold cellUpper cellLower
  push_cast
  ring

/-- Cell zero starts at the band's left endpoint. -/
theorem cell_zero_lower (j : ℕ) : cellLower j 0 = bandLower j := by
  simp [cellLower]

/-- Cell 63 ends at the band's right endpoint. -/
theorem cell_sixtyThree_upper (j : ℕ) : cellUpper j 63 = bandUpper j := by
  unfold cellUpper
  norm_num

/-- The first twelve bands are exactly adjacent; only the last is capped. -/
theorem band_adjacency {j : ℕ} (hj : j < 12) :
    bandUpper j = bandLower (j + 1) := by
  interval_cases j <;> norm_num [bandUpper, bandLower, n]

/-- Exact seam-crossing stress cell required by the strategy contract. -/
theorem seam_cell_ten :
    cellLower 0 10 = 37 / (16 * n) ∧
      cellUpper 0 10 = 75 / (32 * n) := by
  norm_num [cellLower, cellUpper, bandLower, bandUpper, n, min_def]

/-- Exact rational boundaries around the three weak-region stress cells. -/
theorem bandTen_stress_boundaries :
    cellUpper 10 31 = 3072 / n ∧
      cellLower 10 32 = 3072 / n ∧
      cellUpper 10 32 = 3104 / n ∧
      cellLower 10 33 = 3104 / n ∧
      cellUpper 10 33 = 3136 / n ∧
      cellLower 10 34 = 3136 / n ∧
      cellUpper 10 34 = 3168 / n ∧
      cellLower 10 35 = 3168 / n := by
  norm_num [cellLower, cellUpper, bandLower, bandUpper, n, min_def]

/-- Exact cube comparisons: the retained weak interval starts after cell 31,
intersects each of cells 32--34, and ends before cell 35. -/
theorem weak_selector_cube_comparisons :
    cellUpper 10 31 ^ 3 < weakDeltaLower ∧
      cellLower 10 32 ^ 3 ≤ weakDeltaUpper ∧
      weakDeltaLower ≤ cellUpper 10 32 ^ 3 ∧
      cellLower 10 33 ^ 3 ≤ weakDeltaUpper ∧
      weakDeltaLower ≤ cellUpper 10 33 ^ 3 ∧
      cellLower 10 34 ^ 3 ≤ weakDeltaUpper ∧
      weakDeltaLower ≤ cellUpper 10 34 ^ 3 ∧
      weakDeltaUpper < cellLower 10 35 ^ 3 := by
  norm_num [cellLower, cellUpper, bandLower, bandUpper, weakDeltaLower,
    weakDeltaUpper, n, min_def]

/-- Exact target endpoints: the first band begins at `2/n`, and the last band
ends at `1/10`. -/
theorem target_endpoints :
    bandLower 0 = 2 / n ∧ bandUpper 12 = 1 / 10 := by
  norm_num [bandLower, bandUpper, n, min_def]

/-- Exact remote stress interval and its strict positive width. -/
theorem remote_stress :
    remoteLower = 1 / 10 ∧ remoteUpper = 101 / 1000 ∧
      remoteLower < remoteUpper := by
  norm_num [remoteLower, remoteUpper]

end NearOneScalarGrid
