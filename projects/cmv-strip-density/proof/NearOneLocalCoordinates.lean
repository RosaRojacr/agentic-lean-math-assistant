/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalJet

/-!
# Shared physical coordinates for the scale-local atlas

These scalar coordinates and their exact fourth-order jets are kept in a small
module so source reconstruction does not import the expensive generated
algebraic row.
-/

namespace NearOneLocalCoordinates

open NearOneLocalJet
noncomputable section

/-- Physical `z` coordinate used by every scale-local cell. -/
def physicalZ (s p u : ℝ) : ℝ := p + s * p ^ 2 + s ^ 2 * u

/-- Physical `a` coordinate used by every scale-local cell. -/
def physicalA (s p v : ℝ) : ℝ :=
  5 * p / 12 + s * (43 * p ^ 2 + 1056) / 144 + s ^ 2 * v

/-- Physical `b` coordinate used by every scale-local cell. -/
def physicalB (s p w : ℝ) : ℝ :=
  -44 + 19 * p ^ 2 / 24 + s * p * (295 * p ^ 2 - 14256) / 216 + s ^ 2 * w

/-- Exact coordinate jet for `physicalZ`. -/
def zJet (s p u : ℝ) : Jet4 s :=
  ⟨p, p ^ 2, u, 0, 0, physicalZ s p u, by
    simp only [physicalZ]
    ring⟩

/-- Exact coordinate jet for `physicalA`. -/
def aJet (s p v : ℝ) : Jet4 s :=
  ⟨5 * p / 12, (43 * p ^ 2 + 1056) / 144, v, 0, 0,
    physicalA s p v, by
      simp only [physicalA]
      ring⟩

/-- Exact coordinate jet for `physicalB`. -/
def bJet (s p w : ℝ) : Jet4 s :=
  ⟨-44 + 19 * p ^ 2 / 24, p * (295 * p ^ 2 - 14256) / 216, w, 0, 0,
    physicalB s p w, by
      simp only [physicalB]
      ring⟩

@[simp] theorem zJet_value (s p u : ℝ) : (zJet s p u).value = physicalZ s p u := rfl
@[simp] theorem aJet_value (s p v : ℝ) : (aJet s p v).value = physicalA s p v := rfl
@[simp] theorem bJet_value (s p w : ℝ) : (bJet s p w).value = physicalB s p w := rfl

end

end NearOneLocalCoordinates
