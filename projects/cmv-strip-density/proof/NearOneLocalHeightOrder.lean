/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneAnalyticSystem

namespace NearOneLocalHeightOrder

open NearOneAnalyticSystem

/-- The strict height order in the scale-local chart is exactly a polynomial
inequality in `s` and `R`; no endpoint-box bounds on `a` are required. -/
theorem height_order_iff {s a : ℝ} (hs0 : 0 < s) (_hs1 : s < 1) :
    (1 + halfCos (wCoord s a)) / 2 < halfCos s ↔
      2 < (1 - s ^ 2) * (rCoord s a) ^ 2 := by
  have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs0
  rw [show (1 + halfCos (wCoord s a)) / 2 =
      1 / (1 + (wCoord s a) ^ 2) by
    unfold halfCos
    field_simp
    ring]
  unfold halfCos
  rw [div_lt_div_iff₀ (by positivity : 0 < 1 + (wCoord s a) ^ 2)
    (by positivity : 0 < 1 + s ^ 2)]
  calc
    1 * (1 + s ^ 2) < (1 - s ^ 2) * (1 + (wCoord s a) ^ 2) ↔
        s ^ 2 * 2 < s ^ 2 * ((1 - s ^ 2) * (rCoord s a) ^ 2) := by
      unfold wCoord
      constructor <;> intro h <;> nlinarith only [h]
    _ ↔ 2 < (1 - s ^ 2) * (rCoord s a) ^ 2 := mul_lt_mul_iff_right₀ hsSq

end NearOneLocalHeightOrder
