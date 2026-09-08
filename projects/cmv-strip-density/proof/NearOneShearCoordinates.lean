/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneCuspTangent
/-!
# Tangent-centered shear coordinates at the near-one cusp

This module centers the complete normalized near-one root map on its forced cusp
tangent, applies the unit lower-triangular domain shear which diagonalizes the
cusp linearization, and reverses the third residual.  The resulting coordinate
Jacobian at the cusp has positive diagonal `(2, 96, 4 * pi)`.

This is a local coordinate construction only; it does not assert existence of a
positive-parameter solution branch.
-/

namespace NearOneRegularizedThirdRow
open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real
open Filter Asymptotics
set_option maxRecDepth 10000

noncomputable section

/-- The unit lower-triangular domain shear which removes the strict
lower-triangular part of the exact cusp Jacobian. -/
def exactCuspShear : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
    5 / 12, 1, 0;
    (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi),
      (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi), 1]

/-- Physical `(z,a,b)` point represented by parameter `s` and the
tangent-centered shear displacement `u`. -/
def tangentCenteredPoint (s : ℝ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => exactCuspPoint i + s * exactCuspTangent i +
    exactCuspShear.mulVec u i

/-- Reverse only the third residual, preserving the root set while making all
three diagonalized cusp directions positive. -/
def orientNearOneRows (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![y 0, y 1, -y 2]

/-- Complete near-one root map in tangent-centered, sheared, oriented
coordinates. -/
def orientedTangentCenteredRootMap
    (s : ℝ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  orientNearOneRows
    (nearOneRootMap s Real.pi (tangentCenteredPoint s u))

/-- Positive diagonal form of the cusp coordinate Jacobian. -/
def orientedCuspDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 0, 0; 0, 96, 0; 0, 0, 4 * Real.pi]

/-- The domain shear has determinant one, so it is an orientation-preserving
coordinate change. -/
theorem exactCuspShear_det :
    Matrix.det exactCuspShear = 1 := by
  rw [Matrix.det_fin_three]
  simp [exactCuspShear]

/-- Reorienting the residual vector preserves exactly its zero set. -/
theorem orientNearOneRows_eq_zero_iff (y : Fin 3 → ℝ) :
    orientNearOneRows y = 0 ↔ y = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [orientNearOneRows] using congrFun h (0 : Fin 3)
    · simpa [orientNearOneRows] using congrFun h (1 : Fin 3)
    · simpa [orientNearOneRows] using congrFun h (2 : Fin 3)
  · rintro rfl
    ext i
    fin_cases i <;> simp [orientNearOneRows]

/-- The oriented tangent-centered map has the same roots as the original map
evaluated in the tangent-centered chart. -/
theorem orientedTangentCenteredRootMap_eq_zero_iff
    (s : ℝ) (u : Fin 3 → ℝ) :
    orientedTangentCenteredRootMap s u = 0 ↔
      nearOneRootMap s Real.pi (tangentCenteredPoint s u) = 0 :=
  orientNearOneRows_eq_zero_iff _

/-- At `s = 0`, the tangent-centered chart has the explicit affine shear
coordinates used by interval cells. -/
theorem tangentCenteredPoint_zero (u : Fin 3 → ℝ) :
    tangentCenteredPoint 0 u =
      ![Real.pi + u 0,
        5 * Real.pi / 12 + 5 * u 0 / 12 + u 1,
        -44 + 19 * Real.pi ^ 2 / 24 +
          (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * u 0 +
          (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * u 1 + u 2] := by
  ext i
  fin_cases i <;>
    simp [tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
      exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The centered chart sends its origin at `s = 0` to the exact cusp. -/
theorem tangentCenteredPoint_zero_zero :
    tangentCenteredPoint 0 0 = exactCuspPoint := by
  ext i
  fin_cases i <;>
    simp [tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
      exactCuspShear, Matrix.mulVec, dotProduct]

/-- The oriented, centered root map still vanishes at the cusp. -/
theorem orientedTangentCenteredRootMap_cusp :
    orientedTangentCenteredRootMap 0 0 = 0 := by
  rw [orientedTangentCenteredRootMap, tangentCenteredPoint_zero_zero,
    nearOneRootMap_exactCusp]
  ext i
  fin_cases i <;> simp [orientNearOneRows]

/-- The unit lower-triangular shear diagonalizes the exact cusp Jacobian before
row orientation. -/
theorem exactCuspJacobian_mul_exactCuspShear :
    exactCuspJacobian * exactCuspShear =
      !![2, 0, 0; 0, 96, 0; 0, 0, -4 * Real.pi] := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exactCuspJacobian, exactCuspShear, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp [hpi] <;>
    ring

/-- Negating the third row of the sheared exact Jacobian gives the requested
positive diagonal form. -/
theorem orient_exactCuspJacobian_mul_exactCuspShear :
    (fun i j => if i = (2 : Fin 3) then
      -(exactCuspJacobian * exactCuspShear) i j
    else (exactCuspJacobian * exactCuspShear) i j) =
      orientedCuspDiagonal := by
  rw [exactCuspJacobian_mul_exactCuspShear]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientedCuspDiagonal]

private theorem thirdRowEndpointPolynomial_affine_deriv
    (z a b pi dz da db : ℝ) :
    deriv (fun t => thirdRowEndpointPolynomial
      (z + dz * t) (a + da * t) (b + db * t) pi) 0 =
      deriv (fun z' => thirdRowEndpointPolynomial z' a b pi) z * dz +
      deriv (fun a' => thirdRowEndpointPolynomial z a' b pi) a * da +
      deriv (fun b' => thirdRowEndpointPolynomial z a b' pi) b * db := by
  let Z : ℝ[X] := C z + C dz * X
  let A : ℝ[X] := C a + C da * X
  let B : ℝ[X] := C b + C db * X
  let q : ℝ[X] := C (-(4 / 3 : ℝ)) *
    (-576 * A ^ 3 + 42 * A ^ 2 * C pi + 432 * A ^ 2 * Z +
      36 * A * B - 28 * A * C pi * Z - 92 * A * Z ^ 2 + 144 * A +
      4 * B * C pi - 16 * B * Z + C pi * Z ^ 2 - 48 * C pi +
      6 * Z ^ 3 + 120 * Z)
  rw [show (fun t => thirdRowEndpointPolynomial
      (z + dz * t) (a + da * t) (b + db * t) pi) =
      fun t => q.eval t by
    funext t
    simp [q, Z, A, B, thirdRowEndpointPolynomial]]
  rw [q.deriv]
  simp [q, Z, A, B, derivative_pow,
    thirdRowEndpointPolynomial_deriv_z,
    thirdRowEndpointPolynomial_deriv_a,
    thirdRowEndpointPolynomial_deriv_b]
  ring

/-- The actual coordinate Jacobian of the oriented tangent-centered root map at
the cusp is its positive diagonal form. -/
theorem orientedTangentCenteredRootMap_coordinateJacobian_cusp :
    coordinateJacobian (orientedTangentCenteredRootMap 0) (0 : Fin 3 → ℝ) =
      orientedCuspDiagonal := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hthird0 : deriv (fun t => thirdRowEndpointPolynomial
      (Real.pi + t)
      (5 * Real.pi / 12 + 5 * t / 12)
      (-44 + 19 * Real.pi ^ 2 / 24 +
        (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * t)
      Real.pi) 0 = 0 := by
    rw [show (fun t => thirdRowEndpointPolynomial
        (Real.pi + t)
        (5 * Real.pi / 12 + 5 * t / 12)
        (-44 + 19 * Real.pi ^ 2 / 24 +
          (109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * t)
        Real.pi) =
        fun t => thirdRowEndpointPolynomial
          (Real.pi + 1 * t)
          (5 * Real.pi / 12 + (5 / 12) * t)
          (-44 + 19 * Real.pi ^ 2 / 24 +
            ((109 * Real.pi ^ 2 - 5376) / (72 * Real.pi)) * t)
          Real.pi by
      funext t
      congr 1 <;> ring]
    rw [thirdRowEndpointPolynomial_affine_deriv]
    simp [thirdRowEndpointPolynomial_deriv_z,
      thirdRowEndpointPolynomial_deriv_a,
      thirdRowEndpointPolynomial_deriv_b]
    field_simp [hpi]
    ring
  have hthird1 : deriv (fun t => thirdRowEndpointPolynomial
      Real.pi
      (5 * Real.pi / 12 + t)
      (-44 + 19 * Real.pi ^ 2 / 24 +
        (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * t)
      Real.pi) 0 = 0 := by
    rw [show (fun t => thirdRowEndpointPolynomial
        Real.pi
        (5 * Real.pi / 12 + t)
        (-44 + 19 * Real.pi ^ 2 / 24 +
          (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * t)
        Real.pi) =
        fun t => thirdRowEndpointPolynomial
          (Real.pi + 0 * t)
          (5 * Real.pi / 12 + 1 * t)
          (-44 + 19 * Real.pi ^ 2 / 24 +
            ((2880 - 7 * Real.pi ^ 2) / (6 * Real.pi)) * t)
          Real.pi by
      funext t
      congr 1 <;> ring]
    rw [thirdRowEndpointPolynomial_affine_deriv]
    simp [thirdRowEndpointPolynomial_deriv_z,
      thirdRowEndpointPolynomial_deriv_a,
      thirdRowEndpointPolynomial_deriv_b]
    field_simp [hpi]
    ring
  have hthird2 : deriv (fun t => thirdRowEndpointPolynomial
      Real.pi (5 * Real.pi / 12)
      (-44 + 19 * Real.pi ^ 2 / 24 + t) Real.pi) 0 =
      -4 * Real.pi := by
    rw [show (fun t => thirdRowEndpointPolynomial
        Real.pi (5 * Real.pi / 12)
        (-44 + 19 * Real.pi ^ 2 / 24 + t) Real.pi) =
        fun t => thirdRowEndpointPolynomial
          (Real.pi + 0 * t) (5 * Real.pi / 12 + 0 * t)
          (-44 + 19 * Real.pi ^ 2 / 24 + 1 * t) Real.pi by
      funext t
      congr 1 <;> ring]
    rw [thirdRowEndpointPolynomial_affine_deriv]
    simp [thirdRowEndpointPolynomial_deriv_z,
      thirdRowEndpointPolynomial_deriv_a,
      thirdRowEndpointPolynomial_deriv_b]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateJacobian, orientedTangentCenteredRootMap,
      tangentCenteredPoint_zero, orientNearOneRows, nearOneRootMap_zero,
      orientedCuspDiagonal, hthird0, hthird1, hthird2]
  all_goals ring_nf
  exact deriv_const 0 0

end

end NearOneRegularizedThirdRow
