import Mathlib
import CMVGeometry

open Set Function Filter Topology
open scoped NNReal

noncomputable section

variable {F : PlanePoint → PlanePoint} {L : ℝ≥0} {t : ℝ}

private lemma scaled_lipschitz (hF : LipschitzWith L F) :
    LipschitzWith (‖t‖₊ * L) (fun p => t • F p) := by
  exact (lipschitzWith_smul t).comp hF

private lemma translate_contraction (hF : LipschitzWith L F)
    (hsmall : ‖t‖₊ * L < 1) (y : PlanePoint) :
    ContractingWith (‖t‖₊ * L) (fun p => y - t • F p) := by
  refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [dist_eq_norm, sub_sub_sub_cancel_left]
  rw [norm_sub_rev]
  simpa only [dist_comm, dist_eq_norm] using
    (scaled_lipschitz (t := t) hF).dist_le_mul q p

private noncomputable def perturbInv (hF : LipschitzWith L F)
    (hsmall : ‖t‖₊ * L < 1) (y : PlanePoint) : PlanePoint :=
  (translate_contraction (t := t) hF hsmall y).fixedPoint
    (fun p => y - t • F p)

private lemma perturbInv_spec (hF : LipschitzWith L F)
    (hsmall : ‖t‖₊ * L < 1) (y : PlanePoint) :
    perturbInv hF hsmall y + t • F (perturbInv hF hsmall y) = y := by
  have hfix := (translate_contraction (t := t) hF hsmall y).fixedPoint_isFixedPt
  change y - t • F (perturbInv hF hsmall y) = perturbInv hF hsmall y at hfix
  calc
    perturbInv hF hsmall y + t • F (perturbInv hF hsmall y) =
        (y - t • F (perturbInv hF hsmall y)) +
          t • F (perturbInv hF hsmall y) := congrArg (fun z => z + t • F (perturbInv hF hsmall y)) hfix.symm
    _ = y := by abel
private lemma perturbInv_apply (hF : LipschitzWith L F)
    (hsmall : ‖t‖₊ * L < 1) (x : PlanePoint) :
    perturbInv hF hsmall (x + t • F x) = x := by
  symm
  apply (translate_contraction (t := t) hF hsmall (x + t • F x)).fixedPoint_unique
  change x + t • F x - t • F x = x
  abel

noncomputable def smallPerturbationHomeomorph (hF : LipschitzWith L F)
    (hsmall : ‖t‖₊ * L < 1) : PlanePoint ≃ₜ PlanePoint where
  toFun p := p + t • F p
  invFun := perturbInv hF hsmall
  left_inv := perturbInv_apply hF hsmall
  right_inv := perturbInv_spec hF hsmall
  continuous_toFun := (LipschitzWith.id.add (scaled_lipschitz (t := t) hF)).continuous
  continuous_invFun := by
    apply ((AntilipschitzWith.id.add_lipschitzWith
      (scaled_lipschitz (t := t) hF) (by simpa using hsmall)).to_rightInverse
        (perturbInv_spec hF hsmall)).continuous
