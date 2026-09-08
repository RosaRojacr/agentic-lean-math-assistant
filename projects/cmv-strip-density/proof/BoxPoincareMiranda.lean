/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Gametheory.Brouwer_product
import Mathlib.Topology.Order.ProjIcc

/-!
# Poincare--Miranda on a finite-dimensional box

This module derives the opposite-face zero theorem for finite-dimensional real
coordinate boxes from the kernel-checked Brouwer fixed-point theorem for
products of simplices.  The intermediate fixed-point theorem is stated for
continuous self-maps of a closed coordinate box.
-/

open Function Set

noncomputable section

namespace BoxPoincareMiranda

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Inhabited ι] [LinearOrder ι]

private abbrev cubeCard (_ : ι) : ℕ+ := 2

private abbrev Cube (ι : Type*) := ProductSimplices (fun _ : ι => (2 : ℕ+))

private def decode (a b : ι → ℝ) (y : Cube ι) : ι → ℝ :=
  fun i => a i + (y i).1 1 * (b i - a i)

private theorem decode_mem {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (y : Cube ι) : decode a b y ∈ Icc a b := by
  constructor
  · intro i
    have ht : (y i).1 1 ∈ Icc (0 : ℝ) 1 :=
      mem_Icc_of_mem_stdSimplex (y i).2 1
    have hdelta : 0 ≤ b i - a i := sub_nonneg.mpr (hab i).le
    have hmul : 0 ≤ (y i).1 1 * (b i - a i) := mul_nonneg ht.1 hdelta
    simp only [decode]
    linarith
  · intro i
    have ht : (y i).1 1 ∈ Icc (0 : ℝ) 1 :=
      mem_Icc_of_mem_stdSimplex (y i).2 1
    have hdelta : 0 ≤ b i - a i := sub_nonneg.mpr (hab i).le
    have hmul : (y i).1 1 * (b i - a i) ≤ 1 * (b i - a i) :=
      mul_le_mul_of_nonneg_right ht.2 hdelta
    simp only [decode]
    linarith

private def decodeToBox {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    (y : Cube ι) : Icc a b :=
  ⟨decode a b y, decode_mem hab y⟩

private theorem continuous_decodeToBox {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) : Continuous (decodeToBox hab) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun y : Cube ι => a i + (y i).1 1 * (b i - a i))
  have hyi : Continuous (fun y : Cube ι => (y i).1 1) :=
    (continuous_apply 1).comp
      (continuous_subtype_val.comp (continuous_apply i))
  exact continuous_const.add (hyi.mul_const (b i - a i))

private def encode {a b : ι → ℝ} (hab : ∀ i, a i < b i)
    (x : Icc a b) : Cube ι :=
  fun i =>
    ⟨![(b i - x.1 i) / (b i - a i),
        (x.1 i - a i) / (b i - a i)], by
      change (∀ j : Fin 2,
          0 ≤ ![(b i - x.1 i) / (b i - a i),
            (x.1 i - a i) / (b i - a i)] j) ∧
        ∑ j : Fin 2, ![(b i - x.1 i) / (b i - a i),
          (x.1 i - a i) / (b i - a i)] j = 1
      constructor
      · intro j
        fin_cases j
        · exact div_nonneg (sub_nonneg.mpr (x.2.2 i))
            (sub_nonneg.mpr (hab i).le)
        · exact div_nonneg (sub_nonneg.mpr (x.2.1 i))
            (sub_nonneg.mpr (hab i).le)
      · rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp [ne_of_gt (sub_pos.mpr (hab i))]
        ring⟩

private theorem continuous_encode {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) : Continuous (encode hab) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Icc a b =>
    (encode hab x i : stdSimplex ℝ (Fin 2)))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun x : Icc a b =>
      (b i - x.1 i) / (b i - a i))
    have hxi : Continuous (fun x : Icc a b => x.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (continuous_const.sub hxi).div_const (b i - a i)
  · change Continuous (fun x : Icc a b =>
      (x.1 i - a i) / (b i - a i))
    have hxi : Continuous (fun x : Icc a b => x.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (hxi.sub continuous_const).div_const (b i - a i)

private theorem decode_encode {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (x : Icc a b) :
    decodeToBox hab (encode hab x) = x := by
  apply Subtype.ext
  funext i
  change a i + (x.1 i - a i) / (b i - a i) * (b i - a i) = x.1 i
  field_simp [ne_of_gt (sub_pos.mpr (hab i))]
  ring

/-- Every continuous self-map of a nondegenerate finite-dimensional closed
coordinate box has a fixed point. -/
theorem box_fixedPoint {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (f : Icc a b → Icc a b)
    (hf : Continuous f) : ∃ x : Icc a b, f x = x := by
  let g : Cube ι → Cube ι := encode hab ∘ f ∘ decodeToBox hab
  have hg : Continuous g :=
    (continuous_encode hab).comp (hf.comp (continuous_decodeToBox hab))
  obtain ⟨y, hy⟩ := Brouwer_Product cubeCard g hg
  refine ⟨decodeToBox hab y, ?_⟩
  have hdecode := congrArg (decodeToBox hab) hy
  change decodeToBox hab (encode hab (f (decodeToBox hab y))) =
    decodeToBox hab y at hdecode
  simpa only [decode_encode] using hdecode

private theorem projIcc_sub_fixed_imp_zero {a b x y : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b)
    (hlo : x = a → y ≤ 0) (hhi : x = b → 0 ≤ y)
    (hfix : ((projIcc a b hab.le (x - y) : Icc a b) : ℝ) = x) :
    y = 0 := by
  by_contra hy
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have hxy : x < x - y := by linarith
    by_cases hb : b ≤ x - y
    · have hproj := congrArg Subtype.val
        (projIcc_of_right_le hab.le hb)
      have hxb : x = b := by
        change ((projIcc a b hab.le (x - y) : Icc a b) : ℝ) = b at hproj
        linarith
      linarith [hhi hxb]
    · have hmem : x - y ∈ Icc a b :=
        ⟨hx.1.trans hxy.le, le_of_not_ge hb⟩
      have hproj := congrArg Subtype.val (projIcc_of_mem hab.le hmem)
      change ((projIcc a b hab.le (x - y) : Icc a b) : ℝ) = x - y at hproj
      linarith
  · have hxy : x - y < x := by linarith
    by_cases ha : x - y ≤ a
    · have hproj := congrArg Subtype.val
        (projIcc_of_le_left hab.le ha)
      have hxa : x = a := by
        change ((projIcc a b hab.le (x - y) : Icc a b) : ℝ) = a at hproj
        linarith
      linarith [hlo hxa]
    · have hmem : x - y ∈ Icc a b :=
        ⟨le_of_not_ge ha, hxy.le.trans hx.2⟩
      have hproj := congrArg Subtype.val (projIcc_of_mem hab.le hmem)
      change ((projIcc a b hab.le (x - y) : Icc a b) : ℝ) = x - y at hproj
      linarith

/-- Poincare--Miranda for a map on a finite-dimensional real coordinate box.
A nonpositive corresponding component on each lower face and a nonnegative one
on each upper face force a simultaneous zero. -/
theorem poincareMiranda {a b : ι → ℝ}
    (hab : ∀ i, a i < b i) (f : (ι → ℝ) → (ι → ℝ))
    (hf : ContinuousOn f (Icc a b))
    (hlo : ∀ x ∈ Icc a b, ∀ i, x i = a i → f x i ≤ 0)
    (hhi : ∀ x ∈ Icc a b, ∀ i, x i = b i → 0 ≤ f x i) :
    ∃ x ∈ Icc a b, f x = 0 := by
  let fr : Icc a b → (ι → ℝ) := fun x => f x.1
  have hfr : Continuous fr := hf.domRestrict
  let T : Icc a b → Icc a b := fun x =>
    ⟨fun i => ((projIcc (a i) (b i) (hab i).le
        (x.1 i - fr x i) : Icc (a i) (b i)) : ℝ), by
      constructor
      · intro i
        exact (projIcc (a i) (b i) (hab i).le (x.1 i - fr x i)).2.1
      · intro i
        exact (projIcc (a i) (b i) (hab i).le (x.1 i - fr x i)).2.2⟩
  have hT : Continuous T := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_subtype_val.comp
    apply continuous_projIcc.comp
    exact ((continuous_apply i).comp continuous_subtype_val).sub
      ((continuous_apply i).comp hfr)
  obtain ⟨x, hx⟩ := box_fixedPoint hab T hT
  refine ⟨x.1, x.2, ?_⟩
  funext i
  apply projIcc_sub_fixed_imp_zero (hab i) ⟨x.2.1 i, x.2.2 i⟩
  · intro hxi
    exact hlo x.1 x.2 i hxi
  · intro hxi
    exact hhi x.1 x.2 i hxi
  · have hxi := congrArg (fun z : Icc a b => z.1 i) hx
    simpa only [T, fr] using hxi

end BoxPoincareMiranda
