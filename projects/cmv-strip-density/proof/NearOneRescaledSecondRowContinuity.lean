/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRescaledOrientedMap

/-!
# Joint continuity of the rescaled second row

The second rescaled row is evaluation of a polynomial whose coefficients depend
continuously on all three rescaled coordinates.  Because `Polynomial` carries no
topology, this module proves coefficientwise continuity and a uniform degree
bound before reducing evaluation to a fixed finite sum.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter

noncomputable section

private def CC {α : Type*} [TopologicalSpace α] (P : α → ℝ[X]) : Prop :=
  ∀ n, Continuous (fun x => (P x).coeff n)

private lemma cc_const {α : Type*} [TopologicalSpace α] (p : ℝ[X]) :
    CC (fun _ : α => p) := fun _ => continuous_const

private lemma cc_C {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : CC (fun x => C (f x)) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hf
  · simp only [coeff_C, if_neg hn]
    exact continuous_const

private lemma cc_add {α : Type*} [TopologicalSpace α] {P Q : α → ℝ[X]}
    (hP : CC P) (hQ : CC Q) : CC (fun x => P x + Q x) := by
  intro n
  change Continuous (fun x => (P x).coeff n + (Q x).coeff n)
  exact (hP n).add (hQ n)

private lemma cc_neg {α : Type*} [TopologicalSpace α] {P : α → ℝ[X]}
    (hP : CC P) : CC (fun x => - P x) := by
  intro n
  change Continuous (fun x => - (P x).coeff n)
  exact (hP n).neg

private lemma cc_sub {α : Type*} [TopologicalSpace α] {P Q : α → ℝ[X]}
    (hP : CC P) (hQ : CC Q) : CC (fun x => P x - Q x) := by
  simpa only [sub_eq_add_neg] using cc_add hP (cc_neg hQ)

private lemma cc_mul {α : Type*} [TopologicalSpace α] {P Q : α → ℝ[X]}
    (hP : CC P) (hQ : CC Q) : CC (fun x => P x * Q x) := by
  intro n
  simp_rw [coeff_mul]
  exact continuous_finsetSum _ fun k _ => (hP k.1).mul (hQ k.2)

private lemma cc_pow {α : Type*} [TopologicalSpace α] {P : α → ℝ[X]}
    (hP : CC P) (n : ℕ) : CC (fun x => P x ^ n) := by
  induction n with
  | zero => simpa using (cc_const (1 : ℝ[X]) : CC (fun _ : α => (1 : ℝ[X])))
  | succ n ih => simpa [pow_succ] using cc_mul ih hP

private lemma cc_divX {α : Type*} [TopologicalSpace α] {P : α → ℝ[X]}
    (hP : CC P) : CC (fun x => (P x).divX) := by
  intro n
  simpa only [coeff_divX] using hP (n + 1)

private lemma zcc : CC rescaledZPathPolynomial := by
  exact cc_add
    (cc_add (cc_const _) (cc_mul (cc_const _) (cc_const _)))
    (cc_mul (cc_C (continuous_apply 0)) (cc_const _))

private lemma acc : CC rescaledAPathPolynomial := by
  exact cc_add
    (cc_add (cc_const _) (cc_mul (cc_const _) (cc_const _)))
    (cc_mul (cc_C (by fun_prop)) (cc_const _))

private lemma bcc : CC rescaledBPathPolynomial := by
  exact cc_add
    (cc_add (cc_const _) (cc_mul (cc_const _) (cc_const _)))
    (cc_mul (cc_C (by fun_prop)) (cc_const _))

private lemma h2cc : CC rescaledH2PathPolynomial := by
  let Z := rescaledZPathPolynomial
  let A := rescaledAPathPolynomial
  let B := rescaledBPathPolynomial
  let R := fun q => 2 + X * A q
  let E := fun q => 12 * A q - 4 * Z q + 2 * X * B q
  have hZ : CC Z := zcc
  have hA : CC A := acc
  have hB : CC B := bcc
  have hR : CC R :=
    cc_add (cc_const _) (cc_mul (cc_const _) hA)
  have hE : CC E :=
    cc_add
      (cc_sub (cc_mul (cc_const _) hA) (cc_mul (cc_const _) hZ))
      (cc_mul (cc_mul (cc_const _) (cc_const _)) hB)
  have ht0 : CC (fun q => 4 * E q * R q - 8 * Z q) :=
    cc_sub
      (cc_mul (cc_mul (cc_const _) hE) hR)
      (cc_mul (cc_const _) hZ)
  have ht1 : CC (fun q => X * (E q ^ 2 - 4 * Z q ^ 2)) :=
    cc_mul (cc_const _)
      (cc_sub (cc_pow hE 2) (cc_mul (cc_const _) (cc_pow hZ 2)))
  have ht4 : CC (fun q =>
      X ^ 4 * (-4 * E q * R q + 8 * R q ^ 4 * Z q)) :=
    cc_mul (cc_const _)
      (cc_add
        (cc_mul (cc_mul (cc_const _) hE) hR)
        (cc_mul (cc_mul (cc_const _) (cc_pow hR 4)) hZ))
  have ht5 : CC (fun q =>
      X ^ 5 * (-E q ^ 2 + 8 * E q * R q ^ 3 * Z q -
        8 * E q * R q * Z q + 4 * R q ^ 4 * Z q ^ 2)) :=
    cc_mul (cc_const _)
      (cc_add
        (cc_sub
          (cc_add
            (cc_neg (cc_pow hE 2))
            (cc_mul
              (cc_mul (cc_mul (cc_const _) hE) (cc_pow hR 3)) hZ))
          (cc_mul (cc_mul (cc_mul (cc_const _) hE) hR) hZ))
        (cc_mul (cc_mul (cc_const _) (cc_pow hR 4)) (cc_pow hZ 2)))
  have ht6 : CC (fun q =>
      X ^ 6 * (2 * E q ^ 2 * R q ^ 2 * Z q -
        2 * E q ^ 2 * Z q + 4 * E q * R q ^ 3 * Z q ^ 2 -
        4 * E q * R q * Z q ^ 2)) :=
    cc_mul (cc_const _)
      (cc_sub
        (cc_add
          (cc_sub
            (cc_mul
              (cc_mul (cc_mul (cc_const _) (cc_pow hE 2)) (cc_pow hR 2)) hZ)
            (cc_mul (cc_mul (cc_const _) (cc_pow hE 2)) hZ))
          (cc_mul
            (cc_mul (cc_mul (cc_const _) hE) (cc_pow hR 3)) (cc_pow hZ 2)))
        (cc_mul
          (cc_mul (cc_mul (cc_const _) hE) hR) (cc_pow hZ 2)))
  have ht7 : CC (fun q =>
      X ^ 7 * (E q ^ 2 * R q ^ 2 * Z q ^ 2 - E q ^ 2 * Z q ^ 2)) :=
    cc_mul (cc_const _)
      (cc_sub
        (cc_mul (cc_mul (cc_pow hE 2) (cc_pow hR 2)) (cc_pow hZ 2))
        (cc_mul (cc_pow hE 2) (cc_pow hZ 2)))
  have hAll :=
    cc_add (cc_add (cc_add (cc_add (cc_add ht0 ht1) ht4) ht5) ht6) ht7
  unfold CC at hAll ⊢
  intro n
  simpa only [rescaledH2PathPolynomial, Z, A, B, R, E] using hAll n

private def DB (p : ℝ[X]) (n : ℕ) : Prop := p.natDegree ≤ n

private lemma db_nat (n : ℕ) : DB (n : ℝ[X]) 0 := by
  simp [DB]

private lemma db_X : DB (X : ℝ[X]) 1 := by
  simp [DB]

private lemma db_add {p q : ℝ[X]} {m n : ℕ}
    (hp : DB p m) (hq : DB q n) : DB (p + q) (max m n) :=
  natDegree_add_le p q |>.trans <| max_le_max hp hq

private lemma db_sub {p q : ℝ[X]} {m n : ℕ}
    (hp : DB p m) (hq : DB q n) : DB (p - q) (max m n) :=
  natDegree_sub_le p q |>.trans <| max_le_max hp hq

private lemma db_neg {p : ℝ[X]} {n : ℕ} (hp : DB p n) : DB (-p) n := by
  simpa only [DB, natDegree_neg] using hp

private lemma db_mul {p q : ℝ[X]} {m n : ℕ}
    (hp : DB p m) (hq : DB q n) : DB (p * q) (m + n) :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

private lemma db_pow {p : ℝ[X]} {m : ℕ} (hp : DB p m) (n : ℕ) :
    DB (p ^ n) (n * m) :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left n hp)

private lemma h2_degree (q : Fin 3 → ℝ) :
    (rescaledH2PathPolynomial q).natDegree < 24 := by
  let Z := rescaledZPathPolynomial q
  let A := rescaledAPathPolynomial q
  let B := rescaledBPathPolynomial q
  let R := 2 + X * A
  let E := 12 * A - 4 * Z + 2 * X * B
  have hZ : DB Z 2 := by
    dsimp only [Z]
    unfold rescaledZPathPolynomial
    unfold DB
    compute_degree
  have hA : DB A 2 := by
    dsimp only [A]
    unfold rescaledAPathPolynomial
    unfold DB
    compute_degree
  have hB : DB B 2 := by
    dsimp only [B]
    unfold rescaledBPathPolynomial
    unfold DB
    compute_degree
  have hR : DB R 3 := by
    have := db_add (db_nat 2) (db_mul db_X hA)
    norm_num at this ⊢
    exact this
  have hE : DB E 3 := by
    have := db_add
      (db_sub (db_mul (db_nat 12) hA) (db_mul (db_nat 4) hZ))
      (db_mul (db_mul (db_nat 2) db_X) hB)
    norm_num at this ⊢
    exact this
  have ht0 : DB (4 * E * R - 8 * Z) 6 := by
    have := db_sub
      (db_mul (db_mul (db_nat 4) hE) hR)
      (db_mul (db_nat 8) hZ)
    norm_num at this ⊢
    exact this
  have ht1 : DB (X * (E ^ 2 - 4 * Z ^ 2)) 7 := by
    have := db_mul db_X
      (db_sub (db_pow hE 2) (db_mul (db_nat 4) (db_pow hZ 2)))
    norm_num at this ⊢
    exact this
  have ht4 : DB (X ^ 4 * (-4 * E * R + 8 * R ^ 4 * Z)) 18 := by
    have := db_mul (db_pow db_X 4)
      (db_add
        (db_mul (db_mul (db_neg (db_nat 4)) hE) hR)
        (db_mul (db_mul (db_nat 8) (db_pow hR 4)) hZ))
    norm_num at this ⊢
    exact this
  have ht5 : DB (X ^ 5 * (-E ^ 2 + 8 * E * R ^ 3 * Z -
      8 * E * R * Z + 4 * R ^ 4 * Z ^ 2)) 21 := by
    have := db_mul (db_pow db_X 5)
      (db_add
        (db_sub
          (db_add
            (db_neg (db_pow hE 2))
            (db_mul (db_mul (db_mul (db_nat 8) hE) (db_pow hR 3)) hZ))
          (db_mul (db_mul (db_mul (db_nat 8) hE) hR) hZ))
        (db_mul (db_mul (db_nat 4) (db_pow hR 4)) (db_pow hZ 2)))
    norm_num at this ⊢
    exact this
  have ht6 : DB (X ^ 6 * (2 * E ^ 2 * R ^ 2 * Z -
      2 * E ^ 2 * Z + 4 * E * R ^ 3 * Z ^ 2 -
      4 * E * R * Z ^ 2)) 22 := by
    have := db_mul (db_pow db_X 6)
      (db_sub
        (db_add
          (db_sub
            (db_mul (db_mul (db_mul (db_nat 2) (db_pow hE 2))
              (db_pow hR 2)) hZ)
            (db_mul (db_mul (db_nat 2) (db_pow hE 2)) hZ))
          (db_mul (db_mul (db_mul (db_nat 4) hE)
            (db_pow hR 3)) (db_pow hZ 2)))
        (db_mul (db_mul (db_mul (db_nat 4) hE) hR) (db_pow hZ 2)))
    norm_num at this ⊢
    exact this
  have ht7 : DB (X ^ 7 * (E ^ 2 * R ^ 2 * Z ^ 2 -
      E ^ 2 * Z ^ 2)) 23 := by
    have := db_mul (db_pow db_X 7)
      (db_sub
        (db_mul (db_mul (db_pow hE 2) (db_pow hR 2)) (db_pow hZ 2))
        (db_mul (db_pow hE 2) (db_pow hZ 2)))
    norm_num at this ⊢
    exact this
  have hAll :=
    db_add (db_add (db_add (db_add (db_add ht0 ht1) ht4) ht5) ht6) ht7
  dsimp only [DB] at hAll
  change (let Z := rescaledZPathPolynomial q
    let A := rescaledAPathPolynomial q
    let B := rescaledBPathPolynomial q
    let R := 2 + X * A
    let E := 12 * A - 4 * Z + 2 * X * B
    (4 * E * R - 8 * Z +
      X * (E ^ 2 - 4 * Z ^ 2) +
      X ^ 4 * (-4 * E * R + 8 * R ^ 4 * Z) +
      X ^ 5 * (-E ^ 2 + 8 * E * R ^ 3 * Z -
        8 * E * R * Z + 4 * R ^ 4 * Z ^ 2) +
      X ^ 6 * (2 * E ^ 2 * R ^ 2 * Z -
        2 * E ^ 2 * Z + 4 * E * R ^ 3 * Z ^ 2 -
        4 * E * R * Z ^ 2) +
      X ^ 7 * (E ^ 2 * R ^ 2 * Z ^ 2 - E ^ 2 * Z ^ 2)).natDegree < 24)
  dsimp only
  exact hAll.trans_lt (by norm_num)

/-- The pole-free second rescaled row is jointly continuous in `s` and all
three rescaled coordinates. -/
theorem continuous_poleFreeSecondRescaledRow_joint :
    Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
      poleFreeSecondRescaledRow p.1 p.2) := by
  have hcoeff : CC (fun q =>
      (rescaledH2PathPolynomial q).divX.divX) :=
    cc_divX (cc_divX h2cc)
  rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
      poleFreeSecondRescaledRow p.1 p.2) =
      fun p => ∑ n ∈ Finset.range 24,
        ((rescaledH2PathPolynomial p.2).divX.divX).coeff n * p.1 ^ n by
    funext p
    unfold poleFreeSecondRescaledRow
    have hd : (rescaledH2PathPolynomial p.2).divX.divX.natDegree < 24 := calc
      _ ≤ (rescaledH2PathPolynomial p.2).divX.natDegree :=
        natDegree_divX_le
      _ ≤ (rescaledH2PathPolynomial p.2).natDegree :=
        natDegree_divX_le
      _ < 24 := h2_degree p.2
    rw [eval_eq_sum_range' hd]]
  exact continuous_finsetSum _ fun n _ =>
    ((hcoeff n).comp continuous_snd).mul (continuous_fst.pow n)

end

end NearOneRegularizedThirdRow
