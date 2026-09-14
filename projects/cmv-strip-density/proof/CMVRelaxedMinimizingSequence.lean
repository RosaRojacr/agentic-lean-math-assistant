/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVLocalGraphSurgery

/-!
# Exact minimizing sequences for the CMV relaxation

A finite relaxed perimeter admits one actual smooth recovery sequence whose
termwise complete-frontier costs are finite and converge to the relaxed value.
This diagonal selector distinguishes minimizing recovery from arbitrary global
`L¹` recovery, which may carry persistent hidden frontier.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal MeasureTheory Topology NNReal symmDiff

noncomputable section

namespace CMVRelaxation

/-- A finite relaxed perimeter is realized by a smooth recovery sequence in the
only sense needed by the relaxation: the termwise costs converge to the exact
infimum.  In particular, its liminf cost equals that infimum and every selected
term has finite cost. -/
theorem exists_exactMinimizing_smoothSequence
    {lam : ℝ} {E : Set PlanePoint}
    (hrelTop : relaxedPerimeter lam E < ⊤) :
    ∃ A : SmoothSequence,
      NullMeasurableSet E volume ∧
      A.ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (A.carrier n))
        atTop (𝓝 (relaxedPerimeter lam E)) ∧
      A.cost lam = relaxedPerimeter lam E ∧
      ∀ n, smoothCost lam (A.carrier n) < ⊤ := by
  obtain ⟨_, hE, _, _, _, _⟩ :=
    exists_nearMinimizing_finiteCost_smoothSequence
      (E := E) hrelTop (δ := 1) one_ne_zero (by simp)
  let delta : ℕ → ENNReal := fun n => ((n + 1 : ℕ) : ENNReal)⁻¹
  have hdelta_ne : ∀ n, delta n ≠ 0 := by
    intro n
    simp [delta]
  have hdelta_top : ∀ n, delta n < ⊤ := by
    intro n
    simp [delta]
  have hdelta_tendsto : Tendsto delta atTop (𝓝 0) := by
    have h :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp [delta]
  have hdomain : ∀ n, ∃ U : Set PlanePoint,
      IsSmoothDomain U ∧
      characteristicDistance U E < delta n ∧
      smoothCost lam U <
        (relaxedPerimeter lam E + delta n) + delta n ∧
      smoothCost lam U < ⊤ := by
    intro n
    obtain ⟨B, _hE, hBconv, hBnear, hBtend, hBfinite⟩ :=
      exists_nearMinimizing_finiteCost_smoothSequence
        (E := E) hrelTop (hdelta_ne n) (hdelta_top n)
    have hBTop : B.cost lam < ⊤ :=
      hBnear.trans ((ENNReal.add_lt_top).2 ⟨hrelTop, hdelta_top n⟩)
    have hdist : ∀ᶠ k in atTop,
        characteristicDistance (B.carrier k) E < delta n :=
      hBconv.eventually
        (Iio_mem_nhds (bot_lt_iff_ne_bot.2 (hdelta_ne n)))
    have hcost : ∀ᶠ k in atTop,
        smoothCost lam (B.carrier k) < B.cost lam + delta n :=
      hBtend.eventually
        (Iio_mem_nhds (ENNReal.lt_add_right hBTop.ne (hdelta_ne n)))
    obtain ⟨k, hkdist, hkcost⟩ := (hdist.and hcost).exists
    refine ⟨B.carrier k, B.smooth k, hkdist, ?_, hBfinite k⟩
    exact hkcost.trans
      (ENNReal.add_lt_add_right (hdelta_top n).ne hBnear)
  let U : ℕ → Set PlanePoint := fun n => (hdomain n).choose
  have hUsmooth : ∀ n, IsSmoothDomain (U n) :=
    fun n => (hdomain n).choose_spec.1
  let A : SmoothSequence :=
    { carrier := U
      smooth := hUsmooth }
  have hAdist : ∀ n, characteristicDistance (A.carrier n) E ≤ delta n :=
    fun n => (hdomain n).choose_spec.2.1.le
  have hAconv : A.ConvergesTo E := by
    unfold SmoothSequence.ConvergesTo
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hdelta_tendsto (fun _ => bot_le) hAdist
  let q : ℕ → ENNReal :=
    fun n => (relaxedPerimeter lam E + delta n) + delta n
  have hq_tendsto : Tendsto q atTop (𝓝 (relaxedPerimeter lam E)) := by
    have hconst : Tendsto (fun _ : ℕ => relaxedPerimeter lam E)
        atTop (𝓝 (relaxedPerimeter lam E)) :=
      tendsto_const_nhds
    have hraw := (hconst.add hdelta_tendsto).add hdelta_tendsto
    simpa only [q, add_zero] using hraw
  have hupper : ∀ n, smoothCost lam (A.carrier n) ≤ q n :=
    fun n => (hdomain n).choose_spec.2.2.1.le
  have hrelLeCost : relaxedPerimeter lam E ≤ A.cost lam := by
    unfold relaxedPerimeter
    apply sInf_le
    exact ⟨A, hE, hAconv, rfl⟩
  have hliminf :
      relaxedPerimeter lam E ≤
        liminf (fun n => smoothCost lam (A.carrier n)) atTop := by
    simpa only [SmoothSequence.cost] using hrelLeCost
  have hlimsup :
      limsup (fun n => smoothCost lam (A.carrier n)) atTop ≤
        relaxedPerimeter lam E := by
    calc
      limsup (fun n => smoothCost lam (A.carrier n)) atTop ≤
          limsup q atTop :=
        limsup_le_limsup (Eventually.of_forall hupper)
      _ = relaxedPerimeter lam E := hq_tendsto.limsup_eq
  have hAtendsto :
      Tendsto (fun n => smoothCost lam (A.carrier n))
        atTop (𝓝 (relaxedPerimeter lam E)) :=
    tendsto_of_le_liminf_of_limsup_le hliminf hlimsup
  refine ⟨A, hE, hAconv, hAtendsto, ?_, ?_⟩
  · unfold SmoothSequence.cost
    exact hAtendsto.liminf_eq
  · intro n
    exact (hdomain n).choose_spec.2.2.2

end CMVRelaxation
