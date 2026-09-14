import CMVOrientedLoopEndpointOrientation

open Set
open scoped Topology

theorem strictMono_of_continuous_injective_Icc_start_eq_zero
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hstart : f ⟨a, ⟨le_rfl, hab.le⟩⟩ = 0) :
    StrictMono f := by
  letI : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exact hmono
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} := ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} := ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hyx : f y < f x := hanti hxy
    rw [show x = ⟨a, ⟨le_rfl, hab.le⟩⟩ by rfl, hstart] at hyx
    exact (not_lt_of_ge (f y).2.1) hyx

theorem strictAnti_of_continuous_injective_Icc_start_eq_one
    {a b : ℝ} (hab : a < b)
    (f : {x : ℝ // x ∈ Icc a b} → unitInterval)
    (hf : Continuous f) (hinj : Function.Injective f)
    (hstart : f ⟨a, ⟨le_rfl, hab.le⟩⟩ = 1) :
    StrictAnti f := by
  letI : Fact (a ≤ b) := ⟨hab.le⟩
  rcases hf.strictMono_of_inj_boundedOrder' hinj with hmono | hanti
  · exfalso
    let x : {x : ℝ // x ∈ Icc a b} := ⟨a, ⟨le_rfl, hab.le⟩⟩
    let y : {x : ℝ // x ∈ Icc a b} := ⟨b, ⟨hab.le, le_rfl⟩⟩
    have hxy : x < y := hab
    have hxy' : f x < f y := hmono hxy
    rw [show x = ⟨a, ⟨le_rfl, hab.le⟩⟩ by rfl, hstart] at hxy'
    exact (not_lt_of_ge (f y).2.2) hxy'
  · exact hanti
