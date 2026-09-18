/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import MinimumValue

/-!
# A rational certificate for `min g`

`MinimumValue` proved the sharp statement

  `min_{x>0} g x = 3 cos θ*`,     attained at `x* = area θ*`,

where `θ*` is the unique root of `F θ = 3θ - 3 sin θ cos θ - π`. That equality
is exact and is the actual result; this file certifies a numeric bound for it.

Cañete–Miranda–Vittone bound `g` below by `π / 4 = 0.7853981…`, giving the
threshold `lam ≥ 4 / π = 1.2732395…` for excluding four-arc isoperimetric
candidates for the strip density. Their Remark 3.17 asserts this is not optimal
but does not compute the true constant. The baseline certificate here is

  `3 cos 1.3026632 < min g`,

which gives the required exact threshold `lam ≥ 1.2581858`. A separate,
stronger certificate uses `θ* < 1.30266283731`, 20-decimal bounds on `π`, and
exact rational interval doubling to prove the optimized threshold
`lam ≥ 1.2581840884`.

CMV's geometric argument interprets these analytic inequalities as candidate
exclusions, but that geometric bridge is not formalized in this file. The
optimized decimal remains strictly above the documented sharp value
`1.2581840883…`.

## Why no certificate reaches the sharp value

`cos` is strictly decreasing, so every witness `t₀ > θ*` gives a constant
strictly below `3 cos θ*`. The sharp threshold is a supremum over certificates,
attained by none. The bound is stated in exact form `3 * cos 1.3026632 < g x`
rather than as a decimal, avoiding a second layer of rounding.

## Baseline method: three halvings

`F` strictly increasing means one witness `t₀` with `F t₀ > 0` gives
`θ* < t₀`. This needs an upper bound on `sin 2.6053264`, whose argument is far
from `0`. Reflecting gives `y = π - 2.6053264 ∈ (0.5362656, 0.5362666)`, but
`Real.sin_bound` at `y` wastes `y⁵/600 ≈ 7.6 · 10⁻⁵`, since its error term
`y⁵/100` overshoots the true `y⁵/120`.

That waste scales as the fifth power, so each halving gains a factor of `32`.
We halve three times, to `q = y/4`, `r = y/8`, `s = y/16`, and rebuild upward
using only two Mathlib inputs (`Real.sin_bound` and `Real.sin_gt_sub_cube`)
together with the two double-angle identities

  `sin 2u = 2 sin u cos u`,        `cos 2u = 1 - 2 sin²u`.

The second is what makes this cheap: it converts every cosine bound into a
bound on a *sine* at half the argument, where the polynomial estimates are
sharp.

The baseline proof uses six-decimal bounds on `π`; at this depth their
`10⁻⁶` width is the binding error source. Its witness keeps a
`7 · 10⁻⁷` margin against those bounds. The optimized comparison proof below
instead uses Mathlib's 20-decimal bounds and deeper interval doubling.

## History

| method | threshold | gap to sharp |
|---|---|---|
| direct `sin_bound` at `y` | `1.2584157` | `2.3 · 10⁻⁴` |
| one halving | `1.2582032` | `1.9 · 10⁻⁵` |
| two halvings | `1.2581894` | `5.3 · 10⁻⁶` |
| three halvings (this file) | `1.2581857` | `1.7 · 10⁻⁶` |
| d20 `π`, deeper interval doubling | `1.2581840884` | `< 10⁻¹⁰` |
| sharp `1 / (3 cos θ*)` | `1.2581841` | — |

The baseline's next improvement requires sharper `π` bounds, not merely another
halving. The optimized certificate below makes that clean cutover: it uses
`Real.pi_gt_d20` / `Real.pi_lt_d20`, an 11-decimal rational root witness,
and independent exact interval certificates for the reflected sine and witness
cosine.
-/

open Real Set Filter Topology

/-! ## The structural half -/

/-- One rational witness above the root bounds it. -/
lemma θstar_lt_of_F_pos {t : ℝ} (ht : t ∈ Icc 0 π) (h : 0 < F t) : θstar < t := by
  by_contra hcon
  push Not at hcon
  have hs : θstar ∈ Icc 0 π := ⟨le_of_lt θstar_pos, le_of_lt θstar_lt_pi⟩
  rcases eq_or_lt_of_le hcon with heq | hlt
  · rw [heq, θstar_spec] at h
    linarith
  · have := F_strictMonoOn ht hs hlt
    rw [θstar_spec] at this
    linarith

/-- `cos` is strictly decreasing on `[0, π]`, so an upper bound on `θ*` becomes
a lower bound on `k = 3 cos θ*`. -/
lemma three_cos_lt_of_θstar_lt {t : ℝ} (ht : t ≤ π) (h : θstar < t) :
    3 * cos t < 3 * cos θstar := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt θstar_pos) ht h
  linarith

/-! ## `π` to six decimals -/

lemma pi_lb : (3.141592 : ℝ) < π := by
  have := Real.pi_gt_d6
  linarith

lemma pi_ub : π < (3.141593 : ℝ) := by
  have := Real.pi_lt_d6
  linarith

/-! ## The double-angle identity for cosine -/

lemma cos_two_mul_sin_sq (u : ℝ) : cos (2 * u) = 1 - 2 * sin u ^ 2 := by
  rw [cos_two_mul]
  linear_combination (2:ℝ) * sin_sq_add_cos_sq u

/-! ## Level 4: `s = y / 16 ∈ (0.0335166, 0.0335166625)` -/

lemma sin_s_ge : (0.033510324749 : ℝ) ≤ sin ((π - 2.6053264) / 16) := by
  set s : ℝ := (π - 2.6053264) / 16 with hs
  have hlo : (0.0335166 : ℝ) < s := by rw [hs]; linarith [pi_lb]
  have hhi : s < (0.0335166625 : ℝ) := by rw [hs]; linarith [pi_ub]
  have h0 : (0:ℝ) < s := by linarith
  have hc := Real.sin_gt_sub_cube h0
  have h2 : s^2 ≤ (0.0335166625 : ℝ)^2 := by nlinarith
  have h3 : s^3 ≤ (0.0335166625 : ℝ)^3 := by nlinarith
  norm_num at h3
  linarith

lemma sin_s_le : sin ((π - 2.6053264) / 16) ≤ 0.033510387708 := by
  set s : ℝ := (π - 2.6053264) / 16 with hs
  have hlo : (0.0335166 : ℝ) < s := by rw [hs]; linarith [pi_lb]
  have hhi : s < (0.0335166625 : ℝ) := by rw [hs]; linarith [pi_ub]
  have h0 : (0:ℝ) ≤ s := by linarith
  have habs : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_of_nonneg h0] at hb
  rw [abs_le] at hb
  have h2l : (0.0335166 : ℝ)^2 ≤ s^2 := by nlinarith
  have h3l : (0.0335166 : ℝ)^3 ≤ s^3 := by nlinarith
  have h2h : s^2 ≤ (0.0335166625 : ℝ)^2 := by nlinarith
  have h4h : s^4 ≤ (0.0335166625 : ℝ)^4 := by nlinarith
  have h5h : s^5 ≤ (0.0335166625 : ℝ)^5 := by nlinarith
  norm_num at h3l h5h
  linarith [hb.2]

/-! ## Level 3: `r = y / 8 ∈ (0.0670332, 0.067033325)` -/

lemma sin_r_ge : (0.066982997998 : ℝ) ≤ sin ((π - 2.6053264) / 8) := by
  set r : ℝ := (π - 2.6053264) / 8 with hr
  have hlo : (0.0670332 : ℝ) < r := by rw [hr]; linarith [pi_lb]
  have hhi : r < (0.067033325 : ℝ) := by rw [hr]; linarith [pi_ub]
  have h0 : (0:ℝ) < r := by linarith
  have hc := Real.sin_gt_sub_cube h0
  have h2 : r^2 ≤ (0.067033325 : ℝ)^2 := by nlinarith
  have h3 : r^3 ≤ (0.067033325 : ℝ)^3 := by nlinarith
  norm_num at h3
  linarith

lemma sin_r_le : sin ((π - 2.6053264) / 8) ≤ 0.066983136814 := by
  set r : ℝ := (π - 2.6053264) / 8 with hr
  have hlo : (0.0670332 : ℝ) < r := by rw [hr]; linarith [pi_lb]
  have hhi : r < (0.067033325 : ℝ) := by rw [hr]; linarith [pi_ub]
  have h0 : (0:ℝ) ≤ r := by linarith
  have habs : |r| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_of_nonneg h0] at hb
  rw [abs_le] at hb
  have h2l : (0.0670332 : ℝ)^2 ≤ r^2 := by nlinarith
  have h3l : (0.0670332 : ℝ)^3 ≤ r^3 := by nlinarith
  have h2h : r^2 ≤ (0.067033325 : ℝ)^2 := by nlinarith
  have h4h : r^4 ≤ (0.067033325 : ℝ)^4 := by nlinarith
  have h5h : r^5 ≤ (0.067033325 : ℝ)^5 := by nlinarith
  norm_num at h3l h5h
  linarith [hb.2]

lemma cos_r_le : cos ((π - 2.6053264) / 8) ≤ 0.997754116271 := by
  have h := sin_s_ge
  have hd : (π - 2.6053264) / 8 = 2 * ((π - 2.6053264) / 16) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

lemma cos_r_ge : (0.997754107831 : ℝ) ≤ cos ((π - 2.6053264) / 8) := by
  have h := sin_s_le
  have h0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 16) := by linarith [sin_s_ge]
  have hd : (π - 2.6053264) / 8 = 2 * ((π - 2.6053264) / 16) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h, h0]

/-! ## Level 2: `q = y / 4` -/

lemma sin_q_le : sin ((π - 2.6053264) / 4) ≤ 0.133665400954 := by
  have hs := sin_r_le
  have hc := cos_r_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 8) := by linarith [sin_r_ge]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 8) := by linarith [cos_r_ge]
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

lemma sin_q_ge : (0.133665122814 : ℝ) ≤ sin ((π - 2.6053264) / 4) := by
  have hs := sin_r_ge
  have hc := cos_r_ge
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc]

lemma cos_q_le : cos ((π - 2.6053264) / 4) ≤ 0.991026555959 := by
  have h := sin_r_ge
  have hd : (π - 2.6053264) / 4 = 2 * ((π - 2.6053264) / 8) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

/-! ## Level 1: `h = y / 2`, then `sin y` -/

lemma sin_h_le : sin ((π - 2.6053264) / 2) ≤ 0.264931923917 := by
  have hs := sin_q_le
  have hc := cos_q_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 4) := by linarith [sin_q_ge]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 4) := by
    refine le_of_lt (cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [pi_lb, pi_ub]
  have hd : (π - 2.6053264) / 2 = 2 * ((π - 2.6053264) / 4) := by ring
  rw [hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

lemma cos_h_le : cos ((π - 2.6053264) / 2) ≤ 0.964267269887 := by
  have h := sin_q_ge
  have hd : (π - 2.6053264) / 2 = 2 * ((π - 2.6053264) / 4) := by ring
  rw [hd, cos_two_mul_sin_sq]
  nlinarith [h]

lemma sin_witness_lt : sin (2.6053264 : ℝ) < 0.510930366 := by
  have hs := sin_h_le
  have hc := cos_h_le
  have hs0 : (0:ℝ) ≤ sin ((π - 2.6053264) / 2) := by
    refine le_of_lt (sin_pos_of_pos_of_lt_pi ?_ ?_) <;> linarith [pi_lb, pi_ub]
  have hc0 : (0:ℝ) ≤ cos ((π - 2.6053264) / 2) := by
    refine le_of_lt (cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [pi_lb, pi_ub]
  have hrefl : sin (2.6053264 : ℝ) = sin (π - 2.6053264) := (sin_pi_sub _).symm
  have hd : (π - 2.6053264 : ℝ) = 2 * ((π - 2.6053264) / 2) := by ring
  rw [hrefl, hd, sin_two_mul]
  nlinarith [hs, hc, hs0, hc0]

/-- `F 1.3026632 > 0`, hence `θ* < 1.3026632`. Margin `7.0 · 10⁻⁷`. -/
lemma F_at_witness : 0 < F (1.3026632 : ℝ) := by
  have hdouble : (3:ℝ) * (sin 1.3026632 * cos 1.3026632) = 3 / 2 * sin 2.6053264 := by
    have h : (2.6053264 : ℝ) = 2 * 1.3026632 := by norm_num
    rw [h, sin_two_mul]; ring
  rw [F, hdouble]
  linarith [sin_witness_lt, pi_ub]

lemma θstar_lt_witness : θstar < 1.3026632 := by
  refine θstar_lt_of_F_pos ⟨by norm_num, ?_⟩ F_at_witness
  linarith [pi_lb]

/-! ## The bound -/

/-- **The certified bound, in exact form.**

`3 cos 1.3026632 < min (2 arc x - arc (2 x))`. Numerically the left side is
`0.7947952…`. Through CMV's unformalized geometric argument, this corresponds
to `lam ≥ 1.2581858`, against CMV's `4 / π = 1.2732395…` and the sharp
`1.2581840883…`. -/
theorem min_g_gt_witness {x : ℝ} (hx : 0 < x) : 3 * cos (1.3026632 : ℝ) < g x := by
  have h1 : 3 * cos (1.3026632 : ℝ) < 3 * cos θstar :=
    three_cos_lt_of_θstar_lt (by linarith [pi_lb]) θstar_lt_witness
  have h2 : 3 * cos θstar ≤ g x := min_g_eq_three_mul_cos_θstar hx
  linarith

/-! ## The `π / 4` corollary -/

lemma three_cos_witness_gt_pi_div_four : π / 4 < 3 * cos (1.3026632 : ℝ) := by
  set z : ℝ := π / 2 - 1.3026632 with hz
  have hlo : (0.2681328 : ℝ) < z := by rw [hz]; linarith [pi_lb]
  have hhi : z < (0.2681333 : ℝ) := by rw [hz]; linarith [pi_ub]
  have hz0 : (0:ℝ) < z := by linarith
  have hcube := Real.sin_gt_sub_cube hz0
  have hsq_hi : z^2 ≤ (0.2681333 : ℝ)^2 := by nlinarith
  have hcube_hi : z^3 ≤ (0.2681333 : ℝ)^3 := by nlinarith
  norm_num at hcube_hi
  have hrefl : cos (1.3026632 : ℝ) = sin z := by rw [hz, sin_pi_div_two_sub]
  rw [hrefl]
  linarith [pi_ub]

/-- **CMV Remark 3.17, proved.** The published bound `π / 4` on
`min (2 arc x - arc (2 x))` is not optimal: the minimum strictly exceeds it. -/
theorem min_g_gt_pi_div_four {x : ℝ} (hx : 0 < x) : π / 4 < g x := by
  have := min_g_gt_witness hx
  linarith [three_cos_witness_gt_pi_div_four]

/-! ## Exact comparison thresholds -/

open Real

private lemma cos_double_interval {u sl su cl cu : ℝ}
    (hsl0 : 0 ≤ sl)
    (hs : sl ≤ sin u ∧ sin u ≤ su)
    (hcl : cl ≤ 1 - 2 * su ^ 2)
    (hcu : 1 - 2 * sl ^ 2 ≤ cu) :
    cl ≤ cos (2 * u) ∧ cos (2 * u) ≤ cu := by
  rw [cos_two_mul_sin_sq]
  constructor
  · nlinarith only [hsl0, hs.1, hs.2, hcl]
  · nlinarith only [hsl0, hs.1, hcu]

private lemma sin_cos_double_interval {u sl su cl cu sl' su' cl' cu' : ℝ}
    (hsl0 : 0 ≤ sl)
    (hcl0 : 0 ≤ cl)
    (hs : sl ≤ sin u ∧ sin u ≤ su)
    (hc : cl ≤ cos u ∧ cos u ≤ cu)
    (hsl' : sl' ≤ 2 * sl * cl)
    (hsu' : 2 * su * cu ≤ su')
    (hcl' : cl' ≤ 1 - 2 * su ^ 2)
    (hcu' : 1 - 2 * sl ^ 2 ≤ cu') :
    (sl' ≤ sin (2 * u) ∧ sin (2 * u) ≤ su') ∧
      (cl' ≤ cos (2 * u) ∧ cos (2 * u) ≤ cu') := by
  constructor
  · rw [sin_two_mul]
    constructor
    · nlinarith only [hsl0, hcl0, hs.1, hc.1, hsl']
    · nlinarith only [hsl0, hcl0, hs.1, hs.2, hc.1, hc.2, hsu']
  · rw [cos_two_mul_sin_sq]
    constructor
    · nlinarith only [hsl0, hs.1, hs.2, hcl']
    · nlinarith only [hsl0, hs.1, hcu']

private lemma cos_witness_lower :
    (0.264931734135196 : ℝ) ≤ cos (1.3026632 : ℝ) := by
  have hs128_pos : (0 : ℝ) < 1.3026632 / 128 := by norm_num
  have hs128 :
      (0.010176880572851 : ℝ) ≤ sin ((1.3026632 : ℝ) / 128) ∧
        sin ((1.3026632 : ℝ) / 128) ≤ (0.010176880573943 : ℝ) := by
    constructor
    · have h := sin_gt_sub_cube hs128_pos
      norm_num at h ⊢
      linarith only [h]
    · have habs : |(1.3026632 : ℝ) / 128| ≤ 1 := by
        rw [abs_of_nonneg hs128_pos.le]
        norm_num
      have h := sin_bound habs
      rw [abs_of_nonneg hs128_pos.le, abs_le] at h
      norm_num at h ⊢
      linarith only [h.2]
  have hs64_pos : (0 : ℝ) < 1.3026632 / 64 := by norm_num
  have hs64 :
      (0.020352707082809 : ℝ) ≤ sin ((1.3026632 : ℝ) / 64) ∧
        sin ((1.3026632 : ℝ) / 64) ≤ (0.020352707117745 : ℝ) := by
    constructor
    · have h := sin_gt_sub_cube hs64_pos
      norm_num at h ⊢
      linarith only [h]
    · have habs : |(1.3026632 : ℝ) / 64| ≤ 1 := by
        rw [abs_of_nonneg hs64_pos.le]
        norm_num
      have h := sin_bound habs
      rw [abs_of_nonneg hs64_pos.le, abs_le] at h
      norm_num at h ⊢
      linarith only [h.2]
  have hc64raw := cos_double_interval
    (u := (1.3026632 : ℝ) / 128)
    (sl := 0.010176880572851) (su := 0.010176880573943)
    (cl := 0.999792862203567) (cu := 0.999792862203612)
    (by norm_num) hs128 (by norm_num) (by norm_num)
  have hd64 : 2 * ((1.3026632 : ℝ) / 128) = (1.3026632 : ℝ) / 64 := by ring
  rw [hd64] at hc64raw
  have hc64 := hc64raw
  have h32raw := sin_cos_double_interval
    (u := (1.3026632 : ℝ) / 64)
    (sl := 0.020352707082809) (su := 0.020352707117745)
    (cl := 0.999792862203567) (cu := 0.999792862203612)
    (sl' := 0.040696982535824) (su' := 0.040696982605685)
    (cl' := 0.999171534625958) (cu' := 0.999171534628803)
    (by norm_num) (by norm_num) hs64 hc64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd32 : 2 * ((1.3026632 : ℝ) / 64) = (1.3026632 : ℝ) / 32 := by ring
  rw [hd32] at h32raw
  have h32 := h32raw
  have h16raw := sin_cos_double_interval
    (u := (1.3026632 : ℝ) / 32)
    (sl := 0.040696982535824) (su := 0.040696982605685)
    (cl := 0.999171534625958) (cu := 0.999171534628803)
    (sl' := 0.081326532989930) (su' := 0.081326533129768)
    (cl' := 0.996687511213585) (cu' := 0.996687511224958)
    (by norm_num) (by norm_num) h32.1 h32.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd16 : 2 * ((1.3026632 : ℝ) / 32) = (1.3026632 : ℝ) / 16 := by ring
  rw [hd16] at h16raw
  have h16 := h16raw
  have h8raw := sin_cos_double_interval
    (u := (1.3026632 : ℝ) / 16)
    (sl := 0.081326532989930) (su := 0.081326533129768)
    (cl := 0.996687511213585) (cu := 0.996687511224958)
    (sl' := 0.162114279522725) (su' := 0.162114279803326)
    (cl' := 0.986771990018185) (cu' := 0.986771990063676)
    (by norm_num) (by norm_num) h16.1 h16.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd8 : 2 * ((1.3026632 : ℝ) / 16) = (1.3026632 : ℝ) / 8 := by ring
  rw [hd8] at h8raw
  have h8 := h8raw
  have h4raw := sin_cos_double_interval
    (u := (1.3026632 : ℝ) / 8)
    (sl := 0.162114279522725) (su := 0.162114279803326)
    (cl := 0.986771990018185) (cu := 0.986771990063676)
    (sl' := 0.319939660430007) (su' := 0.319939660998536)
    (cl' := 0.947437920567697) (cu' := 0.947437920749656)
    (by norm_num) (by norm_num) h8.1 h8.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd4 : 2 * ((1.3026632 : ℝ) / 8) = (1.3026632 : ℝ) / 4 := by ring
  rw [hd4] at h4raw
  have h4 := h4raw
  have h2raw := sin_cos_double_interval
    (u := (1.3026632 : ℝ) / 4)
    (sl := 0.319939660430007) (su := 0.319939660998536)
    (cl := 0.947437920567697) (cu := 0.947437920749656)
    (sl' := 0.606245933169881) (su' := 0.606245934363606)
    (cl' := 0.795277226640283) (cu' := 0.795277227367864)
    (by norm_num) (by norm_num) h4.1 h4.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd2 : 2 * ((1.3026632 : ℝ) / 4) = (1.3026632 : ℝ) / 2 := by ring
  rw [hd2] at h2raw
  have h2 := h2raw
  have hcosraw := cos_double_interval
    (u := (1.3026632 : ℝ) / 2)
    (sl := 0.606245933169881) (su := 0.606245934363606)
    (cl := 0.264931734135196) (cu := 1)
    (by norm_num) h2.1 (by norm_num) (by norm_num)
  have hd1 : 2 * ((1.3026632 : ℝ) / 2) = (1.3026632 : ℝ) := by ring
  rw [hd1] at hcosraw
  exact hcosraw.1

private lemma inv_baseline_lt_three_cos_witness :
    1 / (1.2581858 : ℝ) < 3 * cos (1.3026632 : ℝ) := by
  have h := cos_witness_lower
  norm_num at h ⊢
  nlinarith only [h]

theorem cmv_comparison_bound {lam x : ℝ}
    (hlam : (1.2581858 : ℝ) ≤ lam)
    (hx : 0 < x) :
    1 / lam < g x := by
  have hinv : 1 / lam ≤ 1 / (1.2581858 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hlam
  exact lt_of_le_of_lt hinv
    (lt_trans inv_baseline_lt_three_cos_witness (min_g_gt_witness hx))

/-! ## Optimized exact comparison threshold -/

private lemma opt_pi_lb : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
private lemma opt_pi_ub : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20

private lemma opt_sin_reflection_upper :
    sin (2.60532567462 : ℝ) ≤ 0.510930572191682027065 := by
  have hs256 :
      (0.002094791354553993674 : ℝ) ≤ sin ((π - 2.60532567462) / 256) ∧
        sin ((π - 2.60532567462) / 256) ≤ (0.002094791354554397057 : ℝ) := by
    set u : ℝ := (π - 2.60532567462) / 256 with hu
    have hlo : (0.00209479288660075483 : ℝ) < u := by rw [hu]; linarith [opt_pi_lb]
    have hhi : u < (0.00209479288660075484 : ℝ) := by rw [hu]; linarith [opt_pi_ub]
    have h0 : (0 : ℝ) < u := by linarith
    constructor
    · have h := sin_gt_sub_cube h0
      have h2 : u ^ 2 ≤ (0.00209479288660075484 : ℝ) ^ 2 := by nlinarith
      have h3 : u ^ 3 ≤ (0.00209479288660075484 : ℝ) ^ 3 := by nlinarith
      norm_num at h3
      linarith only [h, hlo, h3]
    · have habs : |u| ≤ 1 := by rw [abs_of_nonneg h0.le]; linarith
      have h := sin_bound habs
      rw [abs_of_nonneg h0.le, abs_le] at h
      have h2l : (0.00209479288660075483 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith
      have h3 : (0.00209479288660075483 : ℝ) ^ 3 ≤ u ^ 3 := by nlinarith
      have h2h : u ^ 2 ≤ (0.00209479288660075484 : ℝ) ^ 2 := by nlinarith
      have h4h : u ^ 4 ≤ (0.00209479288660075484 : ℝ) ^ 4 := by nlinarith
      have h5 : u ^ 5 ≤ (0.00209479288660075484 : ℝ) ^ 5 := by nlinarith
      norm_num at h3 h5
      linarith only [h.2, hhi, h3, h5]
  have hs128 :
      (0.004189573516827420428 : ℝ) ≤ sin ((π - 2.60532567462) / 128) ∧
        sin ((π - 2.60532567462) / 128) ≤ (0.004189573516840328335 : ℝ) := by
    set u : ℝ := (π - 2.60532567462) / 128 with hu
    have hlo : (0.00418958577320150967 : ℝ) < u := by rw [hu]; linarith [opt_pi_lb]
    have hhi : u < (0.00418958577320150968 : ℝ) := by rw [hu]; linarith [opt_pi_ub]
    have h0 : (0 : ℝ) < u := by linarith
    constructor
    · have h := sin_gt_sub_cube h0
      have h2 : u ^ 2 ≤ (0.00418958577320150968 : ℝ) ^ 2 := by nlinarith
      have h3 : u ^ 3 ≤ (0.00418958577320150968 : ℝ) ^ 3 := by nlinarith
      norm_num at h3
      linarith only [h, hlo, h3]
    · have habs : |u| ≤ 1 := by rw [abs_of_nonneg h0.le]; linarith
      have h := sin_bound habs
      rw [abs_of_nonneg h0.le, abs_le] at h
      have h2l : (0.00418958577320150967 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith
      have h3 : (0.00418958577320150967 : ℝ) ^ 3 ≤ u ^ 3 := by nlinarith
      have h2h : u ^ 2 ≤ (0.00418958577320150968 : ℝ) ^ 2 := by nlinarith
      have h4h : u ^ 4 ≤ (0.00418958577320150968 : ℝ) ^ 4 := by nlinarith
      have h5 : u ^ 5 ≤ (0.00418958577320150968 : ℝ) ^ 5 := by nlinarith
      norm_num at h3 h5
      linarith only [h.2, hhi, h3, h5]
  have hc128raw := cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 256)
    (sl := 0.002094791354553993674) (su := 0.002094791354554397057)
    (cl := 0.999991223698361768308) (cu := 0.999991223698361771689)
    (by norm_num) hs256 (by norm_num) (by norm_num)
  have hd128 : 2 * ((π - 2.60532567462 : ℝ) / 256) = (π - 2.60532567462) / 128 := by ring
  rw [hd128] at hc128raw
  have hc128 := hc128raw
  have h64raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 128)
    (sl := 0.004189573516827420428) (su := 0.004189573516840328335)
    (cl := 0.999991223698361768308) (cu := 0.999991223698361771689)
    (sl' := 0.008379073495733002406) (su' := 0.008379073495758818023)
    (cl' := 0.999964894947493980326) (cu' := 0.999964894947494196641)
    (by norm_num) (by norm_num) hs128 hc128
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd64 : 2 * ((π - 2.60532567462 : ℝ) / 128) = (π - 2.60532567462) / 64 := by ring
  rw [hd64] at h64raw
  have h64 := h64raw
  have h32raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 64)
    (sl := 0.008379073495733002406) (su := 0.008379073495758818023)
    (cl := 0.999964894947493980326) (cu := 0.999964894947494196641)
    (sl' := 0.016757558695835965802) (su' := 0.016757558695887598849)
    (cl' := 0.999859582254705344202) (cu' := 0.999859582254706209446)
    (by norm_num) (by norm_num) h64.1 h64.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd32 : 2 * ((π - 2.60532567462 : ℝ) / 64) = (π - 2.60532567462) / 32 := by ring
  rw [hd32] at h32raw
  have h32 := h32raw
  have h16raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 32)
    (sl := 0.016757558695835965802) (su := 0.016757558695887598849)
    (cl := 0.999859582254705344202) (cu := 0.999859582254706209446)
    (sl' := 0.033510411274454507325) (su' := 0.033510411274557787919)
    (cl' := 0.999438368453107763834) (cu' := 0.999438368453111224810)
    (by norm_num) (by norm_num) h32.1 h32.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd16 : 2 * ((π - 2.60532567462 : ℝ) / 32) = (π - 2.60532567462) / 16 := by ring
  rw [hd16] at h16raw
  have h16 := h16raw
  have h8raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 16)
    (sl := 0.033510411274454507325) (su := 0.033510411274557787919)
    (cl := 0.999438368453107763834) (cu := 0.999438368453111224810)
    (sl' := 0.066983181540666880817) (su' := 0.066983181540873557952)
    (cl' := 0.997754104672419980583) (cu' := 0.997754104672433824485)
    (by norm_num) (by norm_num) h16.1 h16.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd8 : 2 * ((π - 2.60532567462 : ℝ) / 16) = (π - 2.60532567462) / 8 := by ring
  rw [hd8] at h8raw
  have h8 := h8raw
  have h4raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 8)
    (sl := 0.066983181540666880817) (su := 0.066983181540873557952)
    (cl := 0.997754104672419980583) (cu := 0.997754104672433824485)
    (sl' := 0.133665488652436505726) (su' := 0.133665488652850786263)
    (cl' := 0.991026506781324751693) (cu' := 0.991026506781380127262)
    (by norm_num) (by norm_num) h8.1 h8.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd4 : 2 * ((π - 2.60532567462 : ℝ) / 8) = (π - 2.60532567462) / 4 := by ring
  rw [hd4] at h4raw
  have h4 := h4raw
  have h2raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 4)
    (sl := 0.133665488652436505726) (su := 0.133665488652850786263)
    (cl := 0.991026506781324751693) (cu := 0.991026506781380127262)
    (sl' := 0.264932084592885906775) (su' := 0.264932084593721836368)
    (cl' := 0.964267074286389235399) (cu' := 0.964267074286610735442)
    (by norm_num) (by norm_num) h4.1 h4.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd2 : 2 * ((π - 2.60532567462 : ℝ) / 4) = (π - 2.60532567462) / 2 := by ring
  rw [hd2] at h2raw
  have h2 := h2raw
  have h1raw := sin_cos_double_interval
    (u := (π - 2.60532567462 : ℝ) / 2)
    (sl := 0.264932084592885906775) (su := 0.264932084593721836368)
    (cl := 0.964267074286389235399) (cu := 0.964267074286610735442)
    (sl' := 0.510930572189952543361) (su' := 0.510930572191682027065)
    (cl' := 0.859621981105650033593) (cu' := 0.859621981106535891873)
    (by norm_num) (by norm_num) h2.1 h2.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd1 : 2 * ((π - 2.60532567462 : ℝ) / 2) = π - 2.60532567462 := by ring
  rw [hd1] at h1raw
  have hrefl : sin (2.60532567462 : ℝ) = sin (π - 2.60532567462) := (sin_pi_sub _).symm
  rw [hrefl]
  exact h1raw.1.2

private lemma opt_F_at_witness : 0 < F (1.30266283731 : ℝ) := by
  have hdouble : (3 : ℝ) * (sin 1.30266283731 * cos 1.30266283731) =
      3 / 2 * sin 2.60532567462 := by
    have h : (2.60532567462 : ℝ) = 2 * 1.30266283731 := by norm_num
    rw [h, sin_two_mul]
    ring
  rw [F, hdouble]
  linarith [opt_sin_reflection_upper, opt_pi_ub]

private lemma opt_θstar_lt_witness : θstar < 1.30266283731 := by
  refine θstar_lt_of_F_pos ⟨by norm_num, ?_⟩ opt_F_at_witness
  linarith [opt_pi_lb]

private lemma opt_min_g_gt_witness {x : ℝ} (hx : 0 < x) :
    3 * cos (1.30266283731 : ℝ) < g x := by
  have h1 : 3 * cos (1.30266283731 : ℝ) < 3 * cos θstar :=
    three_cos_lt_of_θstar_lt (by linarith [opt_pi_lb]) opt_θstar_lt_witness
  have h2 : 3 * cos θstar ≤ g x := min_g_eq_three_mul_cos_θstar hx
  linarith

private lemma opt_cos_witness_lower :
    (0.264932084590720839353931 : ℝ) ≤ cos (1.30266283731 : ℝ) := by
  have hs512_pos : (0 : ℝ) < 1.30266283731 / 512 := by norm_num
  have hs512 :
      (0.002544260609167936018368 : ℝ) ≤ sin ((1.30266283731 : ℝ) / 512) ∧
        sin ((1.30266283731 : ℝ) / 512) ≤ (0.002544260609169002148735 : ℝ) := by
    constructor
    · have h := sin_gt_sub_cube hs512_pos
      norm_num at h ⊢
      linarith only [h]
    · have habs : |(1.30266283731 : ℝ) / 512| ≤ 1 := by
        rw [abs_of_nonneg hs512_pos.le]
        norm_num
      have h := sin_bound habs
      rw [abs_of_nonneg hs512_pos.le, abs_le] at h
      norm_num at h ⊢
      linarith only [h.2]
  have hs256_pos : (0 : ℝ) < 1.30266283731 / 256 := by norm_num
  have hs256 :
      (0.005088504748616925646946 : ℝ) ≤ sin ((1.30266283731 : ℝ) / 256) ∧
        sin ((1.30266283731 : ℝ) / 256) ≤ (0.005088504748651041818669 : ℝ) := by
    constructor
    · have h := sin_gt_sub_cube hs256_pos
      norm_num at h ⊢
      linarith only [h]
    · have habs : |(1.30266283731 : ℝ) / 256| ≤ 1 := by
        rw [abs_of_nonneg hs256_pos.le]
        norm_num
      have h := sin_bound habs
      rw [abs_of_nonneg hs256_pos.le, abs_le] at h
      norm_num at h ⊢
      linarith only [h.2]
  have hc256raw := cos_double_interval
    (u := (1.30266283731 : ℝ) / 512)
    (sl := 0.002544260609167936018368) (su := 0.002544260609169002148735)
    (cl := 0.999987053475905261956198) (cu := 0.999987053475905272806253)
    (by norm_num) hs512 (by norm_num) (by norm_num)
  have hd256 : 2 * ((1.30266283731 : ℝ) / 512) = (1.30266283731 : ℝ) / 256 := by ring
  rw [hd256] at hc256raw
  have hc256 := hc256raw
  have h128raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 256)
    (sl := 0.005088504748616925646946) (su := 0.005088504748651041818669)
    (cl := 0.999987053475905261956198) (cu := 0.999987053475905272806253)
    (sl' := 0.010176877740335182977931) (su' := 0.010176877740403414548427)
    (cl' := 0.999948214238845911595449) (cu' := 0.999948214238846605996657)
    (by norm_num) (by norm_num) hs256 hc256
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd128 : 2 * ((1.30266283731 : ℝ) / 256) = (1.30266283731 : ℝ) / 128 := by ring
  rw [hd128] at h128raw
  have h128 := h128raw
  have h64raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 128)
    (sl := 0.010176877740335182977931) (su := 0.010176877740403414548427)
    (cl := 0.999948214238845911595449) (cu := 0.999948214238846605996657)
    (sl' := 0.020352701445950455242462) (su' := 0.020352701446086925450279)
    (cl' := 0.999792862318913762982648) (cu' := 0.999792862318916540520053)
    (by norm_num) (by norm_num) h128.1 h128.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd64 : 2 * ((1.30266283731 : ℝ) / 128) = (1.30266283731 : ℝ) / 64 := by ring
  rw [hd64] at h64raw
  have h64 := h64raw
  have h32raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 64)
    (sl := 0.020352701445950455242462) (su := 0.020352701446086925450279)
    (cl := 0.999792862318913762982648) (cu := 0.999792862318916540520053)
    (sl' := 0.040696971269138201124108) (su' := 0.040696971269411198064278)
    (cl' := 0.999171535087692902347217) (cu' := 0.999171535087704012496802)
    (by norm_num) (by norm_num) h64.1 h64.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd32 : 2 * ((1.30266283731 : ℝ) / 64) = (1.30266283731 : ℝ) / 32 := by ring
  rw [hd32] at h32raw
  have h32 := h32raw
  have h16raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 32)
    (sl := 0.040696971269138201124108) (su := 0.040696971269411198064278)
    (cl := 0.999171535087692902347217) (cu := 0.999171535087704012496802)
    (sl' := 0.081326510512809100143291) (su' := 0.081326510513355545985737)
    (cl' := 0.996687513058993438996046) (cu' := 0.996687513059037879590570)
    (by norm_num) (by norm_num) h32.1 h32.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd16 : 2 * ((1.30266283731 : ℝ) / 32) = (1.30266283731 : ℝ) / 16 := by ring
  rw [hd16] at h16raw
  have h16 := h16raw
  have h8raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 16)
    (sl := 0.081326510512809100143291) (su := 0.081326510513355545985737)
    (cl := 0.996687513058993438996046) (cu := 0.996687513059037879590570)
    (sl' := 0.162114235017555574404566) (su' := 0.162114235018652074296981)
    (cl' := 0.986771997375442139696274) (cu' := 0.986771997375619901830477)
    (by norm_num) (by norm_num) h16.1 h16.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd8 : 2 * ((1.30266283731 : ℝ) / 16) = (1.30266283731 : ℝ) / 8 := by ring
  rw [hd8] at h8raw
  have h8 := h8raw
  have h4raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 8)
    (sl := 0.162114235017555574404566) (su := 0.162114235018652074296981)
    (cl := 0.986771997375442139696274) (cu := 0.986771997375619901830477)
    (sl' := 0.319939574982530318967782) (su' := 0.319939574984751945290507)
    (cl' := 0.947437949608634482976031) (cu' := 0.947437949609345515941057)
    (by norm_num) (by norm_num) h8.1 h8.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd4 : 2 * ((1.30266283731 : ℝ) / 8) = (1.30266283731 : ℝ) / 4 := by ring
  rw [hd4] at h4raw
  have h4 := h4raw
  have h2raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 4)
    (sl := 0.319939574982530318967782) (su := 0.319939574984751945290507)
    (cl := 0.947437949608634482976031) (cu := 0.947437949609345515941057)
    (sl' := 0.606245789840212988072429) (su' := 0.606245789844877669417689)
    (cl' := 0.795277336717152574572862) (cu' := 0.795277336719995719298724)
    (by norm_num) (by norm_num) h4.1 h4.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd2 : 2 * ((1.30266283731 : ℝ) / 4) = (1.30266283731 : ℝ) / 2 := by ring
  rw [hd2] at h2raw
  have h2 := h2raw
  have h1raw := sin_cos_double_interval
    (u := (1.30266283731 : ℝ) / 2)
    (sl := 0.606245789840212988072429) (su := 0.606245789844877669417689)
    (cl := 0.795277336717152574572862) (cu := 0.795277336719995719298724)
    (sl' := 0.964267074280222359669416) (su' := 0.964267074291089079423149)
    (cl' := 0.264932084590720839353931) (cu' := 0.264932084602032613060016)
    (by norm_num) (by norm_num) h2.1 h2.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd1 : 2 * ((1.30266283731 : ℝ) / 2) = (1.30266283731 : ℝ) := by ring
  rw [hd1] at h1raw
  exact h1raw.2.1

private lemma opt_inv_candidate_lt_three_cos_witness :
    1 / (1.2581840884 : ℝ) < 3 * cos (1.30266283731 : ℝ) := by
  have h := opt_cos_witness_lower
  norm_num at h ⊢
  nlinarith only [h]

theorem cmv_comparison_bound_optimized {lam x : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (hx : 0 < x) :
    1 / lam < g x := by
  have hinv : 1 / lam ≤ 1 / (1.2581840884 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hlam
  exact lt_of_le_of_lt hinv
    (lt_trans opt_inv_candidate_lt_three_cos_witness (opt_min_g_gt_witness hx))
