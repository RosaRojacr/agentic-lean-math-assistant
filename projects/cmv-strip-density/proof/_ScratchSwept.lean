import CMVGeometry

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal

noncomputable section

abbrev EP := EuclideanPlane

def hsweep (S : Set EP) (L : ℝ) : Set EP :=
  {q | ∃ p ∈ S, ∃ t ∈ Icc (0 : ℝ) L,
    q.fst = p.fst + t ∧ q.snd = p.snd}

lemma hsweep_member_bound (S : Set EP) (L : ℝ) (hL : 0 ≤ L)
    (hS : S.Nonempty) (hD : ediam S ≠ ∞) :
    volume (hsweep S L) ≤
      ENNReal.ofReal L * ediam S + ediam S ^ (2 : ℕ) := by
  let D : ℝ := Metric.diam S
  let X : Set ℝ := WithLp.fst '' S
  let Y : Set ℝ := WithLp.snd '' S
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hXne : X.Nonempty := hS.image _
  have hYne : Y.Nonempty := hS.image _
  have hXbdd : BddBelow X := by
    rcases hS with ⟨a, ha⟩
    refine ⟨a.fst - D, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    have hdist := (WithLp.dist_fst_le a p).trans
      (Metric.dist_le_diam_of_mem' hD ha hp)
    rw [Real.dist_eq] at hdist
    linarith [le_trans (le_abs_self (a.fst - p.fst)) hdist]
  have hYbdd : BddBelow Y := by
    rcases hS with ⟨a, ha⟩
    refine ⟨a.snd - D, ?_⟩
    rintro y ⟨p, hp, rfl⟩
    have hdist := (WithLp.dist_snd_le a p).trans
      (Metric.dist_le_diam_of_mem' hD ha hp)
    rw [Real.dist_eq] at hdist
    linarith [le_trans (le_abs_self (a.snd - p.snd)) hdist]
  let xmin : ℝ := sInf X
  let ymin : ℝ := sInf Y
  have hx (p : EP) (hp : p ∈ S) : p.fst ∈ Icc xmin (xmin + D) := by
    constructor
    · exact csInf_le hXbdd ⟨p, hp, rfl⟩
    · have hlow : p.fst - D ≤ xmin := by
        apply le_csInf hXne
        rintro x ⟨q, hq, rfl⟩
        have hdist := (WithLp.dist_fst_le p q).trans
          (Metric.dist_le_diam_of_mem' hD hp hq)
        rw [Real.dist_eq] at hdist
        linarith [le_trans (le_abs_self (p.fst - q.fst)) hdist]
      linarith
  have hy (p : EP) (hp : p ∈ S) : p.snd ∈ Icc ymin (ymin + D) := by
    constructor
    · exact csInf_le hYbdd ⟨p, hp, rfl⟩
    · have hlow : p.snd - D ≤ ymin := by
        apply le_csInf hYne
        rintro y ⟨q, hq, rfl⟩
        have hdist := (WithLp.dist_snd_le p q).trans
          (Metric.dist_le_diam_of_mem' hD hp hq)
        rw [Real.dist_eq] at hdist
        linarith [le_trans (le_abs_self (p.snd - q.snd)) hdist]
      linarith
  let R : Set (ℝ × ℝ) := Icc xmin (xmin + D + L) ×ˢ Icc ymin (ymin + D)
  have hsub : hsweep S L ⊆ WithLp.toLp 2 '' R := by
    rintro q ⟨p, hp, t, ht, hq1, hq2⟩
    refine ⟨WithLp.ofLp q, ?_, WithLp.toLp_ofLp 2 q⟩
    constructor
    · rw [mem_Icc]
      have hpX := hx p hp
      constructor
      · change xmin ≤ q.fst
        rw [hq1]
        linarith [hpX.1, ht.1]
      · change q.fst ≤ xmin + D + L
        rw [hq1]
        linarith [hpX.2, ht.2]
    · simpa [hq2] using hy p hp
  calc
    volume (hsweep S L) ≤ volume (WithLp.toLp 2 '' R) := measure_mono hsub
    _ = volume R := by
      have himage : WithLp.toLp 2 '' R = WithLp.ofLp ⁻¹' R := by
        ext q
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hq
          exact ⟨WithLp.ofLp q, hq, WithLp.toLp_ofLp 2 q⟩
      rw [himage]
      exact (WithLp.volume_preserving_ofLp ℝ ℝ).measure_preimage
        (show NullMeasurableSet R volume by
          exact (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)
    _ = ENNReal.ofReal (D + L) * ENNReal.ofReal D := by
      dsimp only [R]
      rw [Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Icc, Real.volume_Icc]
      ring_nf
    _ = ENNReal.ofReal L * ediam S + ediam S ^ (2 : ℕ) := by
      have hdiam : ENNReal.ofReal D = ediam S := by
        exact ENNReal.ofReal_toReal hD
      rw [ENNReal.ofReal_add hD0 hL, hdiam]
      rw [pow_two, add_mul]
      ac_rfl

lemma generic_sweep_le
    (sweep : Set EP → ℝ → Set EP)
    (hEmpty : ∀ L, sweep ∅ L = ∅)
    (hCover : ∀ (S : Set EP) (L : ℝ) (t : ℕ → Set EP),
      S ⊆ ⋃ n, t n → sweep S L ⊆ ⋃ n, sweep (t n) L)
    (hBound : ∀ (A : Set EP) (L : ℝ), 0 < L →
      volume (sweep A L) ≤
        ENNReal.ofReal L * ediam A + ediam A ^ (2 : ℕ))
    (S : Set EP) (L : ℝ) (hL : 0 < L) :
    volume (sweep S L) ≤ ENNReal.ofReal L * (μH[1] : Measure EP) S := by
  let ell : ℝ≥0∞ := ENNReal.ofReal L
  let H : ℝ≥0∞ := (μH[1] : Measure EP) S
  have hell0 : ell ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.2 hL)
  have helltop : ell ≠ ∞ := ENNReal.ofReal_ne_top
  have fixed_radius (r : ℝ≥0∞) (hr : 0 < r) (hrtop : r ≠ ∞) :
      volume (sweep S L) ≤ (ell + r) * H := by
    let C := ell + r
    have hC0 : C ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hell0) (le_add_right ell r))
    have hCtop : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨helltop, hrtop⟩
    have hinf :
        (⨅ (t : ℕ → Set EP) (_ : S ⊆ ⋃ n, t n)
            (_ : ∀ n, ediam (t n) ≤ r),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (1 : ℝ)) ≤ H := by
      dsimp only [H]
      rw [Measure.hausdorffMeasure_apply]
      exact le_iSup₂_of_le r hr le_rfl
    calc
      volume (sweep S L) ≤
          C * (⨅ (t : ℕ → Set EP) (_ : S ⊆ ⋃ n, t n)
            (_ : ∀ n, ediam (t n) ≤ r),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (1 : ℝ)) := by
        rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
        refine le_iInf fun t => ?_
        rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
        refine le_iInf fun hst => ?_
        rw [ENNReal.mul_iInf_of_ne hC0 hCtop]
        refine le_iInf fun hdiam => ?_
        calc
          volume (sweep S L) ≤ volume (⋃ n, sweep (t n) L) :=
            measure_mono (hCover S L t hst)
          _ ≤ ∑' n, volume (sweep (t n) L) := measure_iUnion_le _
          _ ≤ ∑' n, C * (⨆ _ : (t n).Nonempty,
              ediam (t n) ^ (1 : ℝ)) := by
            apply ENNReal.tsum_le_tsum
            intro n
            rcases eq_empty_or_nonempty (t n) with hempty | hn
            · subst t
              simp [hEmpty]
            · have hdtop : ediam (t n) ≠ ∞ :=
                ne_top_of_le_ne_top hrtop (hdiam n)
              calc
                volume (sweep (t n) L) ≤
                    ell * ediam (t n) + ediam (t n) ^ (2 : ℕ) := by
                  simpa only [ell] using hBound (t n) L hL
                _ ≤ ell * ediam (t n) + r * ediam (t n) := by
                  rw [pow_two]
                  exact add_le_add_left (mul_right_mono (hdiam n)) _
                _ = C * ediam (t n) := by
                  dsimp only [C]
                  rw [add_mul]
                _ = C * (⨆ _ : (t n).Nonempty,
                    ediam (t n) ^ (1 : ℝ)) := by
                  simp [hn, ENNReal.rpow_one]
          _ = C * (∑' n, ⨆ _ : (t n).Nonempty,
              ediam (t n) ^ (1 : ℝ)) := ENNReal.tsum_mul_left
      _ ≤ C * H := mul_left_mono hinf
  rcases eq_top_or_lt_top H with hH | hH
  · simp [hH, hell0]
  · have hHtop : H ≠ ∞ := ne_of_lt hH
    have hrlim : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero
    have hlim : Tendsto (fun n : ℕ => (ell + (n : ℝ≥0∞)⁻¹) * H)
        atTop (𝓝 (ell * H)) := by
      convert (tendsto_const_nhds.add hrlim).mul_const (Or.inr hHtop) using 1 <;> simp
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply fixed_radius
    · exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)
    · exact ENNReal.inv_ne_top
