import FCAppendix.PayOnce.BoundedEndpoint

namespace FCAppendix.PayOnce.SharpEndpoint

open MeasureTheory Filter Topology Set ManyProposers BoundedEndpoint

theorem pStar_ge_gap {n : ℕ} (hn : 2 ≤ n) {t M w : ℝ}
    (ht : 0 < t) (htw : t < w) (hwM : w ≤ M) :
    (w - t) / (M * ((n : ℝ) - 1) + (M - t)) ≤ pStar n t w := by
  have ha := nat_sub_one_pos hn
  have hgap : 0 < w - t := sub_pos.mpr htw
  have hw := ht.trans htw
  have hM := hw.trans_le hwM
  let x := logPlus (w / t) / ((n : ℝ) - 1)
  have hx : 0 ≤ x := div_nonneg (logPlus_nonneg _) ha.le
  have hlog := div_le_div_of_nonneg_right (gap_div_le_logPlus ht htw) ha.le
  have hlow : (w - t) / (w * ((n : ℝ) - 1)) ≤ x := by
    simpa [x, div_div] using hlog
  have hfrac : (w - t) / (w * ((n : ℝ) - 1) + (w - t)) ≤ x / (1 + x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hlow' := (div_le_iff₀ (mul_pos hw ha)).mp hlow
    nlinarith
  have hden : w * ((n : ℝ) - 1) + (w - t) ≤ M * ((n : ℝ) - 1) + (M - t) := by
    nlinarith [mul_le_mul_of_nonneg_right hwM ha.le]
  calc
    (w - t) / (M * ((n : ℝ) - 1) + (M - t)) ≤
        (w - t) / (w * ((n : ℝ) - 1) + (w - t)) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hden
    _ ≤ x / (1 + x) := hfrac
    _ ≤ pStar n t w := by
      rw [pStar_eq_exp hn ht]
      exact div_one_add_le_one_sub_exp_neg hx

theorem pStar_gap_envelope {n : ℕ} (hn : 2 ≤ n) {t M w : ℝ}
    (ht : 0 < t) (hwM : w ≤ M) :
    max (w - t) 0 / (M * ((n : ℝ) - 1) + (M - t)) ≤ pStar n t w ∧
      pStar n t w ≤ max (w - t) 0 / (t * ((n : ℝ) - 1)) := by
  by_cases htw : t < w
  · rw [max_eq_left (by linarith : 0 ≤ w - t)]
    refine ⟨pStar_ge_gap hn ht htw hwM, ?_⟩
    calc
      pStar n t w ≤ logPlus (w / t) / ((n : ℝ) - 1) := pStar_le_log_div hn ht w
      _ ≤ ((w - t) / t) / ((n : ℝ) - 1) :=
        div_le_div_of_nonneg_right (logPlus_div_le_gap ht htw) (nat_sub_one_pos hn).le
      _ = (w - t) / (t * ((n : ℝ) - 1)) := by rw [div_div]
  · rw [pStar_eq_zero hn ht (not_lt.mp htw), max_eq_right (by linarith : w - t ≤ 0)]
    simp

theorem success_quadratic_bounds (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ success n p - n * p + ((n : ℝ) * (n - 1) / 2) * p ^ 2 ∧
      success n p - n * p + ((n : ℝ) * (n - 1) / 2) * p ^ 2 ≤
        ((n : ℝ) * (n - 1) * (n - 2) / 6) * p ^ 3 := by
  induction n with
  | zero => simp [success]
  | succ n ih =>
    have hs : success (n + 1) p = p + (1 - p) * success n p := by
      unfold success
      ring
    rw [hs]
    push_cast
    have hlo := mul_nonneg (sub_nonneg.mpr hp1) ih.1
    have hup := mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hp1)
    have hc : 0 ≤ (n : ℝ) * (n - 1) := by
      by_cases hn : n = 0
      · simp [hn]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr this)
    have hc' : 0 ≤ (n : ℝ) * (n - 1) * (n - 2) := by
      by_cases hn : n ≤ 1
      · interval_cases n <;> norm_num
      · have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        exact mul_nonneg hc (by linarith)
    constructor
    · nlinarith [mul_nonneg hc (pow_nonneg hp0 3)]
    · nlinarith [mul_nonneg hc' (pow_nonneg hp0 4)]

theorem integrable_pStar_pow (μW : Measure ℝ) [IsFiniteMeasure μW]
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Integrable (fun w => pStar n t w ^ j) μW := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((continuous_pStar hn ht).pow j).aestronglyMeasurable (Eventually.of_forall ?_)
  intro w
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pStar_nonneg n t w) j)]
  exact pow_le_one₀ (pStar_nonneg n t w) (pStar_le_one n ht.le w)

theorem integral_pStar_pow_pos (μW : Measure ℝ) [IsFiniteMeasure μW]
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hend : ∀ u > 0, 0 < μW (Ioi (M - u)))
    {t : ℝ} (ht : 0 < t) (htM : t < M) (j : ℕ) :
    0 < ∫ w, pStar n t w ^ j ∂μW := by
  rw [integral_pos_iff_support_of_nonneg (fun w => pow_nonneg (pStar_nonneg n t w) j)
    (integrable_pStar_pow μW hn ht j)]
  have h := hend (M - t) (sub_pos.mpr htM)
  rw [sub_sub_cancel] at h
  refine lt_of_lt_of_le h (measure_mono ?_)
  intro w hw
  exact Function.mem_support.mpr (pow_pos (pStar_pos hn ht hw) j).ne'

theorem cubic_coefficient_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) * (n - 1) * (n - 2) / 6 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)) (by norm_num)

theorem coverage_loss_bounds (μW : Measure ℝ) [IsFiniteMeasure μW]
    {n : ℕ} (hn : 2 ≤ n) {M t : ℝ} (ht : 0 < t) (hle : ∀ᵐ w ∂μW, w ≤ M) :
    (((n : ℝ) * (n - 1) / 2) - ((n : ℝ) * (n - 1) * (n - 2) / 6) * pStar n t M) *
        (∫ w, pStar n t w ^ 2 ∂μW) ≤
      (n : ℝ) * (∫ w, pStar n t w ∂μW) - (∫ w, success n (pStar n t w) ∂μW) ∧
    (n : ℝ) * (∫ w, pStar n t w ∂μW) - (∫ w, success n (pStar n t w) ∂μW) ≤
      ((n : ℝ) * (n - 1) / 2) * (∫ w, pStar n t w ^ 2 ∂μW) := by
  let a : ℝ := (n : ℝ) * (n - 1) / 2
  let b : ℝ := (n : ℝ) * (n - 1) * (n - 2) / 6
  have hb : 0 ≤ b := cubic_coefficient_nonneg n
  have hI := integrable_pStar μW hn ht
  have hI2 := integrable_pStar_pow μW hn ht 2
  have hIS : Integrable (fun w => success n (pStar n t w)) μW :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_success n).comp (continuous_pStar hn ht)).aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs]
        exact abs_success_pStar_le n ht.le w))
  have hlow : ∀ᵐ w ∂μW, (a - b * pStar n t M) * pStar n t w ^ 2 ≤
      (n : ℝ) * pStar n t w - success n (pStar n t w) := by
    filter_upwards [hle] with w hw
    have hexp := (success_quadratic_bounds n (pStar_nonneg n t w) (pStar_le_one n ht.le w)).2
    have hmul := mul_le_mul_of_nonneg_right (pStar_mono_value hn ht hw)
      (sq_nonneg (pStar n t w))
    have hmul' := mul_le_mul_of_nonneg_left hmul hb
    change success n (pStar n t w) - n * pStar n t w + a * pStar n t w ^ 2 ≤
      b * pStar n t w ^ 3 at hexp
    nlinarith
  have hup : ∀ w, (n : ℝ) * pStar n t w - success n (pStar n t w) ≤ a * pStar n t w ^ 2 := by
    intro w
    have h := (success_quadratic_bounds n (pStar_nonneg n t w) (pStar_le_one n ht.le w)).1
    change 0 ≤ success n (pStar n t w) - n * pStar n t w + a * pStar n t w ^ 2 at h
    linarith
  have hlow' := integral_mono_ae (hI2.const_mul (a - b * pStar n t M))
    ((hI.const_mul (n : ℝ)).sub hIS) hlow
  have hup' := integral_mono ((hI.const_mul (n : ℝ)).sub hIS) (hI2.const_mul a) hup
  simp only [Pi.sub_apply] at hlow' hup'
  rw [integral_const_mul, integral_sub (hI.const_mul _) hIS, integral_const_mul] at hlow'
  rw [integral_sub (hI.const_mul _) hIS, integral_const_mul, integral_const_mul] at hup'
  exact ⟨hlow', hup'⟩

theorem tendsto_coverage_loss_div_second_moment (μW : Measure ℝ) [IsFiniteMeasure μW]
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    Tendsto (fun β =>
      (β - (∫ w, success n (pStar n (t β) w) ∂μW)) /
        (∫ w, pStar n (t β) w ^ 2 ∂μW))
      (𝓝[>] 0) (𝓝 ((n : ℝ) * (n - 1) / 2)) := by
  have ht := tendsto_nhdsWithin_iff.1 (tendsto_root_endpoint μW hn hM hle hend hβ₀ hcap)
  have hp := tendsto_pStar_at_endpoint hn hM ht.1
  have hlow : Tendsto (fun β => (n : ℝ) * (n - 1) / 2 -
      ((n : ℝ) * (n - 1) * (n - 2) / 6) * pStar n (t β) M)
      (𝓝[>] 0) (𝓝 ((n : ℝ) * (n - 1) / 2)) := by
    simpa using tendsto_const_nhds.sub (hp.const_mul ((n : ℝ) * (n - 1) * (n - 2) / 6))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals
    filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
    have htβ := (hcap β hβ).1
    have htM := root_lt_endpoint μW hn hle hβ.1 htβ (hcap β hβ).2
    have hI2 := integral_pStar_pow_pos μW hn hend htβ htM 2
    have hbounds := coverage_loss_bounds μW hn htβ hle
    have hn0 := nat_cast_pos hn
    rw [(hcap β hβ).2, mul_div_cancel₀ _ hn0.ne'] at hbounds
  · exact (le_div_iff₀ hI2).mpr hbounds.1
  · exact (div_le_iff₀ hI2).mpr hbounds.2

theorem tendsto_multiplicity_excess_div_moment_ratio
    (μW : Measure ℝ) [IsFiniteMeasure μW]
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M) (hle : ∀ᵐ w ∂μW, w ≤ M)
    (hend : ∀ u > 0, 0 < μW (Ioi (M - u))) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μW = β / n) :
    Tendsto (fun β =>
      (β / (∫ w, success n (pStar n (t β) w) ∂μW) - 1) /
        ((∫ w, pStar n (t β) w ^ 2 ∂μW) / (∫ w, pStar n (t β) w ∂μW)))
      (𝓝[>] 0) (𝓝 (((n : ℝ) - 1) / 2)) := by
  have hD := tendsto_coverage_loss_div_second_moment μW hn hM hle hend hβ₀ hcap
  have hμ := tendsto_multiplicity_one μW hn hM hle hend hβ₀ hcap
  have hn0 := nat_cast_pos hn
  have hlim := (hD.mul hμ).div_const (n : ℝ)
  have hc : ((n : ℝ) * (n - 1) / 2 * 1) / n = ((n : ℝ) - 1) / 2 := by
    field_simp
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀, hμ.eventually (lt_mem_nhds zero_lt_one)] with β hβ hμne
  have htβ := (hcap β hβ).1
  have htM := root_lt_endpoint μW hn hle hβ.1 htβ (hcap β hβ).2
  have hI2 := integral_pStar_pow_pos μW hn hend htβ htM 2
  have hQ : (∫ w, success n (pStar n (t β) w) ∂μW) ≠ 0 := by
    intro h
    simp only [h, div_zero, lt_self_iff_false] at hμne
  rw [(hcap β hβ).2]
  field_simp

end FCAppendix.PayOnce.SharpEndpoint
