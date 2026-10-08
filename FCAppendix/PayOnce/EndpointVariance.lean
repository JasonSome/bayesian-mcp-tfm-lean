import FCAppendix.PayOnce.EndpointRates
import Mathlib.Probability.Moments.Variance

namespace FCAppendix.PayOnce.EndpointVariance

open MeasureTheory Filter Topology Set ManyProposers BoundedEndpoint SharpEndpoint EndpointMoments EndpointRates
open scoped BigOperators

theorem deriv_H_zero {n : ℕ} (hn : 0 < n) : deriv (H n) 0 = -((n : ℝ) - 1) / 2 := by
  have hsum : HasDerivAt (fun p : ℝ => ∑ j ∈ Finset.range n, (1 - p) ^ j)
      (∑ j ∈ Finset.range n, -(j : ℝ)) 0 := by
    have hterms : ∀ j ∈ Finset.range n, HasDerivAt (fun p : ℝ => (1 - p) ^ j) (-(j : ℝ)) 0 := by
      intro j _
      convert ((hasDerivAt_id (0 : ℝ)).const_sub 1).pow j using 1 <;> first | rfl | simp
    exact HasDerivAt.fun_sum hterms
  have hh := (hsum.div_const (n : ℝ)).deriv
  change deriv (H n) 0 = _ at hh
  rw [hh, Finset.sum_neg_distrib]
  have hsumR (m : ℕ) : (∑ j ∈ Finset.range m, (j : ℝ)) = (m : ℝ) * (m - 1) / 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [hsumR]
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

theorem continuous_deriv_H (n : ℕ) : Continuous (deriv (H n)) := by
  have hh : ContDiff ℝ 1 (H n) := by unfold H; fun_prop
  exact hh.continuous_deriv le_rfl

theorem tendsto_mean_sq_div_second_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => (∫ w, pStar n (M - d) w ∂μ) ^ 2 /
      (∫ w, pStar n (M - d) w ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
  have h₁ := tendsto_first_moment μ hn hM hγ hc hle htail
  have h₂ := tendsto_second_moment μ hn hM hγ hc hle htail
  have ha := nat_sub_one_pos hn
  have hC : 0 < 2 * c / ((γ + 1) * (γ + 2) * (M * ((n : ℝ) - 1)) ^ 2) :=
    div_pos (by positivity) (mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos (mul_pos hM ha)))
  have hd : Tendsto (fun d : ℝ => d ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have hh := (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0)).rpow_const (Or.inr hγ.le)
    simpa only [id_eq, Real.zero_rpow hγ.ne'] using hh
  have hh := ((h₁.pow 2).div h₂ hC.ne').mul hd
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hd' : 0 < d := hd
  have hdγ : d ^ γ ≠ 0 := (Real.rpow_pos_of_pos hd' γ).ne'
  dsimp only [Pi.div_apply]
  rw [Real.rpow_add hd', Real.rpow_add hd', Real.rpow_one, Real.rpow_two]
  field_simp

theorem tendsto_variance_div_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => ProbabilityTheory.variance (pStar n (M - d)) μ /
      (∫ w, pStar n (M - d) w ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 1) := by
  have hh := (tendsto_mean_sq_div_second_moment μ hn hM hγ hc hle htail).const_sub 1
  rw [sub_zero] at hh
  have hend := endpoint_of_tail μ hc htail
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hM] with d hd
  have ht : 0 < M - d := sub_pos.mpr hd.2
  have htM : M - d < M := sub_lt_self _ hd.1
  have hI2 := integral_pStar_pow_pos μ hn hend ht htM 2
  have hLp : MemLp (pStar n (M - d)) 2 μ := memLp_of_bounded
    (Eventually.of_forall fun w => ⟨pStar_nonneg n (M - d) w, pStar_le_one n ht.le w⟩)
    (continuous_pStar hn ht).aestronglyMeasurable 2
  rw [ProbabilityTheory.variance_eq_sub hLp]
  simp only [Pi.pow_apply]
  field_simp

theorem tendsto_active_average (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M)
    (hle : ∀ᵐ w ∂μ, w ≤ M) (hend : ∀ u > 0, 0 < μ (Ioi (M - u)))
    {F : ℝ × ℝ → ℝ} (hFm : Measurable F) (hF : ContinuousAt F (M, 0)) :
    Tendsto (fun d : ℝ =>
      (∫ w, (Ioi (M - d)).indicator (fun w => F (M - d, pStar n (M - d) w)) w ∂μ) /
        μ.real (Ioi (M - d))) (𝓝[>] 0) (𝓝 (F (M, 0))) := by
  have ht : Tendsto (fun d : ℝ => M - d) (𝓝[>] 0) (𝓝 M) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0)).const_sub M
  have hp := tendsto_pStar_at_endpoint hn hM ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hF (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hM,
    ht.eventually (Metric.ball_mem_nhds M hδ), hp.eventually (gt_mem_nhds hδ)] with d hd htd hpd
  have ht0 : 0 < M - d := sub_pos.mpr hd.2
  have hpoint : ∀ w ≤ M, |F (M - d, pStar n (M - d) w) - F (M, 0)| < ε / 2 := by
    intro w hw
    have hpw : dist (pStar n (M - d) w) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pStar_nonneg n (M - d) w)]
      exact (pStar_mono_value hn ht0 hw).trans_lt hpd
    have hdist : dist (M - d, pStar n (M - d) w) (M, 0) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨htd, hpw⟩
    simpa only [Real.dist_eq] using hball hdist
  let g : ℝ → ℝ := (Ioi (M - d)).indicator (fun w => F (M - d, pStar n (M - d) w))
  have hgm : AEStronglyMeasurable g μ :=
    ((hFm.comp (measurable_const.prodMk (continuous_pStar hn ht0).measurable)).indicator
      measurableSet_Ioi).aestronglyMeasurable
  have hg : Integrable g μ := by
    apply Integrable.mono' (integrable_const (|F (M, 0)| + ε / 2)) hgm
    filter_upwards [hle] with w hw
    by_cases hs : w ∈ Ioi (M - d)
    · dsimp [g]
      rw [indicator_of_mem hs]
      have hh := abs_lt.mp (hpoint w hw)
      exact abs_le.mpr ⟨by linarith [neg_abs_le (F (M, 0))], by linarith [le_abs_self (F (M, 0))]⟩
    · simp only [g, indicator_of_notMem hs, norm_zero]
      positivity
  have hlo : ∀ᵐ w ∂μ, (Ioi (M - d)).indicator (fun _ => F (M, 0) - ε / 2) w ≤ g w := by
    filter_upwards [hle] with w hw
    by_cases hs : w ∈ Ioi (M - d)
    · simp only [g, indicator_of_mem hs]
      linarith [(abs_lt.mp (hpoint w hw)).1]
    · simp [g, indicator_of_notMem hs]
  have hup : ∀ᵐ w ∂μ, g w ≤ (Ioi (M - d)).indicator (fun _ => F (M, 0) + ε / 2) w := by
    filter_upwards [hle] with w hw
    by_cases hs : w ∈ Ioi (M - d)
    · simp only [g, indicator_of_mem hs]
      linarith [(abs_lt.mp (hpoint w hw)).2]
    · simp [g, indicator_of_notMem hs]
  have hlo' := integral_mono_ae ((integrable_const _).indicator measurableSet_Ioi) hg hlo
  have hup' := integral_mono_ae hg ((integrable_const _).indicator measurableSet_Ioi) hup
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hlo' hup'
  have hT : 0 < μ.real (Ioi (M - d)) :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm ((measureReal_ne_zero_iff).mpr (hend d hd.1).ne'))
  have hlow : F (M, 0) - ε / 2 ≤ (∫ w, g w ∂μ) / μ.real (Ioi (M - d)) :=
    (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hlo')
  have hupp : (∫ w, g w ∂μ) / μ.real (Ioi (M - d)) ≤ F (M, 0) + ε / 2 :=
    (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using hup')
  rw [Real.dist_eq, abs_lt]
  change -(ε) < (∫ w, g w ∂μ) / μ.real (Ioi (M - d)) - F (M, 0) ∧ _
  constructor <;> linarith

noncomputable def limitBid (n : ℕ) (t w : ℝ) : ℝ := t / H n (pStar n t w)

noncomputable def priceWeight (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  H n x.2 / (x.1 * (-deriv (H n) x.2))

noncomputable def priceSlope (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ w, (Ioi t).indicator (fun w => priceWeight n (t, pStar n t w)) w ∂μ

theorem priceSlope_eq_source (μ : Measure ℝ) (n : ℕ) (t : ℝ) :
    priceSlope μ n t = ∫ w, (Ioi t).indicator
      (fun w => 1 / (limitBid n t w * (-deriv (H n) (pStar n t w)))) w ∂μ := by
  unfold priceSlope
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  by_cases hw : w ∈ Ioi t
  · rw [indicator_of_mem hw, indicator_of_mem hw]
    simp only [priceWeight, limitBid, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
    ring
  · rw [indicator_of_notMem hw, indicator_of_notMem hw]

theorem measurable_priceWeight (n : ℕ) : Measurable (priceWeight n) := by
  have hH := (continuous_H n).measurable
  have hD := (continuous_deriv_H n).measurable
  exact (hH.comp measurable_snd).div (measurable_fst.mul (hD.comp measurable_snd).neg)

theorem continuousAt_priceWeight {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M) :
    ContinuousAt (priceWeight n) (M, 0) := by
  have hn0 : 0 < n := by omega
  have ha := nat_sub_one_pos hn
  have hH : ContinuousAt (fun x : ℝ × ℝ => H n x.2) (M, 0) :=
    (continuous_H n).continuousAt.comp continuousAt_snd
  have hD : ContinuousAt (fun x : ℝ × ℝ => deriv (H n) x.2) (M, 0) :=
    (continuous_deriv_H n).continuousAt.comp continuousAt_snd
  apply hH.div (continuousAt_fst.mul hD.neg)
  change M * (-deriv (H n) 0) ≠ 0
  rw [deriv_H_zero hn0]
  have : 0 < -(-((n : ℝ) - 1) / 2) := by linarith
  exact (mul_pos hM this).ne'

theorem priceWeight_endpoint {n : ℕ} (hn : 2 ≤ n) (M : ℝ) :
    priceWeight n (M, 0) = 2 / (M * ((n : ℝ) - 1)) := by
  have hn0 : 0 < n := by omega
  rw [priceWeight, H_zero n hn0, deriv_H_zero hn0]
  have he : M * -(-((n : ℝ) - 1) / 2) = (M * ((n : ℝ) - 1)) / 2 := by ring
  rw [he, one_div_div]

theorem tendsto_priceSlope_div_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M : ℝ} (hM : 0 < M) (hle : ∀ᵐ w ∂μ, w ≤ M)
    (hend : ∀ u > 0, 0 < μ (Ioi (M - u))) :
    Tendsto (fun d : ℝ => priceSlope μ n (M - d) / μ.real (Ioi (M - d)))
      (𝓝[>] 0) (𝓝 (2 / (M * ((n : ℝ) - 1)))) := by
  have hh := tendsto_active_average μ hn hM hle hend (measurable_priceWeight n)
    (continuousAt_priceWeight hn hM)
  rwa [priceWeight_endpoint hn] at hh

theorem tendsto_priceSlope_div_gap_rpow (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => priceSlope μ n (M - d) / d ^ γ) (𝓝[>] 0)
      (𝓝 (2 * c / (M * ((n : ℝ) - 1)))) := by
  have hend := endpoint_of_tail μ hc htail
  have hh := (tendsto_priceSlope_div_tail μ hn hM hle hend).mul htail
  rw [div_mul_eq_mul_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hT : μ.real (Ioi (M - d)) ≠ 0 := (measureReal_ne_zero_iff).mpr (hend d hd).ne'
  field_simp

noncomputable def sigmaSq (μ : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ProbabilityTheory.variance (pStar n t) μ / priceSlope μ n t ^ 2

theorem tendsto_sigmaSq_div_gap_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun d : ℝ => sigmaSq μ n (M - d) / d ^ (2 - γ)) (𝓝[>] 0)
      (𝓝 (1 / (2 * c * (γ + 1) * (γ + 2)))) := by
  have hv := tendsto_variance_div_second_moment μ hn hM hγ hc hle htail
  have h₂ := tendsto_second_moment μ hn hM hγ hc hle htail
  have hA := tendsto_priceSlope_div_gap_rpow μ hn hM hc hle htail
  have ha := nat_sub_one_pos hn
  have hAc : 0 < 2 * c / (M * ((n : ℝ) - 1)) := div_pos (by positivity) (mul_pos hM ha)
  have hh := (hv.mul h₂).div (hA.pow 2) (pow_ne_zero 2 hAc.ne')
  have he : 1 * (2 * c / ((γ + 1) * (γ + 2) * (M * ((n : ℝ) - 1)) ^ 2)) /
      (2 * c / (M * ((n : ℝ) - 1))) ^ 2 = 1 / (2 * c * (γ + 1) * (γ + 2)) := by
    field_simp
  rw [he] at hh
  have hend := endpoint_of_tail μ hc htail
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hM] with d hd
  have ht := sub_pos.mpr hd.2
  have hI2 := integral_pStar_pow_pos μ hn hend ht (sub_lt_self M hd.1) 2
  have hdγ := (Real.rpow_pos_of_pos hd.1 γ).ne'
  have hpow : d ^ (γ + 2) = d ^ (2 - γ) * (d ^ γ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hd.1.le, ← Real.rpow_add hd.1]
    congr 1
    norm_num
    ring
  change (ProbabilityTheory.variance (pStar n (M - d)) μ /
    (∫ w, pStar n (M - d) w ^ 2 ∂μ) *
      ((∫ w, pStar n (M - d) w ^ 2 ∂μ) / d ^ (γ + 2))) /
      (priceSlope μ n (M - d) / d ^ γ) ^ 2 = _
  rw [hpow]
  unfold sigmaSq
  field_simp

theorem tendsto_sigmaSq_div_comparisonGap_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {M γ c : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hc : 0 < c)
    (hle : ∀ᵐ w ∂μ, w ≤ M)
    (htail : Tendsto (fun u : ℝ => μ.real (Ioi (M - u)) / u ^ γ) (𝓝[>] 0) (𝓝 c))
    {β₀ : ℝ} (hβ₀ : 0 < β₀) {t : ℝ → ℝ}
    (hcap : ∀ β ∈ Ioo 0 β₀, 0 < t β ∧ ∫ w, pStar n (t β) w ∂μ = β / n) :
    Tendsto (fun β : ℝ => sigmaSq μ n (t β) / (comparisonGap n M γ c β) ^ (2 - γ))
      (𝓝[>] 0) (𝓝 (1 / (2 * c * (γ + 1) * (γ + 2)))) := by
  have hd := tendsto_capacity_gap μ hn hM hc hle htail hβ₀ hcap
  have hs := (tendsto_sigmaSq_div_gap_rpow μ hn hM hγ hc hle htail).comp hd
  simp only [Function.comp_def, sub_sub_cancel] at hs
  have hr := (tendsto_gap_div_comparisonGap μ hn hM hγ hc hle htail hβ₀ hcap).rpow_const
    (p := 2 - γ) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hr
  have hh := hs.mul hr
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT hβ₀] with β hβ
  have hgap : 0 < M - t β := sub_pos.mpr
    (root_lt_endpoint μ hn hle hβ.1 (hcap β hβ).1 (hcap β hβ).2)
  have hcomp : 0 < comparisonGap n M γ c β := by
    unfold comparisonGap
    apply Real.rpow_pos_of_pos
    exact div_pos (mul_pos (mul_pos (by linarith) (mul_pos hM (nat_sub_one_pos hn))) hβ.1)
      (mul_pos (nat_cast_pos hn) hc)
  have hgap' := (Real.rpow_pos_of_pos hgap (2 - γ)).ne'
  rw [Real.div_rpow hgap.le hcomp.le]
  field_simp

end FCAppendix.PayOnce.EndpointVariance
