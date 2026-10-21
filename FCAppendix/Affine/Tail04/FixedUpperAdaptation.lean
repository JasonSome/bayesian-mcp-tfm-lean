import FCAppendix.Affine.Tail04.OriginalRankTail
import FCAppendix.Affine.Hybrid.UpperFiniteError

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem powerTail_double_threshold (M v : ℝ) (hM : 0 < M) (hv : 0 < v) :
    powerTail M 10 v = (1 / 1024 : ℝ) * powerTail (2 * M) 10 v := by
  rw [powerTail_ten M v hM hv, powerTail_ten (2 * M) v (by positivity) hv,
    div_pow, div_pow, mul_pow]
  norm_num
  ring

theorem original_relative_tail_at_double
    (mu : Measure ℝ) (M hTail : ℝ) (hM : 0 < M)
    (hrelative : ∀ v, M ≤ v → mu.real (Ioi v) = hTail * powerTail M 10 v) :
    ∀ v, 2 * M ≤ v →
      mu.real (Ioi v) = (hTail / 1024) * powerTail (2 * M) 10 v := by
  intro v hv
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity : 0 < 2 * M) hv
  rw [hrelative v (by linarith), powerTail_double_threshold M v hM hv0]
  ring

theorem original_contactTail_le_seven_twentieths
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmass : mu.real univ ≤ 7 / 10) (v : ℝ) :
    Existence.RankEnvelope.contactTail mu 2 v ∈ Icc (0 : ℝ) (7 / 20) := by
  have hm : mu.real (Ioi v) ≤ 7 / 10 :=
    (measureReal_mono (subset_univ _)).trans hmass
  unfold Existence.RankEnvelope.contactTail
  norm_num only [Nat.cast_ofNat]
  constructor
  · exact div_nonneg measureReal_nonneg (by norm_num)
  · linarith

theorem original_fixed_rank_failure
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmass : mu.real univ ≤ 7 / 10)
    (m : ℕ) (hm : 200 ≤ m) (v : ℝ) :
    0 ≤ 1 - Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2 v ∧
    1 - Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2 v ≤
      Real.exp (-lowerRankRate * m) := by
  have hp := original_contactTail_le_seven_twentieths mu hmass v
  have hc : marketCapacity m ≤ m - 1 + 1 := by
    have hh := (capacity_bounds m hm).2.2.2
    omega
  have hq := rankSuccess_bounds (m - 1) (marketCapacity m)
    (Existence.RankEnvelope.contactTail mu 2 v) hc ⟨hp.1, by linarith [hp.2]⟩
  have he := rankSuccess_eq_canonical (m - 1) (marketCapacity m)
    (Existence.RankEnvelope.contactTail mu 2 v) hc ⟨hp.1, by linarith [hp.2]⟩
  have hb := rank_failure_fixed_gap m hm
    (Existence.RankEnvelope.contactTail mu 2 v) hp.1 hp.2
  rw [he] at hq hb
  change 0 ≤ 1-Existence.RankEnvelope.rankSuccess (m-1) (marketCapacity m)
    (Existence.RankEnvelope.contactTail mu 2 v) ∧ _
  exact ⟨by linarith [hq.2], hb⟩

theorem doubled_tail_constant_exponential
    (hTail : ℝ) (hh : hTail ∈ Icc (0 : ℝ) 1)
    (m : ℕ) (hm : 200 ≤ m) :
    rankTailConstant (m - 1) (marketCapacity m) (hTail / 1024) ≤
      Real.exp (-Real.log 2 * m) := by
  have hclo := (capacity_bounds m hm).1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcn : 2 * m ≤ 11 * marketCapacity m := by
    have hh' : (2 : ℝ) * m ≤ 11 * (marketCapacity m : ℝ) := by linarith
    exact_mod_cast hh'
  have hp0 : 0 ≤ hTail / 1024 / 2 := by
    exact div_nonneg (div_nonneg hh.1 (by norm_num)) (by norm_num)
  have hp : hTail / 1024 / 2 ≤ (1 / 2 : ℝ) ^ 11 := by
    norm_num
    linarith [hh.2]
  calc
    rankTailConstant (m - 1) (marketCapacity m) (hTail / 1024)
        ≤ (2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ 11) ^ marketCapacity m := by
      unfold rankTailConstant
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      · exact pow_le_pow_left₀ hp0 hp _
      · exact pow_nonneg hp0 _
      · positivity
    _ = (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (11 * marketCapacity m) := by rw [pow_mul]
    _ ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (2 * m) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hcn) (by positivity)
    _ = (1 / 2 : ℝ) ^ m := by
      rw [pow_mul, ← mul_pow]
      norm_num
    _ = Real.exp (-Real.log 2 * m) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      simp only [one_div]

theorem envelope_error_split
    (q : ℝ → ℝ) (hq : Monotone q) (hcont : Continuous q)
    (t R H : ℝ) (htH : t ≤ H)
    (hint : IntegrableOn (fun x => 1 - q x) (Ioi H)) :
    IntegrableOn (fun x => 1 - q x) (Ioi t) ∧
    Existence.RankEnvelope.error q t R ≤
      (H - R) * (1 - q t) + ∫ x in Ioi H, (1 - q x) := by
  have hf : Continuous (fun x => 1 - q x) := continuous_const.sub hcont
  have hpref : IntegrableOn (fun x => 1 - q x) (Ioc t H) :=
    (hf.integrableOn_Icc (μ := volume) (a := t) (b := H)).mono_set Ioc_subset_Icc_self
  have hset : Ioc t H ∪ Ioi H = Ioi t := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact htH.trans_lt hx
    · intro hx
      by_cases hxH : x ≤ H
      · exact Or.inl ⟨hx, hxH⟩
      · exact Or.inr (lt_of_not_ge hxH)
  have hfull : IntegrableOn (fun x => 1 - q x) (Ioi t) := by
    rw [← hset]
    exact hpref.union hint
  have he := intervalIntegral.integral_interval_add_Ioi'
    (hf.intervalIntegrable (μ := volume) (a := t) (b := H)) hint
  have hb := (Existence.RankEnvelope.integral_bounds hq htH).1
  have hsplit : (∫ x in t..H, 1 - q x) = (H - t) - ∫ x in t..H, q x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hcont.intervalIntegrable (μ := volume) (a := t) (b := H)),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
  refine ⟨hfull, ?_⟩
  unfold Existence.RankEnvelope.error
  rw [← he, hsplit]
  nlinarith

theorem original_fixed_upper_integrable_error
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ ≤ 7 / 10)
    (t R M hTail : ℝ) (ht : 0 < t) (hRt : R ≤ t) (htM : t ≤ M)
    (hh : hTail ∈ Icc (0 : ℝ) 1)
    (hrelative : ∀ v, M ≤ v → mu.real (Ioi v) = hTail * powerTail M 10 v)
    (m : ℕ) (hm : 200 ≤ m) :
    IntegrableOn
      (fun v => 1 - Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2 v)
      (Ioi t) ∧
    0 ≤ Existence.RankEnvelope.error
      (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R ∧
    Existence.RankEnvelope.error
      (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R ≤
      (2 * M - R) * Real.exp (-lowerRankRate * m) +
        2 * M * Real.exp (-Real.log 2 * m) := by
  have hM : 0 < M := ht.trans_le htM
  obtain ⟨hclo, hchi, hc, hcm⟩ := capacity_bounds m hm
  have hcc : marketCapacity m ≤ m - 1 + 1 := by omega
  have he : m - 2 + 1 = m - 1 := by omega
  have hmass1 : mu.real univ ≤ 1 := hmass.trans (by norm_num)
  have hqmono : Monotone (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) := by
    simpa only [he] using
      (Existence.RankEnvelope.rank_monotone mu (r := m - 2) hc
        (by omega) (by norm_num) hmass1)
  have hqcont := Existence.RankEnvelope.continuous_rank mu (m - 1) (marketCapacity m) 2
  have hrel := original_relative_tail_at_double mu M hTail hM hrelative
  have hhh : hTail / 1024 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hh.1 (by norm_num)
    · linarith [hh.2]
  obtain ⟨htail, hwtail, htailBound, hwtailBound⟩ :=
    original_pareto_rank_integrals mu (m - 1) (marketCapacity m)
      (hTail / 1024) (2 * M) hc hcc hhh (by positivity) hrel
  have hs := envelope_error_split
    (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2)
    hqmono hqcont t R (2 * M) (by linarith) htail
  have hfloor := (original_fixed_rank_failure mu hmass m hm t).2
  have hD := doubled_tail_constant_exponential hTail hh m hm
  have hc1 : (1 : ℝ) ≤ marketCapacity m := by exact_mod_cast hc
  have hden : 1 ≤ 10 * (marketCapacity m : ℝ) - 1 := by linarith
  have htailFinal :
      (∫ v in Ioi (2 * M),
        1 - Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2 v) ≤
      2 * M * Real.exp (-Real.log 2 * m) := by
    apply htailBound.trans
    apply (div_le_iff₀ (by linarith : 0 < 10 * (marketCapacity m : ℝ) - 1)).2
    have hh' := mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ 2 * M)
    have hh'' := mul_le_mul_of_nonneg_left hden
      (by positivity : 0 ≤ 2 * M * Real.exp (-Real.log 2 * m))
    nlinarith
  refine ⟨hs.1, Existence.RankEnvelope.error_nonneg hRt
    (fun v => (Existence.RankEnvelope.rank_bounds mu _ _ (by norm_num) hmass1 v).2), ?_⟩
  have hfirst := mul_le_mul_of_nonneg_left hfloor (by linarith : 0 ≤ 2 * M - R)
  linarith [hs.2]

theorem original_fixed_upper_envelope
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ ≤ 7 / 10)
    (t R M hTail : ℝ) (hR : 0 < R) (hRt : R < t) (htM : t ≤ M)
    (hh : hTail ∈ Icc (0 : ℝ) 1)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hrelative : ∀ v, M ≤ v → mu.real (Ioi v) = hTail * powerTail M 10 v)
    (m : ℕ) (hm : 200 ≤ m) :
    Existence.RankEnvelope.UpperEnvelopeProperties mu (m - 2) (marketCapacity m)
      (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2)
      (Existence.RankEnvelope.bid
        (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R)
      (Existence.RankEnvelope.utility
        (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R)
      t R (Existence.RankEnvelope.error
        (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R) := by
  obtain ⟨hclo, hchi, hc, hcm⟩ := capacity_bounds m hm
  have he : m - 2 + 1 = m - 1 := by omega
  have hi := (original_fixed_upper_integrable_error mu hmass t R M hTail
    (hR.trans hRt) hRt.le htM hh hrelative m hm).1
  have hp := Existence.RankEnvelope.upper_envelope mu (m - 2) (marketCapacity m)
    hc (by omega) (hmass.trans (by norm_num)) t R hR hRt hsupport
    (by simpa only [he] using hi)
  simpa only [he] using hp

private theorem exp_rate_tendsto_zero (d : ℝ) (hd : 0 < d) :
    Tendsto (fun m : ℕ => Real.exp (-d * m)) atTop (𝓝 0) := by
  have ha : Tendsto (fun m : ℕ => d*(m:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).const_mul_atTop hd
  simpa only [neg_mul,Function.comp_def] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ha

theorem original_fixed_rank_tendsto_one
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmass : mu.real univ ≤ 7 / 10) (v : ℝ) :
    Tendsto (fun m : ℕ => Existence.RankEnvelope.rank mu
      (m - 1) (marketCapacity m) 2 v) atTop (𝓝 1) := by
  have hD : Tendsto (fun m : ℕ => 1 - Existence.RankEnvelope.rank mu
      (m - 1) (marketCapacity m) 2 v) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (exp_rate_tendsto_zero lowerRankRate lowerRankRate_pos)
    · filter_upwards [eventually_ge_atTop (200 : ℕ)] with m hm
      exact (original_fixed_rank_failure mu hmass m hm v).1
    · filter_upwards [eventually_ge_atTop (200 : ℕ)] with m hm
      exact (original_fixed_rank_failure mu hmass m hm v).2
  simpa only [sub_zero, sub_sub_cancel] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hD

theorem original_fixed_error_tendsto_zero
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ ≤ 7 / 10)
    (t R M hTail : ℝ) (ht : 0 < t) (hRt : R ≤ t) (htM : t ≤ M)
    (hh : hTail ∈ Icc (0 : ℝ) 1)
    (hrelative : ∀ v, M ≤ v → mu.real (Ioi v) = hTail * powerTail M 10 v) :
    Tendsto (fun m : ℕ => Existence.RankEnvelope.error
      (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R)
      atTop (𝓝 0) := by
  have hb : Tendsto (fun m : ℕ =>
      (2 * M - R) * Real.exp (-lowerRankRate * m) +
        2 * M * Real.exp (-Real.log 2 * m)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((exp_rate_tendsto_zero lowerRankRate lowerRankRate_pos).const_mul (2 * M - R)).add
        ((exp_rate_tendsto_zero (Real.log 2) (Real.log_pos (by norm_num))).const_mul (2 * M))
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop (200 : ℕ)] with m hm
    exact (original_fixed_upper_integrable_error mu hmass t R M hTail
      ht hRt htM hh hrelative m hm).2.1
  · filter_upwards [eventually_ge_atTop (200 : ℕ)] with m hm
    exact (original_fixed_upper_integrable_error mu hmass t R M hTail
      ht hRt htM hh hrelative m hm).2.2

theorem original_fixed_eventually_hidden_guard
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ ≤ 7 / 10)
    (eta t R M hTail : ℝ) (heta : 0 < eta) (hR : 0 < R)
    (hRt : R < t) (htM : t ≤ M) (hh : hTail ∈ Icc (0 : ℝ) 1)
    (hrelative : ∀ v, M ≤ v → mu.real (Ioi v) = hTail * powerTail M 10 v) :
    ∀ᶠ m : ℕ in atTop,
      Existence.RankEnvelope.error
        (Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2) t R <
      eta * R * (1 - 2 * (1 -
        Existence.RankEnvelope.rank mu (m - 1) (marketCapacity m) 2 t)) := by
  have he := original_fixed_error_tendsto_zero mu hmass t R M hTail
    (hR.trans hRt) hRt.le htM hh hrelative
  have hd : Tendsto (fun m : ℕ => 1 - Existence.RankEnvelope.rank mu
      (m - 1) (marketCapacity m) 2 t) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (original_fixed_rank_tendsto_one mu hmass t)
  exact Hybrid.eventually_upper_hidden_guard he hd heta hR

end FCAppendix.Affine.Tail04
