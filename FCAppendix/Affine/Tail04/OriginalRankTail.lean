import FCAppendix.Affine.Tail04.RankTail
import FCAppendix.Affine.Tail04.UpperOriginal

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Real Filter Topology

def paretoRankFailure (N c : ℕ) (h t v : ℝ) : ℝ :=
  1 - rankSuccess N c (h / 2 * powerTail t 10 v)

def rankTailConstant (N c : ℕ) (h : ℝ) : ℝ :=
  (2 : ℝ) ^ N * (h / 2) ^ c

theorem paretoRankFailure_measurable (N c : ℕ) (h t : ℝ) :
    Measurable (paretoRankFailure N c h t) := by
  unfold paretoRankFailure rankSuccess Bayes.binomBelow PiBinomial.pmf powerTail
  fun_prop

theorem paretoRankFailure_bounds (N c : ℕ) (h t v : ℝ)
    (hc : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hv : t ≤ v) :
    0 ≤ paretoRankFailure N c h t v ∧
    paretoRankFailure N c h t v ≤ rankTailConstant N c h * powerTail t (10 * c) v := by
  have hv0 : 0 < v := ht.trans_le hv
  have hratio : 1 ≤ v / t := (le_div_iff₀ ht).2 (by simpa using hv)
  have hpow0 := powerTail_nonneg t 10 v ht hv0.le
  have hpow1 : powerTail t 10 v ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hratio (by norm_num)
  have hp : h / 2 * powerTail t 10 v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hh.1]) hpow0
    · nlinarith [hh.1, hh.2]
  refine ⟨?_, rank_failure_pareto N c h t v hc hh ht hv⟩
  have hq := (rankSuccess_bounds N c _ hc hp).2
  dsimp [paretoRankFailure]
  linarith

theorem pareto_rank_failure_integrals (N c : ℕ) (h t : ℝ)
    (hc0 : 1 ≤ c) (hcN : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) :
    IntegrableOn (paretoRankFailure N c h t) (Ioi t) ∧
    IntegrableOn (fun v => v * paretoRankFailure N c h t v) (Ioi t) ∧
    (∫ v in Ioi t, paretoRankFailure N c h t v) ≤
      rankTailConstant N c h * t / (10 * (c : ℝ) - 1) ∧
    (∫ v in Ioi t, v * paretoRankFailure N c h t v) ≤
      rankTailConstant N c h * t ^ 2 / (10 * (c : ℝ) - 2) := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc0
  apply failure_integrals (paretoRankFailure N c h t)
    (rankTailConstant N c h) t (10 * (c : ℝ)) ht (by linarith)
  · exact mul_nonneg (by positivity) (pow_nonneg (by linarith [hh.1]) _)
  · exact (paretoRankFailure_measurable N c h t).aestronglyMeasurable
  · intro v hv
    exact paretoRankFailure_bounds N c h t v hcN hh ht hv.le

def paretoEnvelopeError (N c : ℕ) (h t R : ℝ) : ℝ :=
  (t - R) * paretoRankFailure N c h t t +
    ∫ v in Ioi t, paretoRankFailure N c h t v

theorem pareto_envelope_error_bound (N c : ℕ) (h t R : ℝ)
    (hc0 : 1 ≤ c) (hcN : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hR0 : 0 ≤ R) (hRt : R ≤ t) :
    0 ≤ paretoEnvelopeError N c h t R ∧
    paretoEnvelopeError N c h t R ≤ 2 * t * rankTailConstant N c h := by
  obtain ⟨_hi, _hwi, hiBound, _hwBound⟩ :=
    pareto_rank_failure_integrals N c h t hc0 hcN hh ht
  have hfloor := paretoRankFailure_bounds N c h t t hcN hh ht le_rfl
  rw [powerTail_at_floor t (10 * (c : ℝ)) ht.ne', mul_one] at hfloor
  have hD : 0 ≤ rankTailConstant N c h :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith [hh.1]) _)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc0
  have hden : 1 ≤ 10 * (c : ℝ) - 1 := by linarith
  have hIntegralNonneg : 0 ≤ ∫ v in Ioi t, paretoRankFailure N c h t v := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (paretoRankFailure_bounds N c h t v hcN hh ht hv.le).1
  have hfirst : (t - R) * paretoRankFailure N c h t t ≤ t * rankTailConstant N c h := by
    exact (mul_le_mul_of_nonneg_left hfloor.2 (sub_nonneg.mpr hRt)).trans
      (mul_le_mul_of_nonneg_right (by linarith : t - R ≤ t) hD)
  have hint : (∫ v in Ioi t, paretoRankFailure N c h t v) ≤
      t * rankTailConstant N c h := by
    apply hiBound.trans
    apply (div_le_iff₀ (by linarith : 0 < 10 * (c : ℝ) - 1)).2
    have h := mul_le_mul_of_nonneg_left hden (mul_nonneg hD ht.le)
    nlinarith
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hRt) hfloor.1) hIntegralNonneg
  · dsimp [paretoEnvelopeError]
    nlinarith

theorem powerTail_ten (t v : ℝ) (ht : 0 < t) (hv : 0 < v) :
    powerTail t 10 v = (t / v) ^ 10 := by
  have hratio : 0 < v / t := div_pos hv ht
  dsimp [powerTail]
  rw [Real.rpow_neg hratio.le]
  rw [show (v/t)^(10:ℝ)=(v/t)^(10:ℕ) from Real.rpow_natCast (v/t) 10]
  rw [←inv_pow,inv_div]

theorem rankSuccess_eq_canonical (N c : ℕ) (p : ℝ)
    (hc : c ≤ N + 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    rankSuccess N c p = Existence.RankEnvelope.rankSuccess N c p := by
  rw [rankSuccess, Existence.RankEnvelope.rankSuccess_eq_prob N c hp,
    Bayes.binomBelow_eq_prob N c hc p hp.1 hp.2]

theorem original_rank_failure_eq_pareto
    (mu : Measure ℝ) (N c : ℕ) (h t v : ℝ)
    (hc : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hv : t ≤ v)
    (hrelative : mu.real (Ioi v) = h * powerTail t 10 v) :
    1 - Existence.RankEnvelope.rank mu N c 2 v =
      paretoRankFailure N c h t v := by
  have hv0 : 0 < v := ht.trans_le hv
  have hp0 := powerTail_nonneg t 10 v ht hv0.le
  have hp1 : powerTail t 10 v ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      ((le_div_iff₀ ht).2 (by simpa using hv)) (by norm_num)
  have hp : h / 2 * powerTail t 10 v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hh.1]) hp0
    · nlinarith [hh.1, hh.2]
  have he : mu.real (Ioi v) / (2 : ℝ) = h / 2 * powerTail t 10 v := by
    rw [hrelative]
    ring
  unfold Existence.RankEnvelope.rank Existence.RankEnvelope.contactTail
  norm_num only [Nat.cast_ofNat]
  rw [he, ← rankSuccess_eq_canonical N c _ hc hp]
  rfl

theorem original_pareto_rank_integrals
    (mu : Measure ℝ) (N c : ℕ) (h t : ℝ)
    (hc0 : 1 ≤ c) (hcN : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t)
    (hrelative : ∀ v, t ≤ v → mu.real (Ioi v) = h * powerTail t 10 v) :
    IntegrableOn (fun v => 1 - Existence.RankEnvelope.rank mu N c 2 v) (Ioi t) ∧
    IntegrableOn (fun v => v * (1 - Existence.RankEnvelope.rank mu N c 2 v)) (Ioi t) ∧
    (∫ v in Ioi t, 1 - Existence.RankEnvelope.rank mu N c 2 v) ≤
      rankTailConstant N c h * t / (10 * (c : ℝ) - 1) ∧
    (∫ v in Ioi t, v * (1 - Existence.RankEnvelope.rank mu N c 2 v)) ≤
      rankTailConstant N c h * t ^ 2 / (10 * (c : ℝ) - 2) := by
  obtain ⟨hi, hwi, hib, hwib⟩ := pareto_rank_failure_integrals N c h t hc0 hcN hh ht
  have he : (fun v => 1 - Existence.RankEnvelope.rank mu N c 2 v)
      =ᵐ[volume.restrict (Ioi t)] paretoRankFailure N c h t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact original_rank_failure_eq_pareto mu N c h t v hcN hh ht hv.le (hrelative v hv.le)
  have hwe : (fun v => v * (1 - Existence.RankEnvelope.rank mu N c 2 v))
      =ᵐ[volume.restrict (Ioi t)] (fun v => v * paretoRankFailure N c h t v) := by
    filter_upwards [he] with v hv
    rw [hv]
  refine ⟨hi.congr he.symm, hwi.congr hwe.symm, ?_, ?_⟩
  · rw [integral_congr_ae he]
    exact hib
  · rw [integral_congr_ae hwe]
    exact hwib

theorem original_pareto_upper_envelope
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (m c : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (hmass : mu.real univ ≤ 1)
    (h t R : ℝ) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hrelative : ∀ v, t ≤ v → mu.real (Ioi v) = h * powerTail t 10 v) :
    Existence.RankEnvelope.UpperEnvelopeProperties mu (m - 2) c
      (Existence.RankEnvelope.rank mu (m - 1) c 2)
      (Existence.RankEnvelope.bid (Existence.RankEnvelope.rank mu (m - 1) c 2) t R)
      (Existence.RankEnvelope.utility (Existence.RankEnvelope.rank mu (m - 1) c 2) t R)
      t R (Existence.RankEnvelope.error (Existence.RankEnvelope.rank mu (m - 1) c 2) t R) := by
  have he : m - 2 + 1 = m - 1 := by omega
  have hi := (original_pareto_rank_integrals mu (m - 1) c h t hc (by omega)
    hh ht hrelative).1
  have hh' := Existence.RankEnvelope.upper_envelope mu (m - 2) c hc (by omega)
    hmass t R hR hRt hsupport
    (by simpa only [he] using hi)
  simpa only [he] using hh'

theorem original_pareto_error_bound
    (mu : Measure ℝ) (N c : ℕ) (h t R : ℝ)
    (hc0 : 1 ≤ c) (hcN : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hR : 0 ≤ R) (hRt : R ≤ t)
    (hrelative : ∀ v, t ≤ v → mu.real (Ioi v) = h * powerTail t 10 v) :
    0 ≤ Existence.RankEnvelope.error (Existence.RankEnvelope.rank mu N c 2) t R ∧
    Existence.RankEnvelope.error (Existence.RankEnvelope.rank mu N c 2) t R ≤
      2 * t * rankTailConstant N c h := by
  have he : (fun v => 1 - Existence.RankEnvelope.rank mu N c 2 v)
      =ᵐ[volume.restrict (Ioi t)] paretoRankFailure N c h t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact original_rank_failure_eq_pareto mu N c h t v hcN hh ht hv.le (hrelative v hv.le)
  have hfloor := original_rank_failure_eq_pareto mu N c h t t hcN hh ht le_rfl
    (hrelative t le_rfl)
  have herr : Existence.RankEnvelope.error (Existence.RankEnvelope.rank mu N c 2) t R =
      paretoEnvelopeError N c h t R := by
    unfold Existence.RankEnvelope.error paretoEnvelopeError
    rw [hfloor, integral_congr_ae he]
  rw [herr]
  exact pareto_envelope_error_bound N c h t R hc0 hcN hh ht hR hRt

end FCAppendix.Affine.Tail04
