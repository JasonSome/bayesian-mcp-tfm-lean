import FCAppendix.Affine.Tail04.OriginalRankTail
import FCAppendix.Affine.Hybrid.UpperFiniteError

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology

theorem rankTailConstant_moving (K : ℝ) (m : ℕ) :
    rankTailConstant (m - 1) (marketCapacity m) (2 * K / (m : ℝ) ^ 2) =
      movingRankMajorant K m := by
  unfold rankTailConstant movingRankMajorant
  congr 2
  ring

theorem movingRankMajorant_nonneg (K : ℝ) (m : ℕ) (hK : 0 ≤ K) :
    0 ≤ movingRankMajorant K m := by
  unfold movingRankMajorant
  positivity

theorem movingRankMajorant_eventually_exp (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ m : ℕ in atTop,
      movingRankMajorant K m ≤ Real.exp (-Real.log 2 * (m : ℝ)) := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (256 : ℕ), tendsto_atTop.1 hnat K] with m hm hKm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm256 : (256 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 8 * Real.log 2 ≤ Real.log (m : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hm256
    have he : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at hh
  apply (movingRankMajorant_superexp K m hK hm hKm).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog hm0
  nlinarith

theorem movingRankMajorant_polynomial_tendsto (K : ℝ) (hK : 0 ≤ K) (k : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k * movingRankMajorant K m) atTop (𝓝 0) := by
  have hbase : Tendsto (fun m : ℕ => (m : ℝ) ^ k *
      Real.exp (-Real.log 2 * (m : ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ)
      (Real.log 2) (Real.log_pos (by norm_num))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
    simpa only [Real.rpow_natCast, Function.comp_def] using hh
  apply squeeze_zero' _ _ hbase
  · exact Eventually.of_forall (fun m => mul_nonneg (by positivity)
      (movingRankMajorant_nonneg K m hK))
  · filter_upwards [movingRankMajorant_eventually_exp K hK] with m hm
    exact mul_le_mul_of_nonneg_left hm (by positivity)

theorem moving_upper_mass_eventually_unit (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ m : ℕ in atTop, 2 * K / (m : ℝ) ^ 2 ∈ Icc (0 : ℝ) 1 := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), tendsto_atTop.1 hnat (2 * K)] with m hm hKm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hm0)).2
  nlinarith

def originalMovingDeficit (mu : ℕ → Measure ℝ) (m : ℕ) : ℝ :=
  1 - Existence.RankEnvelope.rank (mu m) (m - 1) (marketCapacity m) 2 (movingThreshold m)

def originalMovingError (mu : ℕ → Measure ℝ) (R : ℕ → ℝ) (m : ℕ) : ℝ :=
  Existence.RankEnvelope.error
    (Existence.RankEnvelope.rank (mu m) (m - 1) (marketCapacity m) 2)
    (movingThreshold m) (R m)

theorem original_moving_upper_bounds
    (mu : ℕ → Measure ℝ) (R : ℕ → ℝ) (K : ℝ) (m : ℕ) (hm : 200 ≤ m)
    (hh : 2 * K / (m : ℝ) ^ 2 ∈ Icc (0 : ℝ) 1)
    (hR : 0 ≤ R m) (hRt : R m ≤ movingThreshold m)
    (hrelative : ∀ v, movingThreshold m ≤ v →
      (mu m).real (Ioi v) = (2 * K / (m : ℝ) ^ 2) * powerTail (movingThreshold m) 10 v) :
    (0 ≤ originalMovingDeficit mu m ∧ originalMovingDeficit mu m ≤ movingRankMajorant K m) ∧
    (0 ≤ originalMovingError mu R m ∧
      originalMovingError mu R m ≤ 2 * movingThreshold m * movingRankMajorant K m) := by
  have ht := movingThreshold_pos m (by omega)
  obtain ⟨hclo, hchi, hc, hcm⟩ := capacity_bounds m hm
  have hcc : marketCapacity m ≤ m - 1 + 1 := by omega
  have he := original_pareto_error_bound (mu m) (m - 1) (marketCapacity m)
    (2 * K / (m : ℝ) ^ 2) (movingThreshold m) (R m) hc hcc hh ht hR hRt hrelative
  have hd := paretoRankFailure_bounds (m - 1) (marketCapacity m)
    (2 * K / (m : ℝ) ^ 2) (movingThreshold m) (movingThreshold m) hcc hh ht le_rfl
  rw [powerTail_at_floor _ _ ht.ne', mul_one, rankTailConstant_moving] at hd
  have hid := original_rank_failure_eq_pareto (mu m) (m - 1) (marketCapacity m)
    (2 * K / (m : ℝ) ^ 2) (movingThreshold m) (movingThreshold m) hcc hh ht le_rfl
    (hrelative _ le_rfl)
  rw [← hid] at hd
  rw [rankTailConstant_moving] at he
  exact ⟨hd, he⟩

theorem original_moving_upper_scaled_limits
    (mu : ℕ → Measure ℝ) (R : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hsource : ∀ᶠ m : ℕ in atTop,
      0 ≤ R m ∧ R m ≤ movingThreshold m ∧
      ∀ v, movingThreshold m ≤ v →
        (mu m).real (Ioi v) = (2 * K / (m : ℝ) ^ 2) * powerTail (movingThreshold m) 10 v) :
    Tendsto (fun m => movingThreshold m ^ 2 * originalMovingDeficit mu m) atTop (𝓝 0) ∧
    Tendsto (fun m => movingThreshold m * originalMovingError mu R m) atTop (𝓝 0) := by
  have hbound : ∀ᶠ m : ℕ in atTop,
      (0 ≤ originalMovingDeficit mu m ∧ originalMovingDeficit mu m ≤ movingRankMajorant K m) ∧
      (0 ≤ originalMovingError mu R m ∧
        originalMovingError mu R m ≤ 2 * movingThreshold m * movingRankMajorant K m) := by
    filter_upwards [eventually_ge_atTop (200 : ℕ), moving_upper_mass_eventually_unit K hK,
      hsource] with m hm hh hs
    exact original_moving_upper_bounds mu R K m hm hh hs.1 hs.2.1 hs.2.2
  have hlim := movingRankMajorant_polynomial_tendsto K hK 2
  constructor
  · apply squeeze_zero' _ _ hlim
    · filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with m hb hm
      exact mul_nonneg (sq_nonneg _) hb.1.1
    · filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with m hb hm
      have ht0 := (movingThreshold_pos m (by omega)).le
      have htm := movingThreshold_le_population m hm
      have hp := pow_le_pow_left₀ ht0 htm 2
      exact (mul_le_mul_of_nonneg_left hb.1.2 (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hp (movingRankMajorant_nonneg K m hK))
  · have hlim2 : Tendsto (fun m : ℕ => 2 * ((m : ℝ) ^ 2 * movingRankMajorant K m))
        atTop (𝓝 0) := by simpa only [mul_zero] using hlim.const_mul 2
    apply squeeze_zero' _ _ hlim2
    · filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with m hb hm
      exact mul_nonneg (movingThreshold_pos m (by omega)).le hb.2.1
    · filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with m hb hm
      have ht0 := (movingThreshold_pos m (by omega)).le
      have hp := pow_le_pow_left₀ ht0 (movingThreshold_le_population m hm) 2
      have h1 := mul_le_mul_of_nonneg_left hb.2.2 ht0
      have h2 := mul_le_mul_of_nonneg_right hp (movingRankMajorant_nonneg K m hK)
      nlinarith

theorem original_moving_upper_limits
    (mu : ℕ → Measure ℝ) (R : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hsource : ∀ᶠ m : ℕ in atTop,
      0 ≤ R m ∧ R m ≤ movingThreshold m ∧
      ∀ v, movingThreshold m ≤ v →
        (mu m).real (Ioi v) = (2 * K / (m : ℝ) ^ 2) * powerTail (movingThreshold m) 10 v) :
    Tendsto (originalMovingDeficit mu) atTop (𝓝 0) ∧
    Tendsto (originalMovingError mu R) atTop (𝓝 0) := by
  have hscaled := original_moving_upper_scaled_limits mu R K hK hsource
  have hnonneg : ∀ᶠ m : ℕ in atTop,
      0 ≤ originalMovingDeficit mu m ∧ 0 ≤ originalMovingError mu R m := by
    filter_upwards [eventually_ge_atTop (200 : ℕ), moving_upper_mass_eventually_unit K hK,
      hsource] with m hm hh hs
    have hb := original_moving_upper_bounds mu R K m hm hh hs.1 hs.2.1 hs.2.2
    exact ⟨hb.1.1, hb.2.1⟩
  constructor
  · apply squeeze_zero' (hnonneg.mono (fun _ h => h.1)) _ hscaled.1
    filter_upwards [hnonneg, eventually_ge_atTop (1 : ℕ)] with m hm hn
    have ht := movingThreshold_ge_one m hn
    have hp : 1 ≤ movingThreshold m ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hm.1
  · apply squeeze_zero' (hnonneg.mono (fun _ h => h.2)) _ hscaled.2
    filter_upwards [hnonneg, eventually_ge_atTop (1 : ℕ)] with m hm hn
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (movingThreshold_ge_one m hn) hm.2

theorem original_moving_eventually_hidden_guard
    (mu : ℕ → Measure ℝ) (R : ℕ → ℝ) (K eta R0 : ℝ)
    (hK : 0 ≤ K) (heta : 0 < eta) (hR0 : 0 < R0)
    (hlower : ∀ᶠ m : ℕ in atTop, R0 ≤ R m)
    (hsource : ∀ᶠ m : ℕ in atTop,
      0 ≤ R m ∧ R m ≤ movingThreshold m ∧
      ∀ v, movingThreshold m ≤ v →
        (mu m).real (Ioi v) = (2 * K / (m : ℝ) ^ 2) * powerTail (movingThreshold m) 10 v) :
    ∀ᶠ m : ℕ in atTop,
      originalMovingError mu R m < eta * R m * (1 - 2 * originalMovingDeficit mu m) := by
  have hlim := original_moving_upper_limits mu R K hK hsource
  have hguard := Hybrid.eventually_upper_hidden_guard hlim.2 hlim.1 heta hR0
  have hsmall : ∀ᶠ m : ℕ in atTop, originalMovingDeficit mu m < 1 / 2 :=
    hlim.1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hguard, hlower, hsmall] with m hg hR hd
  apply hg.trans_le
  have h := mul_le_mul_of_nonneg_left hR heta.le
  exact mul_le_mul_of_nonneg_right h (by linarith)

end FCAppendix.Affine.Tail04
