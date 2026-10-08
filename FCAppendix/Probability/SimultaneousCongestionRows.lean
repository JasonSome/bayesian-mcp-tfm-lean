import FCAppendix.Probability.FiniteTiltCalculus

namespace FCAppendix.SimultaneousCongestion

open Filter Topology Set Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def count (K : Finset ι) (S : Finset ι) : ℝ := selected K S

@[simp] theorem Z_count (μ : FiniteLaw (Finset ι)) (K : Finset ι) (t : ℝ) :
    FiniteCramer.Z μ (count K) t = mgf μ K t := rfl

@[simp] theorem mean_count (μ : FiniteLaw (Finset ι)) (K : Finset ι) (t : ℝ) :
    FiniteCramer.mean μ (count K) t = tiltMean μ K t := rfl

theorem log_congestion_lower {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hswap : SwapInvariant μ K) (N c : ℕ) (hNpos : 0 < N) {t η : ℝ}
    (ht : 0 ≤ t) (hη : 0 < η)
    (hN : (K.card : ℝ) ≤ 2 * N * η ^ 2)
    (hc : (c : ℝ) ≤ N * (tiltMean μ K t / K.card - η)) :
    0 < congestionProb μ K N c ∧
    FiniteCramer.cgf μ (count K) t - t * (tiltMean μ K t + K.card * η) -
      log 2 / N ≤ log (congestionProb μ K N c) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  let L := exp (-(t * (N * (tiltMean μ K t + K.card * η)))) * (mgf μ K t) ^ N / 2
  have hL : 0 < L := div_pos (mul_pos (exp_pos _) (pow_pos (mgf_pos μ K t) N))
    (by norm_num)
  have hLP : L ≤ congestionProb μ K N c :=
    congestionProb_ge_of_swap hswap N c ht hη hN hc
  refine ⟨hL.trans_le hLP, ?_⟩
  have hlog := (div_le_div_of_nonneg_right (log_le_log hL hLP) hN'.le)
  have heq : log L / N = FiniteCramer.cgf μ (count K) t -
      t * (tiltMean μ K t + K.card * η) - log 2 / N := by
    dsimp [L, FiniteCramer.cgf]
    rw [log_div (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ (mgf_pos μ K t).ne')) (by norm_num),
      log_mul (exp_ne_zero _) (pow_ne_zero _ (mgf_pos μ K t).ne'), log_exp, log_pow]
    field_simp
    ring
  rwa [heq] at hlog

theorem log_congestion_upper (μ : FiniteLaw (Finset ι)) (K : Finset ι)
    (N c : ℕ) (hNpos : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (hP : 0 < congestionProb μ K N c) :
    log (congestionProb μ K N c) / N ≤
      FiniteCramer.cgf μ (count K) t - t * K.card * ((c : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlog := log_le_log hP (congestionProb_le μ K N c ht)
  rw [log_mul (exp_ne_zero _) (pow_ne_zero _ (mgf_pos μ K t).ne'),
    log_exp, log_pow] at hlog
  have hh := div_le_div_of_nonneg_right hlog hN'.le
  apply hh.trans_eq
  change _ = log (mgf μ K t) - _
  field_simp [hN'.ne']
  ring

theorem eventually_log_lower_of_tilt
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    (hswap : ∀ᶠ a in atTop, SwapInvariant (μa a) K)
    {N c : ℕ → ℕ} (hN : Tendsto N atTop atTop) {ρ t η d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / N a) atTop (𝓝 ρ))
    (ht : 0 ≤ t) (hη : 0 < η)
    (hgap : ρ < tiltMean μ K t / K.card - η)
    (hd : d < FiniteCramer.cgf μ (count K) t -
      t * (tiltMean μ K t + K.card * η)) :
    ∀ᶠ a in atTop, 0 < congestionProb (μa a) K (N a) (c a) ∧
      d ≤ log (congestionProb (μa a) K (N a) (c a)) / N a := by
  have hm : Tendsto (fun a => tiltMean (μa a) K t) atTop (𝓝 (tiltMean μ K t)) :=
    FiniteCramer.tendsto_mean hμ (count K) tendsto_const_nhds
  have hthreshold : ∀ᶠ a in atTop,
      (c a : ℝ) / N a ≤ tiltMean (μa a) K t / K.card - η := by
    have hh := ((hm.div_const (K.card : ℝ)).sub_const η).sub hc
    filter_upwards [hh.eventually_const_lt (show 0 <
      tiltMean μ K t / K.card - η - ρ by linarith)] with a ha
    linarith
  have hNatPos := hN.eventually_ge_atTop 1
  have hrealTop : Tendsto (fun a => (N a : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlarge : ∀ᶠ a in atTop, (K.card : ℝ) ≤ 2 * N a * η ^ 2 := by
    have hh := (hrealTop.const_mul_atTop (show 0 < 2 * η ^ 2 by positivity)).eventually_ge_atTop
      (K.card : ℝ)
    filter_upwards [hh] with a ha
    nlinarith
  have hlogzero : Tendsto (fun a => log 2 / (N a : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (log 2)).comp hN
  have hlower := ((FiniteCramer.tendsto_cgf hμ (count K) (t := t) tendsto_const_nhds).sub
    ((hm.add_const ((K.card : ℝ) * η)).const_mul t)).sub hlogzero
  have hbound : ∀ᶠ a in atTop, d < FiniteCramer.cgf (μa a) (count K) t -
      t * (tiltMean (μa a) K t + K.card * η) - log 2 / N a :=
    hlower.eventually_const_lt (by simpa using hd)
  filter_upwards [hswap, hNatPos, hlarge, hthreshold, hbound] with a hs hn hl hth hb
  have hn' : (0 : ℝ) < N a := by exact_mod_cast (show 0 < N a by omega)
  have hct : (c a : ℝ) ≤ N a * (tiltMean (μa a) K t / K.card - η) := by
    simpa only [mul_comm] using (div_le_iff₀ hn').mp hth
  obtain ⟨hp, hlog⟩ := log_congestion_lower hs (N a) (c a) (by omega) ht hη hl hct
  exact ⟨hp, hb.le.trans hlog⟩

theorem eventually_log_lower
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hK : K.Nonempty)
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    (hswap : ∀ᶠ a in atTop, SwapInvariant (μa a) K)
    {N c : ℕ → ℕ} (hN : Tendsto N atTop atTop) {ρ t d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / N a) atTop (𝓝 ρ))
    (ht : 0 ≤ t) (hgap : (K.card : ℝ) * ρ < tiltMean μ K t)
    (hd : d < FiniteCramer.cgf μ (count K) t - t * tiltMean μ K t) :
    ∀ᶠ a in atTop, 0 < congestionProb (μa a) K (N a) (c a) ∧
      d ≤ log (congestionProb (μa a) K (N a) (c a)) / N a := by
  have hk : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  let z := tiltMean μ K t
  let A := FiniteCramer.cgf μ (count K) t - t * z
  let η := min ((z / K.card - ρ) / 2) ((A - d) / (2 * (|t| * K.card + 1)))
  have hgap' : ρ < z / K.card := (lt_div_iff₀ hk).mpr (by simpa [z, mul_comm] using hgap)
  have hden : 0 < 2 * (|t| * K.card + 1) := by positivity
  have hη : 0 < η := lt_min (by linarith) (div_pos (sub_pos.mpr hd) hden)
  have hη₁ : η ≤ (z / K.card - ρ) / 2 := min_le_left _ _
  have hη₂ : η * (2 * (|t| * K.card + 1)) ≤ A - d :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  apply eventually_log_lower_of_tilt hμ hswap hN hc ht hη
  · change ρ < z / K.card - η
    linarith
  · change d < FiniteCramer.cgf μ (count K) t - t * (z + K.card * η)
    rw [abs_of_nonneg ht] at hη₂
    dsimp [A] at hη₂
    have hprod : 0 ≤ t * (K.card : ℝ) * η := by positivity
    nlinarith

theorem eventually_log_upper
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    {N c : ℕ → ℕ} (hN : Tendsto N atTop atTop) {ρ t d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / N a) atTop (𝓝 ρ))
    (hpos : ∀ᶠ a in atTop, 0 < congestionProb (μa a) K (N a) (c a))
    (ht : 0 ≤ t)
    (hd : FiniteCramer.cgf μ (count K) t - t * K.card * ρ < d) :
    ∀ᶠ a in atTop, log (congestionProb (μa a) K (N a) (c a)) / N a ≤ d := by
  have he := (FiniteCramer.tendsto_cgf hμ (count K) (t := t) tendsto_const_nhds).sub
    (hc.const_mul (t * K.card))
  filter_upwards [hpos, hN.eventually_ge_atTop 1, he.eventually_lt_const hd] with a hp hn ha
  exact (log_congestion_upper (μa a) K (N a) (c a) (by omega) ht hp).trans ha.le

theorem tendsto_log_congestion
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hK : K.Nonempty)
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    (hswap : ∀ᶠ a in atTop, SwapInvariant (μa a) K)
    {N c : ℕ → ℕ} (hN : Tendsto N atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / N a) atTop (𝓝 ρ))
    (hint : FiniteCramer.Interior μ (count K) (K.card * ρ)) :
    (∀ᶠ a in atTop, 0 < congestionProb (μa a) K (N a) (c a)) ∧
    Tendsto (fun a => log (congestionProb (μa a) K (N a) (c a)) / N a) atTop
      (𝓝 (-FiniteCramer.rate μ (count K) (K.card * ρ))) := by
  have hlo (d : ℝ) (hd : d < -FiniteCramer.rate μ (count K) (K.card * ρ)) :
      ∀ᶠ a in atTop, 0 < congestionProb (μa a) K (N a) (c a) ∧
        d ≤ log (congestionProb (μa a) K (N a) (c a)) / N a := by
    obtain ⟨t, ht, hm, he⟩ := FiniteCramer.exists_tilt_lower_bound hint hd
    exact eventually_log_lower hK hμ hswap hN hc ht hm he
  have hpos := (hlo (-FiniteCramer.rate μ (count K) (K.card * ρ) - 1) (by linarith)).mono
    (fun _ ha => ha.1)
  refine ⟨hpos, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro d hd
    obtain ⟨e, hde, he⟩ := exists_between hd
    exact (hlo e he).mono (fun _ ha => hde.trans_le ha.2)
  · intro d hd
    obtain ⟨e, he, hed⟩ := exists_between hd
    obtain ⟨t, ht, hm, hr⟩ := FiniteCramer.optimizer hint
    have htval : FiniteCramer.cgf μ (count K) t - t * K.card * ρ =
        -FiniteCramer.rate μ (count K) (K.card * ρ) := by
      rw [hr]
      dsimp [FiniteCramer.objective]
      ring
    exact (eventually_log_upper hμ hN hc hpos ht.le (htval ▸ he)).mono
      (fun _ ha => ha.trans_lt hed)

theorem rival_population_scaling {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    Tendsto (fun a => M a - 1) atTop atTop ∧
    Tendsto (fun a => ((M a - 1 : ℕ) : ℝ) / M a) atTop (𝓝 1) := by
  have hN : Tendsto (fun a => M a - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hM.eventually_ge_atTop (b + 1)] with a ha
    omega
  refine ⟨hN, ?_⟩
  have hz : Tendsto (fun a => 1 / (M a : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp hM
  have he : (fun a => ((M a - 1 : ℕ) : ℝ) / M a) =ᶠ[atTop]
      (fun a => 1 - 1 / (M a : ℝ)) := by
    filter_upwards [hM.eventually_ge_atTop 1] with a ha
    have hm : (M a : ℝ) ≠ 0 := by exact_mod_cast (show M a ≠ 0 by omega)
    rw [Nat.cast_sub ha, Nat.cast_one, sub_div, div_self hm]
  simpa only [sub_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hz).congr' he.symm

theorem capacity_per_rival {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ)) :
    Tendsto (fun a => (c a : ℝ) / (M a - 1 : ℕ)) atTop (𝓝 ρ) := by
  have he := hc.div (rival_population_scaling hM).2 (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun a => ((c a : ℝ) / M a) / (((M a - 1 : ℕ) : ℝ) / M a)) =ᶠ[atTop]
      (fun a => (c a : ℝ) / (M a - 1 : ℕ)) := by
    filter_upwards [hM.eventually_ge_atTop 2] with a ha
    have hm : (M a : ℝ) ≠ 0 := by exact_mod_cast (show M a ≠ 0 by omega)
    have hn : ((M a - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show M a - 1 ≠ 0 by omega)
    field_simp
  simpa using he.congr' heq

theorem tendsto_neg_log_congestion_full_population
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hK : K.Nonempty)
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    (hswap : ∀ᶠ a in atTop, SwapInvariant (μa a) K)
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hint : FiniteCramer.Interior μ (count K) (K.card * ρ)) :
    (∀ᶠ a in atTop, 0 < congestionProb (μa a) K (M a - 1) (c a)) ∧
    Tendsto (fun a => -log (congestionProb (μa a) K (M a - 1) (c a)) / M a) atTop
      (𝓝 (FiniteCramer.rate μ (count K) (K.card * ρ))) := by
  obtain ⟨hp, hlog⟩ := tendsto_log_congestion hK hμ hswap
    (rival_population_scaling hM).1 (capacity_per_rival hM hc) hint
  refine ⟨hp, ?_⟩
  have he := hlog.neg.mul (rival_population_scaling hM).2
  have heq : (fun a => -(log (congestionProb (μa a) K (M a - 1) (c a)) /
      (M a - 1 : ℕ)) * (((M a - 1 : ℕ) : ℝ) / M a)) =ᶠ[atTop]
      (fun a => -log (congestionProb (μa a) K (M a - 1) (c a)) / M a) := by
    filter_upwards [hM.eventually_ge_atTop 2] with a ha
    have hn : ((M a - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show M a - 1 ≠ 0 by omega)
    field_simp
  simpa only [neg_neg, mul_one] using he.congr' heq

end FCAppendix.SimultaneousCongestion
