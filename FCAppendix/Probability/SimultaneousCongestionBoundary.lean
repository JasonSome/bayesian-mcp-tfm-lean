import FCAppendix.Probability.SimultaneousCongestionRows

namespace FCAppendix.SimultaneousCongestion

open Filter Topology Real CommonList Proposer
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem congestionProb_empty (μ : FiniteLaw (Finset ι)) (N c : ℕ) :
    congestionProb μ ∅ N c = 1 := by
  classical
  simp [congestionProb, Congested, FiniteLaw.prob]

theorem congestionProb_eq_zero_of_support_bound
    (μ : FiniteLaw (Finset ι)) (K : Finset ι) (N c R : ℕ)
    (hsupport : ∀ S, 0 < μ.mass S → selected K S ≤ R)
    (hcut : N * R < K.card * c) :
    congestionProb μ K N c = 0 := by
  classical
  unfold congestionProb FiniteLaw.prob FiniteLaw.expect
  apply Finset.sum_eq_zero
  intro T _
  by_cases hT : Congested K c T
  · simp only [if_pos hT, mul_one]
    change (∏ i : Fin N, μ.mass (T i)) = 0
    by_contra hp
    have hm (i : Fin N) : 0 < μ.mass (T i) :=
      lt_of_le_of_ne (μ.nonneg _) (Ne.symm ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)))
    have hupper : (∑ i : Fin N, (selected K (T i) : ℝ)) ≤ (N : ℝ) * R := by
      calc
        _ ≤ ∑ _ : Fin N, (R : ℝ) := Finset.sum_le_sum (fun i _ => by
          exact_mod_cast hsupport (T i) (hm i))
        _ = _ := by simp
    have hlower : (K.card : ℝ) * c ≤ ∑ s ∈ K, (includers s T : ℝ) := by
      calc
        _ = ∑ _s ∈ K, (c : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun s hs => by exact_mod_cast hT s hs)
    rw [← sum_selected_eq] at hlower
    have hcut' : (N : ℝ) * R < (K.card : ℝ) * c := by exact_mod_cast hcut
    linarith
  · simp [hT]

theorem congestionProb_eq_zero_of_capacity_gt
    (μ : FiniteLaw (Finset ι)) {K : Finset ι} (hK : K.Nonempty)
    {N c : ℕ} (hc : N < c) : congestionProb μ K N c = 0 := by
  apply congestionProb_eq_zero_of_support_bound μ K N c K.card
    (fun S _ => selected_le K S)
  have hh := Nat.mul_lt_mul_of_pos_right hc (Finset.card_pos.mpr hK)
  simpa only [Nat.mul_comm] using hh

theorem congestionProb_le_exp_objective (μ : FiniteLaw (Finset ι))
    (K : Finset ι) (N c : ℕ) (hN : 0 < N) {θ : ℝ} (hθ : 0 ≤ θ) :
    congestionProb μ K N c ≤ exp (-(N : ℝ) *
      FiniteCramer.objective μ (count K) (K.card * ((c : ℝ) / N)) θ) := by
  have h := congestionProb_le μ K N c hθ
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hZ : 0 < mgf μ K θ := mgf_pos μ K θ
  have he : exp (-(θ * (K.card * c))) * mgf μ K θ ^ N =
      exp (-(N : ℝ) * FiniteCramer.objective μ (count K)
        (K.card * ((c : ℝ) / N)) θ) := by
    have hpow : mgf μ K θ ^ N = exp ((N : ℝ) * log (mgf μ K θ)) := by
      rw [exp_nat_mul, exp_log hZ]
    rw [hpow, ← exp_add]
    congr 1
    change -(θ * ((K.card : ℝ) * c)) + (N : ℝ) * log (mgf μ K θ) =
      -(N : ℝ) * ((K.card * ((c : ℝ) / N)) * θ - log (mgf μ K θ))
    field_simp [hn]
    ring
  rwa [he] at h

theorem eventually_exp_upper_of_witness
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    {N c : ℕ → ℕ} (hN : Tendsto N atTop atTop) {ρ θ d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / N a) atTop (𝓝 ρ))
    (hθ : 0 ≤ θ) (hd : d < FiniteCramer.objective μ (count K) (K.card * ρ) θ) :
    ∀ᶠ a in atTop, congestionProb (μa a) K (N a) (c a) ≤ exp (-d * N a) := by
  have hlim : Tendsto (fun a => FiniteCramer.objective (μa a) (count K)
      (K.card * ((c a : ℝ) / N a)) θ) atTop
        (𝓝 (FiniteCramer.objective μ (count K) (K.card * ρ) θ)) :=
    ((hc.const_mul (K.card : ℝ)).mul_const θ).sub
      (FiniteCramer.tendsto_cgf hμ (count K) tendsto_const_nhds)
  filter_upwards [hN.eventually_ge_atTop 1, hlim.eventually_const_lt hd] with a hn ha
  apply (congestionProb_le_exp_objective (μa a) K (N a) (c a) (by omega) hθ).trans
  apply exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left ha.le (Nat.cast_nonneg (N a) : (0 : ℝ) ≤ N a)
  nlinarith

theorem eventually_exp_upper_full_population
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ θ d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hθ : 0 ≤ θ) (hd : d < FiniteCramer.objective μ (count K) (K.card * ρ) θ) :
    ∀ᶠ a in atTop, congestionProb (μa a) K (M a - 1) (c a) ≤ exp (-d * M a) := by
  let L := FiniteCramer.objective μ (count K) (K.card * ρ) θ
  obtain ⟨e, hde, heL⟩ := exists_between hd
  have hb := eventually_exp_upper_of_witness hμ (rival_population_scaling hM).1
    (capacity_per_rival hM hc) hθ heL
  have hratio : Tendsto (fun a => e * (((M a - 1 : ℕ) : ℝ) / M a)) atTop (𝓝 e) := by
    simpa using (rival_population_scaling hM).2.const_mul e
  filter_upwards [hb, hM.eventually_ge_atTop 1,
    hratio.eventually_const_lt hde] with a ha hm hr
  have hm' : (0 : ℝ) < M a := by exact_mod_cast (show 0 < M a by omega)
  have hmul := (lt_div_iff₀ hm').mp (show d < e * ((M a - 1 : ℕ) : ℝ) / M a by
    simpa only [mul_div_assoc] using hr)
  exact ha.trans (exp_le_exp.mpr (by linarith))

theorem eventually_exp_upper_of_unbounded_objective
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hunbounded : ∀ d : ℝ, ∃ θ, 0 ≤ θ ∧
      d < FiniteCramer.objective μ (count K) (K.card * ρ) θ) :
    ∀ d : ℝ, ∀ᶠ a in atTop,
      congestionProb (μa a) K (M a - 1) (c a) ≤ exp (-d * M a) := by
  intro d
  obtain ⟨θ, hθ, hd⟩ := hunbounded d
  exact eventually_exp_upper_full_population hμ hM hc hθ hd

theorem zero_contact_limit_superexponential
    {μa : ℕ → FiniteLaw (Finset ι)} {μ : FiniteLaw (Finset ι)} {K : Finset ι}
    (hK : K.Nonempty)
    (hzero : ∀ S, 0 < μ.mass S → selected K S = 0)
    (hμ : ∀ S, Tendsto (fun a => (μa a).mass S) atTop (𝓝 (μ.mass S)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ)) :
    ∀ d : ℝ, ∀ᶠ a in atTop,
      congestionProb (μa a) K (M a - 1) (c a) ≤ exp (-d * M a) := by
  have hk : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hcgf (θ : ℝ) : FiniteCramer.cgf μ (count K) θ = 0 := by
    have hZ : FiniteCramer.Z μ (count K) θ = 1 := by
      calc
        _ = μ.expect (fun _ => 1) := by
          unfold FiniteCramer.Z FiniteLaw.expect
          apply Finset.sum_congr rfl
          intro S _
          by_cases hs : μ.mass S = 0
          · simp [hs]
          · have hz := hzero S (lt_of_le_of_ne (μ.nonneg S) (Ne.symm hs))
            simp [count, hz]
        _ = 1 := μ.expect_const 1
    simp [FiniteCramer.cgf, hZ]
  apply eventually_exp_upper_of_unbounded_objective hμ hM hc
  intro d
  let θ := (|d| + 1) / ((K.card : ℝ) * ρ)
  have hθ : 0 < θ := div_pos (by positivity) (mul_pos hk hρ)
  refine ⟨θ, hθ.le, ?_⟩
  rw [FiniteCramer.objective, hcgf, sub_zero]
  have he : (K.card : ℝ) * ρ * θ = |d| + 1 := by
    dsimp [θ]
    field_simp
  rw [he]
  linarith [le_abs_self d]

end FCAppendix.SimultaneousCongestion
