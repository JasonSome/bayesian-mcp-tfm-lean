import FCAppendix.Probability.SimultaneousCongestionRows

namespace FCAppendix.SimultaneousCongestion

open Filter Topology Set Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tendsto_of_abs_sub_le {A : Type*} {l : Filter A}
    {f g e : A → ℝ} {a : ℝ} (hg : Tendsto g l (𝓝 a))
    (he : Tendsto e l (𝓝 0)) (hfg : ∀ᶠ x in l, |f x - g x| ≤ e x) :
    Tendsto f l (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hfg, he.eventually_lt_const (show 0 < ε / 2 by linarith),
    (Metric.tendsto_nhds.mp hg) (ε / 2) (by linarith)] with x hx hxe hxg
  calc
    dist (f x) a ≤ dist (f x) (g x) + dist (g x) a := dist_triangle _ _ _
    _ ≤ e x + dist (g x) a := by rw [Real.dist_eq]; linarith
    _ < ε := by linarith

theorem tendsto_of_abs_sub_lt_one_div {f g : ℕ → ℝ} {a : ℝ}
    (hg : Tendsto g atTop (𝓝 a))
    (hfg : ∀ j, |f j - g j| < 1 / ((j : ℝ) + 1)) :
    Tendsto f atTop (𝓝 a) :=
  tendsto_of_abs_sub_le hg tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall (fun j => (hfg j).le))

theorem locally_uniform_congestion
    {μ : FiniteLaw (Finset ι)} {K : Finset ι} {ρ : ℝ}
    (hK : K.Nonempty)
    (hint : FiniteCramer.Interior μ (count K) (K.card * ρ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ (ν : FiniteLaw (Finset ι)), SwapInvariant ν K →
      ∀ N ≥ N₀, ∀ c : ℕ,
      (∀ S, |ν.mass S - μ.mass S| < δ) → |(c : ℝ) / N - ρ| < δ →
      0 < congestionProb ν K N c ∧
      |-log (congestionProb ν K N c) / N -
        FiniteCramer.rate μ (count K) (K.card * ρ)| < ε := by
  classical
  by_contra hn
  have hnone : ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ,
      ¬ ∀ (ν : FiniteLaw (Finset ι)), SwapInvariant ν K →
        ∀ N ≥ N₀, ∀ c : ℕ,
        (∀ S, |ν.mass S - μ.mass S| < δ) → |(c : ℝ) / N - ρ| < δ →
        0 < congestionProb ν K N c ∧
        |-log (congestionProb ν K N c) / N -
          FiniteCramer.rate μ (count K) (K.card * ρ)| < ε := by
    simpa only [not_exists, not_and] using hn
  have hbad (j : ℕ) : ∃ (ν : FiniteLaw (Finset ι)) (N c : ℕ),
      SwapInvariant ν K ∧ j + 1 ≤ N ∧
      (∀ S, |ν.mass S - μ.mass S| < 1 / ((j : ℝ) + 1)) ∧
      |(c : ℝ) / N - ρ| < 1 / ((j : ℝ) + 1) ∧
      ¬ (0 < congestionProb ν K N c ∧
        |-log (congestionProb ν K N c) / N -
          FiniteCramer.rate μ (count K) (K.card * ρ)| < ε) := by
    have hh := hnone (1 / ((j : ℝ) + 1)) (by positivity) (j + 1)
    push Not at hh
    obtain ⟨ν, hs, N, hn, c, hm, hc, hfail⟩ := hh
    exact ⟨ν, N, c, hs, hn, hm, hc, by simpa only [not_and, not_lt] using hfail⟩
  choose ν N c hs hn hm hc hfail using hbad
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact le_trans hj (Nat.le_trans (Nat.le_succ j) (hn j))
  have hmass (S : Finset ι) : Tendsto (fun j => (ν j).mass S) atTop (𝓝 (μ.mass S)) :=
    tendsto_of_abs_sub_lt_one_div tendsto_const_nhds (fun j => hm j S)
  have hcap : Tendsto (fun j => (c j : ℝ) / N j) atTop (𝓝 ρ) :=
    tendsto_of_abs_sub_lt_one_div tendsto_const_nhds hc
  obtain ⟨hp, hlog⟩ := tendsto_log_congestion hK hmass (Eventually.of_forall hs) hN hcap hint
  have hl : Tendsto (fun j => -log (congestionProb (ν j) K (N j) (c j)) / N j) atTop
      (𝓝 (FiniteCramer.rate μ (count K) (K.card * ρ))) := by
    simpa only [neg_neg, neg_div] using hlog.neg
  have hb : ∀ᶠ j in atTop,
      |-log (congestionProb (ν j) K (N j) (c j)) / N j -
        FiniteCramer.rate μ (count K) (K.card * ρ)| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hl.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨j, hj, hj'⟩ := (hp.and hb).exists
  exact hfail j ⟨hj, hj'⟩

theorem locally_uniform_congestion_own_rate
    {μ : FiniteLaw (Finset ι)} {K : Finset ι} {ρ : ℝ}
    (hK : K.Nonempty)
    (hint : FiniteCramer.Interior μ (count K) (K.card * ρ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ (ν : FiniteLaw (Finset ι)), SwapInvariant ν K →
      ∀ N ≥ N₀, ∀ c : ℕ,
      (∀ S, |ν.mass S - μ.mass S| < δ) → |(c : ℝ) / N - ρ| < δ →
      FiniteCramer.Interior ν (count K) (K.card * ((c : ℝ) / N)) ∧
      0 < congestionProb ν K N c ∧
      |-log (congestionProb ν K N c) / N -
        FiniteCramer.rate ν (count K) (K.card * ((c : ℝ) / N))| < ε := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  have hbad (j : ℕ) : ∃ (ν : FiniteLaw (Finset ι)) (N c : ℕ),
      SwapInvariant ν K ∧ j + 1 ≤ N ∧
      (∀ S, |ν.mass S - μ.mass S| < 1 / ((j : ℝ) + 1)) ∧
      |(c : ℝ) / N - ρ| < 1 / ((j : ℝ) + 1) ∧
      ¬ (FiniteCramer.Interior ν (count K) (K.card * ((c : ℝ) / N)) ∧
        0 < congestionProb ν K N c ∧
        |-log (congestionProb ν K N c) / N -
          FiniteCramer.rate ν (count K) (K.card * ((c : ℝ) / N))| < ε) := by
    have hh := hn (1 / ((j : ℝ) + 1)) (by positivity) (j + 1)
    push Not at hh
    obtain ⟨ν, hs, N, hn, c, hm, hc, hfail⟩ := hh
    exact ⟨ν, N, c, hs, hn, hm, hc, by simpa only [not_and, not_lt] using hfail⟩
  choose ν N c hs hn hm hc hfail using hbad
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact le_trans hj (Nat.le_trans (Nat.le_succ j) (hn j))
  have hmass (S : Finset ι) : Tendsto (fun j => (ν j).mass S) atTop (𝓝 (μ.mass S)) :=
    tendsto_of_abs_sub_lt_one_div tendsto_const_nhds (fun j => hm j S)
  have hcap : Tendsto (fun j => (c j : ℝ) / N j) atTop (𝓝 ρ) :=
    tendsto_of_abs_sub_lt_one_div tendsto_const_nhds hc
  have htarget := hcap.const_mul (K.card : ℝ)
  have hi := FiniteCramer.eventually_interior hmass htarget hint
  have hr := FiniteCramer.tendsto_rate hmass htarget hint
  obtain ⟨hp, hl⟩ := tendsto_log_congestion hK hmass (Eventually.of_forall hs) hN hcap hint
  have he : Tendsto (fun j => -log (congestionProb (ν j) K (N j) (c j)) / N j -
      FiniteCramer.rate (ν j) (count K) (K.card * ((c j : ℝ) / N j))) atTop (𝓝 0) := by
    simpa only [neg_neg, neg_div, sub_self] using hl.neg.sub hr
  have hb : ∀ᶠ j in atTop,
      |-log (congestionProb (ν j) K (N j) (c j)) / N j -
        FiniteCramer.rate (ν j) (count K) (K.card * ((c j : ℝ) / N j))| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      he.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨j, hj, hpj, hbj⟩ := (hi.and (hp.and hb)).exists
  exact hfail j ⟨hj, hpj, hbj⟩

theorem compact_uniform_congestion
    {A : Type*} [MetricSpace A] {C : Set A} (hC : IsCompact C)
    (μ : A → FiniteLaw (Finset ι)) (ρ : A → ℝ) {K : Finset ι}
    (hK : K.Nonempty)
    (hmass : ∀ S, ContinuousOn (fun p => (μ p).mass S) C)
    (hρ : ContinuousOn ρ C)
    (hswap : ∀ p ∈ C, SwapInvariant (μ p) K)
    (hint : ∀ p ∈ C, FiniteCramer.Interior (μ p) (count K) (K.card * ρ p))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ p ∈ C, ∀ N ≥ N₀, ∀ c : ℕ,
      |(c : ℝ) / N - ρ p| < δ →
      0 < congestionProb (μ p) K N c ∧
      |-log (congestionProb (μ p) K N c) / N -
        FiniteCramer.rate (μ p) (count K) (K.card * ρ p)| < ε := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  have hbad (j : ℕ) : ∃ p ∈ C, ∃ N c : ℕ, j + 1 ≤ N ∧
      |(c : ℝ) / N - ρ p| < 1 / ((j : ℝ) + 1) ∧
      ¬ (0 < congestionProb (μ p) K N c ∧
        |-log (congestionProb (μ p) K N c) / N -
          FiniteCramer.rate (μ p) (count K) (K.card * ρ p)| < ε) := by
    have hh := hn (1 / ((j : ℝ) + 1)) (by positivity) (j + 1)
    push Not at hh
    obtain ⟨p, hp, N, hN, c, hc, hf⟩ := hh
    exact ⟨p, hp, N, c, hN, hc, by simpa only [not_and, not_lt] using hf⟩
  choose p hp N c hN hc hfail using hbad
  obtain ⟨q, hq, χ, hχ, hconv⟩ := hC.isSeqCompact hp
  have hwithin : Tendsto (p ∘ χ) atTop (𝓝[C] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall (fun j => hp (χ j))⟩
  have hμlim (S : Finset ι) :
      Tendsto (fun j => (μ (p (χ j))).mass S) atTop (𝓝 ((μ q).mass S)) :=
    (hmass S q hq).tendsto.comp hwithin
  have hρlim : Tendsto (fun j => ρ (p (χ j))) atTop (𝓝 (ρ q)) :=
    (hρ q hq).tendsto.comp hwithin
  have hNtop : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact le_trans hj (Nat.le_trans (Nat.le_succ j) (hN j))
  have hcap : Tendsto (fun j => (c (χ j) : ℝ) / N (χ j)) atTop (𝓝 (ρ q)) :=
    tendsto_of_abs_sub_le hρlim
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hχ.tendsto_atTop)
      (Eventually.of_forall (fun j => (hc (χ j)).le))
  obtain ⟨hpos, hlog⟩ := tendsto_log_congestion hK hμlim
    (Eventually.of_forall (fun j => hswap _ (hp (χ j))))
    (hNtop.comp hχ.tendsto_atTop) hcap (hint q hq)
  have hr := FiniteCramer.tendsto_rate hμlim (hρlim.const_mul (K.card : ℝ)) (hint q hq)
  have he := hlog.neg.sub hr
  have hb := (Metric.tendsto_nhds.mp he) ε hε
  obtain ⟨j, hj, hj'⟩ := (hpos.and hb).exists
  apply hfail (χ j)
  refine ⟨hj, ?_⟩
  simpa only [neg_neg, sub_self, Real.dist_eq, sub_zero, neg_div, Function.comp_apply] using hj'

end FCAppendix.SimultaneousCongestion
