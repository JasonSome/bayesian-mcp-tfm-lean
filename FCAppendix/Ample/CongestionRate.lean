import FCAppendix.Ample.ContactLaw
import FCAppendix.Probability.SimultaneousCongestionBoundary

namespace FCAppendix.Ample

open Finset Filter Topology Real
open scoped BigOperators

theorem rival_optimizer_of_law {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    {lawWeights : ℕ → ℝ} (hlam : ValidLaw n lawWeights) {ρ : ℝ}
    (hslack : contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    ∃ t, 0 < t ∧
      SimultaneousCongestion.tiltMean (contactLaw n lawWeights hlam) (selected n k) t = k * ρ ∧
      rivalObjective n ρ k lawWeights t = rivalRate n ρ k lawWeights ∧ 0 < rivalRate n ρ k lawWeights := by
  have hi := contactLaw_interior hk1 hk hlam hslack htop
  obtain ⟨t, ht, hm, hr⟩ := FiniteCramer.optimizer hi
  have hp := FiniteCramer.rate_pos hi
  rw [contactLaw_rate hk] at hp hr
  refine ⟨t, ht, hm, ?_, hp⟩
  simpa only [FiniteCramer.objective, contactLaw_cgf, card_selected hk, rivalObjective]
    using hr.symm

theorem ample_event_rate
    {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    {lama : ℕ → ℕ → ℝ} {lawWeights : ℕ → ℝ}
    (hlama : ∀ a, ValidLaw n (lama a)) (hlam : ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Icc 1 n, Tendsto (fun a => lama a j) atTop (𝓝 (lawWeights j)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hslack : contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    (∀ᶠ a in atTop, 0 < congestProb n (M a - 1) (c a) k (lama a)) ∧
    Tendsto (fun a => -log (congestProb n (M a - 1) (c a) k (lama a)) / M a) atTop
      (𝓝 (rivalRate n ρ k lawWeights)) := by
  have hK : (selected n k).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_selected hk]
    omega
  have hi : FiniteCramer.Interior (contactLaw n lawWeights hlam)
      (SimultaneousCongestion.count (selected n k)) ((selected n k).card * ρ) := by
    rw [card_selected hk]
    exact contactLaw_interior hk1 hk hlam hslack htop
  have hh := SimultaneousCongestion.tendsto_neg_log_congestion_full_population hK
    (contactLaw_mass_tendsto hlama hlam hconv)
    (Eventually.of_forall (fun a => contactLaw_swapInvariant n (lama a) (hlama a) (selected n k)))
    hM hc hi
  simpa only [contactLaw_congestionProb, card_selected hk, contactLaw_rate hk, congestProb] using hh

theorem ample_event_rate_at
    {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) (K : Finset (Fin n)) (hK : K.card = k)
    {lama : ℕ → ℕ → ℝ} {lawWeights : ℕ → ℝ}
    (hlama : ∀ a, ValidLaw n (lama a)) (hlam : ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Icc 1 n, Tendsto (fun a => lama a j) atTop (𝓝 (lawWeights j)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hslack : contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    (∀ᶠ a in atTop, 0 < congestProbAt n (M a - 1) (c a) (lama a) K) ∧
    Tendsto (fun a => -log (congestProbAt n (M a - 1) (c a) (lama a) K) / M a) atTop
      (𝓝 (rivalRate n ρ k lawWeights)) := by
  simpa only [congestProbAt_eq_congestProb, hK] using
    ample_event_rate hk1 hk hlama hlam hconv hM hc hslack htop

theorem rivalRate_tendsto {A : Type*} {l : Filter A} {n k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ n) {lama : A → ℕ → ℝ} {lawWeights : ℕ → ℝ}
    (hlama : ∀ a, ValidLaw n (lama a)) (hlam : ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Icc 1 n, Tendsto (fun a => lama a j) l (𝓝 (lawWeights j)))
    {ρa : A → ℝ} {ρ : ℝ} (hρ : Tendsto ρa l (𝓝 ρ))
    (hslack : contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    Tendsto (fun a => rivalRate n (ρa a) k (lama a)) l (𝓝 (rivalRate n ρ k lawWeights)) := by
  have hh := FiniteCramer.tendsto_rate (contactLaw_mass_tendsto hlama hlam hconv)
    (hρ.const_mul (k : ℝ)) (contactLaw_interior hk1 hk hlam hslack htop)
  simpa only [contactLaw_rate hk] using hh

theorem strict_added_constraint_of_law {n k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ n)
    {lawWeights : ℕ → ℝ} (hlam : ValidLaw n lawWeights) {ρ : ℝ}
    (hslack : contactMarginal n lawWeights < ρ) (hlam1 : 0 < lawWeights 1)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    ∃ t, 0 ≤ t ∧ rivalRate n ρ k lawWeights < rivalObjective n ρ (k + 1) lawWeights t := by
  obtain ⟨t, ht, _, hopt, hpos⟩ := rival_optimizer_of_law hk1 (by omega) hlam hslack htop
  exact rival_added_constraint_gt hk1 hk ρ hlam.nonneg hlam1 ht.le hopt hpos

theorem eventually_event_bound_of_chernoff
    {n k : ℕ} (hk : k ≤ n) {lama : ℕ → ℕ → ℝ} {lawWeights : ℕ → ℝ}
    (hlama : ∀ a, ValidLaw n (lama a)) (hlam : ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Icc 1 n, Tendsto (fun a => lama a j) atTop (𝓝 (lawWeights j)))
    {M c : ℕ → ℕ} (hM : Tendsto M atTop atTop) {ρ θ d : ℝ}
    (hc : Tendsto (fun a => (c a : ℝ) / M a) atTop (𝓝 ρ))
    (hθ : 0 ≤ θ) (hd : d < rivalObjective n ρ k lawWeights θ) :
    ∀ᶠ a in atTop, congestProb n (M a - 1) (c a) k (lama a) ≤ exp (-d * M a) := by
  have hh := SimultaneousCongestion.eventually_exp_upper_full_population
    (K := selected n k) (contactLaw_mass_tendsto hlama hlam hconv) hM hc hθ
    (show d < FiniteCramer.objective (contactLaw n lawWeights hlam)
      (SimultaneousCongestion.count (selected n k)) ((selected n k).card * ρ) θ by
        simpa only [FiniteCramer.objective, contactLaw_cgf, card_selected hk,
          rivalObjective] using hd)
  simpa only [contactLaw_congestionProb, congestProb, card_selected hk] using hh

theorem ample_event_rate_compact
    {A : Type*} [MetricSpace A] {C : Set A} (hC : IsCompact C)
    {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (lawWeights : A → ℕ → ℝ) (ρ : A → ℝ)
    (hlam : ∀ p, ValidLaw n (lawWeights p))
    (hcont : ∀ j ∈ Icc 1 n, ContinuousOn (fun p => lawWeights p j) C)
    (hρ : ContinuousOn ρ C)
    (hslack : ∀ p ∈ C, contactMarginal n (lawWeights p) < ρ p)
    (htop : ∀ p ∈ C, ∃ j ∈ Icc 1 n,
      0 < lawWeights p j ∧ (k : ℝ) * ρ p < (min k j : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ p ∈ C, ∀ N ≥ N₀, ∀ c : ℕ,
      |(c : ℝ) / N - ρ p| < δ →
      0 < congestProb n N c k (lawWeights p) ∧
      |-log (congestProb n N c k (lawWeights p)) / N - rivalRate n (ρ p) k (lawWeights p)| < ε := by
  have hK : (selected n k).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_selected hk]
    omega
  have hm (S : Finset (Fin n)) : ContinuousOn (fun p => (contactLaw n (lawWeights p) (hlam p)).mass S) C := by
    intro p hp
    exact contactLaw_mass_tendsto hlam (hlam p) (fun j hj => (hcont j hj p hp).tendsto) S
  have hi (p : A) (hp : p ∈ C) : FiniteCramer.Interior (contactLaw n (lawWeights p) (hlam p))
      (SimultaneousCongestion.count (selected n k)) ((selected n k).card * ρ p) := by
    rw [card_selected hk]
    exact contactLaw_interior hk1 hk (hlam p) (hslack p hp) (htop p hp)
  have hh := SimultaneousCongestion.compact_uniform_congestion hC
    (fun p => contactLaw n (lawWeights p) (hlam p)) ρ hK hm hρ
    (fun p _ => contactLaw_swapInvariant n (lawWeights p) (hlam p) (selected n k)) hi hε
  simpa only [contactLaw_congestionProb, card_selected hk, contactLaw_rate hk, congestProb] using hh

end FCAppendix.Ample
