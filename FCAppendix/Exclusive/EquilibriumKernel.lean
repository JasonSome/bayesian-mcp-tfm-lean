import FCAppendix.Exclusive.CommonListKernel

namespace FCAppendix.Exclusive

open scoped BigOperators
open Proposer CommonList

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem equilibrium_marginals_unique (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (μ ν : FiniteLaw (Finset ι))
    (hμ : ExclusiveEquilibrium n c b μ) (hν : ExclusiveEquilibrium n c b ν) :
    marginal μ = marginal ν := by
  classical
  let p := marginal μ
  let q := marginal ν
  let r : ι → ℝ → ℝ := fun i x => b i * (1 - x) ^ (n - 1)
  have h1 := hμ.2 ν hν.1
  have h2 := hν.2 μ hμ.1
  simp only [exclusive_payoff_eq] at h1 h2
  have hz : 0 ≤ ∑ i, (p i - q i) * (r i (p i) - r i (q i)) := by
    simp only [p, q, r]
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib]
    linarith
  have hstrict (i : ι) (x y : ℝ) (hxy : x < y) (hy : y ≤ 1) :
      r i y < r i x :=
    receipt_strict (n - 1) (by omega) (b i) x y (hb i) hxy hy
  have hnonpos (i : ι) :
      (p i - q i) * (r i (p i) - r i (q i)) ≤ 0 := by
    rcases lt_trichotomy (p i) (q i) with h | h | h
    · have hs := hstrict i (p i) (q i) h (marginal_le_one ν i)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · simp only [h, sub_self, zero_mul, le_refl]
    · have hs := hstrict i (q i) (p i) h (marginal_le_one μ i)
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  funext i
  by_contra hi
  have hneg : (p i - q i) * (r i (p i) - r i (q i)) < 0 := by
    rcases lt_or_gt_of_ne hi with h | h
    · have hs := hstrict i (p i) (q i) h (marginal_le_one ν i)
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have hs := hstrict i (q i) (p i) h (marginal_le_one μ i)
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have : (∑ j, (p j - q j) * (r j (p j) - r j (q j))) < 0 := by
    calc
      _ < ∑ _j : ι, (0 : ℝ) := Finset.sum_lt_sum
        (fun j _ => hnonpos j) ⟨i, Finset.mem_univ i, hneg⟩
      _ = 0 := by simp
  linarith

theorem equilibrium_kernel (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (hc : c < Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : ExclusiveEquilibrium n c b μ) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ i, marginal μ i = demand n (b i) lam) ∧
      (∑ i, demand n (b i) lam) = c := by
  obtain ⟨lam, hlam, hroot⟩ := exists_price n hn b hb c hc
  obtain ⟨ν, _, hνcoord, hν⟩ :=
    exists_exclusive_equilibrium n hn b hb c lam hlam hroot
  have he := equilibrium_marginals_unique n hn b hb c μ ν hμ hν
  exact ⟨lam, hlam, fun i => (congrFun he i).trans (hνcoord i), hroot⟩

theorem equilibrium_unique_price (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (hc0 : 0 < c) (hc : c < Fintype.card ι) (μ : FiniteLaw (Finset ι))
    (hμ : ExclusiveEquilibrium n c b μ) :
    ∃! lam : ℝ, 0 < lam ∧
      (∀ i, marginal μ i = demand n (b i) lam) ∧
      (∑ i, demand n (b i) lam) = c := by
  obtain ⟨lam, hlam, hcoord, hroot⟩ := equilibrium_kernel n hn b hb c hc μ hμ
  obtain ⟨tau, _htau, huniq⟩ := exists_unique_price n hn b hb c hc0 hc
  refine ⟨lam, ⟨hlam, hcoord, hroot⟩, ?_⟩
  intro s hs
  exact (huniq s ⟨hs.1, hs.2.2⟩).trans (huniq lam ⟨hlam, hroot⟩).symm

theorem equilibrium_sum_marginal (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (μ : FiniteLaw (Finset ι)) (hμ : ExclusiveEquilibrium n c b μ) :
    (∑ i, marginal μ i) = (min c (Fintype.card ι) : ℕ) := by
  by_cases hc : c < Fintype.card ι
  · obtain ⟨lam, _, hcoord, hroot⟩ := equilibrium_kernel n hn b hb c hc μ hμ
    simp_rw [hcoord]
    simpa only [Nat.min_eq_left hc.le] using hroot
  · have hNc : Fintype.card ι ≤ c := Nat.le_of_not_gt hc
    rw [exclusive_small_list_unique n hn b hb c hNc μ hμ]
    simp [marginal_dirac, Nat.min_eq_right hNc]

theorem equilibrium_support_card (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (c : ℕ)
    (μ : FiniteLaw (Finset ι)) (hμ : ExclusiveEquilibrium n c b μ) :
    ∀ S, μ.mass S ≠ 0 → S.card = min c (Fintype.card ι) := by
  classical
  let C := min c (Fintype.card ι)
  have hsum := equilibrium_sum_marginal n hn b hb c μ hμ
  rw [sum_marginal] at hsum
  have hcap (S : Finset ι) (hS : μ.mass S ≠ 0) : S.card ≤ C :=
    le_min (hμ.1 S hS) (Finset.card_le_univ S)
  have hnonneg (S : Finset ι) : 0 ≤ μ.mass S * ((C : ℝ) - S.card) := by
    by_cases hS : μ.mass S = 0
    · simp [hS]
    · exact mul_nonneg (μ.nonneg S) (sub_nonneg.mpr (by exact_mod_cast hcap S hS))
  have hz : (∑ S, μ.mass S * ((C : ℝ) - S.card)) = 0 := by
    change μ.expect (fun S => (C : ℝ) - S.card) = 0
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, hsum]
    exact sub_self _
  intro S hS
  have hzS := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => hnonneg T)).mp hz
    S (Finset.mem_univ S)
  have he : (C : ℝ) = S.card := sub_eq_zero.mp ((mul_eq_zero.mp hzS).resolve_left hS)
  exact_mod_cast he.symm

theorem equilibrium_bid_formula (n : ℕ) (hn : 2 ≤ n)
    {b lam p : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    (hp : p = demand n b lam) (hp0 : 0 < p) :
    p < 1 ∧ b = lam / (1 - p) ^ (n - 1) := by
  have hp1 : p < 1 := by
    rw [hp]
    exact demand_lt_one n hb hlam
  have hdp : 0 < demand n b lam := by simpa only [← hp] using hp0
  have hlt : lam < b := (demand_pos_iff n hn hb hlam.le).mp hdp
  have he := demand_receipt n hn hb hlam
  rw [← hp, min_eq_right hlt.le] at he
  refine ⟨hp1, ?_⟩
  exact (eq_div_iff (ne_of_gt (pow_pos (sub_pos.mpr hp1) _))).mpr he

theorem equilibrium_bid_order_iff (n : ℕ) (hn : 2 ≤ n)
    {b₁ b₂ lam p₁ p₂ : ℝ} (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hlam : 0 < lam) (hp₁ : p₁ = demand n b₁ lam)
    (hp₂ : p₂ = demand n b₂ lam) (hp₁0 : 0 < p₁) (hp₂0 : 0 < p₂) :
    b₁ < b₂ ↔ p₁ < p₂ := by
  obtain ⟨hp₁1, hb₁eq⟩ := equilibrium_bid_formula n hn hb₁ hlam hp₁ hp₁0
  obtain ⟨hp₂1, hb₂eq⟩ := equilibrium_bid_formula n hn hb₂ hlam hp₂ hp₂0
  have hpow₁ : 0 < (1 - p₁) ^ (n - 1) := pow_pos (sub_pos.mpr hp₁1) _
  have hpow₂ : 0 < (1 - p₂) ^ (n - 1) := pow_pos (sub_pos.mpr hp₂1) _
  have hreceipt₁ : b₁ * (1 - p₁) ^ (n - 1) = lam :=
    (eq_div_iff (ne_of_gt hpow₁)).mp hb₁eq
  have hreceipt₂ : b₂ * (1 - p₂) ^ (n - 1) = lam :=
    (eq_div_iff (ne_of_gt hpow₂)).mp hb₂eq
  constructor
  · intro hb
    by_contra hp
    have hple : p₂ ≤ p₁ := le_of_not_gt hp
    have hpow := PayOnce.power_mono (sub_nonneg.mpr hp₁1.le)
      (show 1 - p₁ ≤ 1 - p₂ by linarith) (n - 1)
    have hmul := mul_le_mul_of_nonneg_left hpow hb₂.le
    have hstrict := mul_lt_mul_of_pos_right hb hpow₁
    nlinarith
  · intro hp
    have hpow := power_strict (sub_nonneg.mpr hp₂1.le)
      (show 1 - p₂ < 1 - p₁ by linarith) (n - 1) (by omega)
    have hlt := mul_lt_mul_of_pos_left hpow hb₁
    by_contra hb
    have hle : b₂ ≤ b₁ := le_of_not_gt hb
    have hmul := mul_le_mul_of_nonneg_right hle hpow₂.le
    nlinarith

end FCAppendix.Exclusive
