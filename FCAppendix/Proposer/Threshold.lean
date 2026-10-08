import FCAppendix.Proposer.ExactCapacity
import FCAppendix.PayOnce.Receipt

namespace FCAppendix
namespace Proposer

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def Threshold (p r : ι → ℝ) (lam : ℝ) : Prop :=
  (∀ i, p i = 0 → r i ≤ lam) ∧
  (∀ i, p i = 1 → lam ≤ r i) ∧
  (∀ i, 0 < p i → p i < 1 → r i = lam)

omit [Fintype ι] in
theorem coordinate_threshold (p r : ι → ℝ) (lam : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ht : Threshold p r lam) (i : ι) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (q - p i) * (r i - lam) ≤ 0 := by
  by_cases hz : p i = 0
  · have h := ht.1 i hz
    rw [hz, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hq0 (by linarith)
  by_cases ho : p i = 1
  · have h := ht.2.1 i ho
    rw [ho]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · have hl : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hz)
    have hu : p i < 1 := lt_of_le_of_ne (hp1 i) ho
    rw [ht.2.2 i hl hu, sub_self, mul_zero]

theorem threshold_linear_optimal (p r : ι → ℝ) (lam : ℝ) (c : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = c)
    (hlam : 0 ≤ lam) (ht : Threshold p r lam)
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hqsum : ∑ i, q i ≤ c) :
    (∑ i, q i * r i) ≤ ∑ i, p i * r i := by
  have hs : (∑ i, (q i - p i) * (r i - lam)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => coordinate_threshold p r lam hp0 hp1 ht i (q i) (hq0 i) (hq1 i))
  have he : (∑ i, (q i - p i) * (r i - lam)) =
      (∑ i, q i * r i) - (∑ i, p i * r i) - lam * ((∑ i, q i) - c) := by
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum]
    ring
  have hc : lam * ((∑ i, q i) - c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  rw [he] at hs
  linarith

noncomputable def marginal (μ : FiniteLaw (Finset ι)) (i : ι) : ℝ :=
  μ.prob (fun S => i ∈ S)

noncomputable def revenue (μ : FiniteLaw (Finset ι)) (r : ι → ℝ) : ℝ :=
  μ.expect (fun S => ∑ i ∈ S, r i)

theorem revenue_marginals (μ : FiniteLaw (Finset ι)) (r : ι → ℝ) :
    revenue μ r = ∑ i, marginal μ i * r i := by
  classical
  have he : ∀ S : Finset ι, (∑ i ∈ S, r i) =
      ∑ i, (if i ∈ S then (1 : ℝ) else 0) * r i := by
    intro S
    simp
  unfold revenue
  simp_rw [he]
  rw [FiniteLaw.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteLaw.expect_mul_const, marginal, FiniteLaw.prob_eq_expect]

theorem sum_marginal (μ : FiniteLaw (Finset ι)) :
    (∑ i, marginal μ i) = μ.expect (fun S => (S.card : ℝ)) := by
  classical
  unfold marginal
  simp_rw [FiniteLaw.prob_eq_expect]
  rw [← FiniteLaw.expect_finset_sum]
  apply FiniteLaw.expect_congr
  intro S
  exact Game.sum_membership_real S

theorem marginal_capacity (μ : FiniteLaw (Finset ι)) (c : ℕ)
    (hcap : ∀ S, μ.mass S ≠ 0 → S.card ≤ c) :
    (∑ i, marginal μ i) ≤ (c : ℝ) := by
  rw [sum_marginal]
  calc
    _ ≤ μ.expect (fun _ => (c : ℝ)) := by
      unfold FiniteLaw.expect
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : μ.mass S = 0
      · simp [hS]
      · exact mul_le_mul_of_nonneg_left (by beta_reduce; exact_mod_cast hcap S hS) (μ.nonneg S)
    _ = _ := μ.expect_const _

theorem implement_best_response (p r : ι → ℝ) (lam : ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = c)
    (hlam : 0 ≤ lam) (ht : Threshold p r lam) :
    ∃ μ : FiniteLaw (Finset ι),
      (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
      (∀ i, marginal μ i = p i) ∧
      (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ c) →
        revenue ν r ≤ revenue μ r) := by
  obtain ⟨μ, hμcap, hμmarg⟩ := ExactCapacity.exists_lottery p c hp0 hp1 hsum
  refine ⟨μ, hμcap, hμmarg, ?_⟩
  intro ν hνcap
  rw [revenue_marginals, revenue_marginals]
  change (∑ i, marginal ν i * r i) ≤ ∑ i, μ.prob (fun S => i ∈ S) * r i
  simp_rw [hμmarg]
  exact threshold_linear_optimal p r lam c hp0 hp1 hsum hlam ht (marginal ν)
    (fun i => ν.prob_nonneg _) (fun i => ν.prob_le_one _) (marginal_capacity ν c hνcap)

theorem unique_marginals (score : ι → ℝ → ℝ)
    (hstrict : ∀ i x y, 0 ≤ x → x < y → y ≤ 1 → score i y < score i x)
    (p q : ι → ℝ) (lam τ c : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = c)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hqsum : ∑ i, q i = c)
    (hlam : 0 ≤ lam) (hτ : 0 ≤ τ)
    (hp : Threshold p (fun i => score i (p i)) lam)
    (hq : Threshold q (fun i => score i (q i)) τ) : p = q := by
  classical
  have h1 := threshold_linear_optimal p (fun i => score i (p i)) lam c
    hp0 hp1 hpsum hlam hp q hq0 hq1 (le_of_eq hqsum)
  have h2 := threshold_linear_optimal q (fun i => score i (q i)) τ c
    hq0 hq1 hqsum hτ hq p hp0 hp1 (le_of_eq hpsum)
  have hz : 0 ≤ ∑ i, (p i - q i) * (score i (p i) - score i (q i)) := by
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib]
    linarith
  have hnonpos : ∀ i, (p i - q i) * (score i (p i) - score i (q i)) ≤ 0 := by
    intro i
    rcases lt_trichotomy (p i) (q i) with hl | he | hr
    · have hs := hstrict i (p i) (q i) (hp0 i) hl (hq1 i)
      nlinarith
    · simp [he]
    · have hs := hstrict i (q i) (p i) (hq0 i) hr (hp1 i)
      nlinarith
  funext i
  by_contra hne
  have hi : (p i - q i) * (score i (p i) - score i (q i)) < 0 := by
    rcases lt_or_gt_of_ne hne with hl | hr
    · have hs := hstrict i (p i) (q i) (hp0 i) hl (hq1 i)
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have hs := hstrict i (q i) (p i) (hq0 i) hr (hp1 i)
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hs : (∑ i, (p i - q i) * (score i (p i) - score i (q i))) < 0 := by
    calc
      _ < ∑ _i : ι, (0 : ℝ) := Finset.sum_lt_sum
        (fun j _ => hnonpos j) ⟨i, Finset.mem_univ _, hi⟩
      _ = _ := by simp
  linarith

theorem pay_once_unique (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (p q : ι → ℝ) (lam τ c : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = c)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hqsum : ∑ i, q i = c)
    (hlam : 0 ≤ lam) (hτ : 0 ≤ τ)
    (hp : Threshold p (fun i => b i * PayOnce.H n (p i)) lam)
    (hq : Threshold q (fun i => b i * PayOnce.H n (q i)) τ) : p = q := by
  apply unique_marginals (fun i x => b i * PayOnce.H n x) _
    p q lam τ c hp0 hp1 hpsum hq0 hq1 hqsum hlam hτ hp hq
  intro i x y _ hxy hy
  exact PayOnce.receipt_strict n hn (b i) x y (hb i) hxy hy

end Proposer
end FCAppendix
