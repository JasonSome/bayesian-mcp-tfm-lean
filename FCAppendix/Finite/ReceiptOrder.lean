import FCAppendix.Model.Schedules

namespace FCAppendix
namespace Finite

open scoped BigOperators

noncomputable def conditionalReceipt {n : ℕ} (A : Schedule n)
    (ν : FiniteLaw (Fin n)) (b : ℝ) : ℝ :=
  ν.expect (fun K => b * A.charge (K.val + 1) / ((K.val : ℝ) + 1))

theorem conditionalReceipt_bounds {n : ℕ} (A : Schedule n) (ν : FiniteLaw (Fin n))
    (a b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ A.charge r) :
    a * b ≤ conditionalReceipt A ν b ∧ conditionalReceipt A ν b ≤ b := by
  constructor
  · apply ν.const_le_expect
    intro K
    have hden : (0 : ℝ) < (K.val : ℝ) + 1 := by positivity
    apply (le_div_iff₀ hden).mpr
    have h := ha (K.val + 1) (by omega) (by omega)
    push_cast at h
    nlinarith [mul_le_mul_of_nonneg_left h hb]
  · apply ν.expect_le_const
    intro K
    have hden : (0 : ℝ) < (K.val : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).mpr
    have h := A.upper (K.val + 1) (by omega)
    push_cast at h
    nlinarith [mul_le_mul_of_nonneg_left h hb]

variable {ι : Type*}

def Optimal (c : ℕ) (r : ι → ℝ) (S : Finset ι) : Prop :=
  S.card ≤ c ∧ ∀ T : Finset ι, T.card ≤ c → (∑ i ∈ T, r i) ≤ ∑ i ∈ S, r i

theorem optimal_fills (c : ℕ) (r : ι → ℝ) (S : Finset ι) (hS : Optimal c r S)
    (j : ι) (hj : j ∉ S) (hrj : 0 < r j) : S.card = c := by
  classical
  apply le_antisymm hS.1
  by_contra h
  have hlt : S.card < c := lt_of_not_ge h
  have hcap : (insert j S).card ≤ c := by rw [Finset.card_insert_of_notMem hj]; omega
  have hopt := hS.2 (insert j S) hcap
  rw [Finset.sum_insert hj] at hopt
  linarith

theorem optimal_swap (c : ℕ) (r : ι → ℝ) (S : Finset ι) (hS : Optimal c r S)
    (i j : ι) (hi : i ∈ S) (hj : j ∉ S) : r j ≤ r i := by
  classical
  have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcap : (insert j (S.erase i)).card ≤ c := by
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcS := hS.1
    omega
  have hopt := hS.2 (insert j (S.erase i)) hcap
  have he := Finset.sum_erase_add S r hi
  rw [Finset.sum_insert hj'] at hopt
  linarith

theorem balanced_order (c : ℕ) (b r : ι → ℝ) (a : ℝ) (S : Finset ι)
    (hS : Optimal c r S) (hlo : ∀ i, a * b i ≤ r i) (hhi : ∀ i, r i ≤ b i)
    (i j : ι) (hi : i ∈ S) (hj : j ∉ S) : a * b j ≤ b i := by
  exact le_trans (hlo j) (le_trans (optimal_swap c r S hS i j hi hj) (hhi i))

theorem included_of_few_competitors [Fintype ι] [DecidableEq ι] (c : ℕ) (r : ι → ℝ) (S : Finset ι)
    (hS : Optimal c r S) (j : ι) (hjpos : 0 < r j)
    (hfew : (Finset.univ.filter (fun i => i ≠ j ∧ r j ≤ r i)).card < c) : j ∈ S := by
  classical
  by_contra hj
  have hfill := optimal_fills c r S hS j hj hjpos
  have hsub : S ⊆ Finset.univ.filter (fun i => i ≠ j ∧ r j ≤ r i) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, optimal_swap c r S hS i j hi hj⟩
    intro hij
    subst i
    exact hj hi
  have hc := Finset.card_le_card hsub
  omega

theorem excluded_of_many_better [Fintype ι] (c : ℕ) (r : ι → ℝ) (S : Finset ι)
    (hS : Optimal c r S) (j : ι)
    (hmany : c ≤ (Finset.univ.filter (fun i => r j < r i)).card) : j ∉ S := by
  classical
  intro hj
  let T := Finset.univ.filter (fun i => r j < r i)
  have hsub : T ⊆ S.erase j := by
    intro i hi
    have hri : r j < r i := (Finset.mem_filter.mp hi).2
    have hij : i ≠ j := by intro he; subst i; exact (lt_irrefl _ hri)
    apply Finset.mem_erase.mpr
    refine ⟨hij, ?_⟩
    by_contra hnot
    have h := optimal_swap c r S hS j i hj hnot
    linarith
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hj] at hcard
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hj⟩
  have hcap := hS.1
  change c ≤ T.card at hmany
  omega

theorem expected_revenue_additive {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (receipt : ι → Ω → ℝ) (S : Finset ι) :
    ν.expect (fun ω => ∑ i ∈ S, receipt i ω) = ∑ i ∈ S, ν.expect (receipt i) :=
  ν.expect_finset_sum S receipt

end Finite
end FCAppendix
