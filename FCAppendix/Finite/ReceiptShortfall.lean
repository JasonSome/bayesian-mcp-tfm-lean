import FCAppendix.Finite.ReceiptOrder

namespace FCAppendix.Finite

theorem optimal_low_card_le_shortfall {ι : Type*} [DecidableEq ι]
    (c : ℕ) (r : ι → ℝ) (S H L : Finset ι) (hS : Optimal c r S)
    (hpriority : ∀ h ∈ H, ∀ l ∈ L, r l < r h) :
    (S ∩ L).card ≤ c - H.card := by
  classical
  by_cases hne : (S ∩ L).Nonempty
  · obtain ⟨l, hl⟩ := hne
    have hH : H ⊆ S := by
      intro h hh
      by_contra hnot
      have ho := optimal_swap c r S hS l h (Finset.mem_inter.mp hl).1 hnot
      exact (not_le_of_gt (hpriority h hh l (Finset.mem_inter.mp hl).2)) ho
    have hdisj : Disjoint H (S ∩ L) := Finset.disjoint_left.mpr (by
      intro i hiH hiL
      exact (lt_irrefl (r i)) (hpriority i hiH i (Finset.mem_inter.mp hiL).2))
    have hcard := Finset.card_le_card (show H ∪ (S ∩ L) ⊆ S from
      Finset.union_subset hH Finset.inter_subset_left)
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have hc := hS.1
    omega
  · have hz : S ∩ L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hz]

theorem optimal_low_card_real_le_shortfall {ι : Type*} [DecidableEq ι]
    (c : ℕ) (r : ι → ℝ) (S H L : Finset ι) (hS : Optimal c r S)
    (hpriority : ∀ h ∈ H, ∀ l ∈ L, r l < r h) :
    ((S ∩ L).card : ℝ) ≤ max ((c : ℝ) - H.card) 0 := by
  have h := optimal_low_card_le_shortfall c r S H L hS hpriority
  by_cases hH : H.card ≤ c
  · have hR : ((S ∩ L).card : ℝ) ≤ (c - H.card : ℕ) := Nat.cast_le.mpr h
    rw [Nat.cast_sub hH] at hR
    exact hR.trans (le_max_left _ _)
  · have hz : (S ∩ L).card = 0 := by omega
    simp only [hz, Nat.cast_zero]
    exact le_max_right _ _

end FCAppendix.Finite
