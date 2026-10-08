import FCAppendix.Finite.ReceiptShortfall

namespace FCAppendix.Finite

open scoped BigOperators

theorem optimal_truncated_receipt_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ) (r : ι → ℝ) (S H : Finset ι) (hS : Optimal c r S)
    (hpos : ∀ i ∈ S, 0 ≤ r i) (t : ℝ) (ht : 0 ≤ t)
    (hH : ∀ i ∈ H, t ≤ r i) (P : ι → Prop) [DecidablePred P] :
    t * ((S.card : ℝ) - (S.filter fun i => ¬ P i).card - max ((c : ℝ) - H.card) 0) ≤
      ∑ i ∈ S, if P i then r i else 0 := by
  classical
  let L := Finset.univ.filter (fun i => r i < t)
  have hlow : ((S ∩ L).card : ℝ) ≤ max ((c : ℝ) - H.card) 0 :=
    optimal_low_card_real_le_shortfall c r S H L hS (fun h hh l hl =>
      ((Finset.mem_filter.mp hl).2).trans_le (hH h hh))
  have hpt (i : ι) (hi : i ∈ S) : t ≤ (if P i then r i else 0) +
      t * (if ¬ P i then 1 else 0) + t * (if r i < t then 1 else 0) := by
    by_cases hp : P i <;> by_cases hr : r i < t <;>
      simp only [hp, hr, not_true_eq_false, not_false_eq_true, ↓reduceIte, mul_one, mul_zero,
        add_zero, zero_add]
    · linarith [hpos i hi]
    · exact le_of_not_gt hr
    · linarith
    · exact le_rfl
  have hsum := Finset.sum_le_sum (fun i hi => hpt i hi)
  have hbad : (∑ i ∈ S, if ¬ P i then (1 : ℝ) else 0) = ((S.filter fun i => ¬ P i).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hsmall : (∑ i ∈ S, if r i < t then (1 : ℝ) else 0) = ((S ∩ L).card : ℝ) := by
    rw [← Finset.sum_filter]
    have heq : S.filter (fun i => r i < t) = S ∩ L := by ext; simp [L]
    rw [heq]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    hbad, hsmall] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hlow ht]

end FCAppendix.Finite
