import FCAppendix.Probability.FiniteLaw

namespace FCAppendix
namespace Ample

open scoped BigOperators

noncomputable def boundaryMass (n : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  h * (n.choose j : ℝ) / ((2 : ℝ) ^ n - 1)

theorem two_pow_ge_one (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

theorem boundary_denominator_pos (n : ℕ) (hn : 0 < n) : 0 < (2 : ℝ) ^ n - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have h := two_pow_ge_one k
  rw [pow_succ]
  nlinarith

theorem positive_choose_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ)) = (2 : ℝ) ^ n - 1 := by
  have hn := Nat.sum_range_choose n
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at hn
  have hr : (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ)) + 1 = (2 : ℝ) ^ n := by
    exact_mod_cast hn
  linarith

theorem positive_weighted_choose_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ)) =
      (n : ℝ) * 2 ^ (n - 1) := by
  have hn := Nat.sum_range_mul_choose n
  rw [Finset.sum_range_succ'] at hn
  simp only [Nat.zero_mul, Nat.add_zero] at hn
  exact_mod_cast hn

theorem boundaryMass_nonneg (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h) (j : ℕ) :
    0 ≤ boundaryMass n h j :=
  div_nonneg (mul_nonneg hh (Nat.cast_nonneg _)) (le_of_lt (boundary_denominator_pos n hn))

theorem boundaryMass_total (n : ℕ) (hn : 0 < n) (h : ℝ) :
    (∑ j ∈ Finset.range n, boundaryMass n h (j + 1)) = h := by
  unfold boundaryMass
  rw [← Finset.sum_div, ← Finset.mul_sum, positive_choose_sum]
  exact mul_div_cancel_right₀ h (ne_of_gt (boundary_denominator_pos n hn))

theorem boundaryMass_load (n : ℕ) (h : ℝ) :
    (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * boundaryMass n h (j + 1)) =
      h * ((n : ℝ) * 2 ^ (n - 1)) / ((2 : ℝ) ^ n - 1) := by
  calc
    _ = (∑ j ∈ Finset.range n,
        h * (((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ)) / ((2 : ℝ) ^ n - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold boundaryMass
      ring
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.mul_sum, positive_weighted_choose_sum]

theorem boundaryMass_multiplicity (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h) :
    (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * boundaryMass n h (j + 1)) /
      (∑ j ∈ Finset.range n, boundaryMass n h (j + 1)) =
      (n : ℝ) * 2 ^ (n - 1) / ((2 : ℝ) ^ n - 1) := by
  rw [boundaryMass_total n hn, boundaryMass_load]
  field_simp [ne_of_gt hh]

end Ample
end FCAppendix
