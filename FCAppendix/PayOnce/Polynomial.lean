import FCAppendix.Probability.IndependentCounts

namespace FCAppendix
namespace PayOnce

open scoped BigOperators

noncomputable def success (n : ℕ) (p : ℝ) : ℝ := 1 - (1 - p) ^ n

noncomputable def H (n : ℕ) (p : ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, (1 - p) ^ j) / (n : ℝ)

theorem geometric_identity (n : ℕ) (p : ℝ) :
    p * (∑ j ∈ Finset.range n, (1 - p) ^ j) = success n p := by
  induction n with
  | zero => simp [success]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold success
    rw [pow_succ]
    ring

theorem H_mul (n : ℕ) (hn : 0 < n) (p : ℝ) :
    (n : ℝ) * p * H n p = success n p := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  unfold H
  calc
    _ = p * (∑ j ∈ Finset.range n, (1 - p) ^ j) := by field_simp [hn0]
    _ = _ := geometric_identity n p

@[simp] theorem H_zero (n : ℕ) (hn : 0 < n) : H n 0 = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp [H, hn0]

@[simp] theorem H_one (n : ℕ) (hn : 0 < n) : H n 1 = 1 / (n : ℝ) := by
  have hsum : (∑ j ∈ Finset.range n, (0 : ℝ) ^ j) = 1 := by
    cases n with
    | zero => omega
    | succ n => simp [Finset.sum_range_succ', zero_pow]
  simp only [H, sub_self, hsum]

theorem power_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (j : ℕ) : x ^ j ≤ y ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hxy hx (pow_nonneg (le_trans hx hxy) j)

theorem H_nonneg (n : ℕ) (p : ℝ) (hp : p ≤ 1) : 0 ≤ H n p := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j _ => pow_nonneg (sub_nonneg.mpr hp) j)
  · exact Nat.cast_nonneg n

theorem H_bounds (n : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 / (n : ℝ) ≤ H n p ∧ H n p ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 1 ≤ ∑ j ∈ Finset.range n, (1 - p) ^ j := by
    have h := Finset.single_le_sum
      (s := Finset.range n) (f := fun j => (1 - p) ^ j)
      (fun j _ => pow_nonneg (sub_nonneg.mpr hp1) j)
      (Finset.mem_range.mpr hn)
    simpa using h
  have hs1 : (∑ j ∈ Finset.range n, (1 - p) ^ j) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        simpa using power_mono (sub_nonneg.mpr hp1) (show 1 - p ≤ 1 by linarith) j
      _ = _ := by simp
  constructor
  · exact div_le_div_of_nonneg_right hs0 (le_of_lt hnR)
  · exact (div_le_one hnR).mpr hs1

theorem H_pos (n : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < H n p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_of_lt_of_le (div_pos zero_lt_one hnR) (H_bounds n hn p hp0 hp1).1

theorem H_antitone (n : ℕ) (p q : ℝ) (hpq : p ≤ q) (hq : q ≤ 1) :
    H n q ≤ H n p := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro j _
  exact power_mono (sub_nonneg.mpr hq) (by linarith) j

theorem H_strict (n : ℕ) (hn : 2 ≤ n) (p q : ℝ) (hpq : p < q) (hq : q ≤ 1) :
    H n q < H n p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (div_lt_div_iff_of_pos_right hnR).mpr
  apply Finset.sum_lt_sum
  · intro j _
    exact power_mono (sub_nonneg.mpr hq) (by linarith) j
  · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa using (show 1 - q < 1 - p by linarith)

theorem continuous_H (n : ℕ) : Continuous (H n) := by
  unfold H
  fun_prop

theorem continuous_success (n : ℕ) : Continuous (success n) := by
  unfold success
  fun_prop

theorem success_pos (n : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 < success n p := by
  rw [← H_mul n hn p]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos hnR hp0) (H_pos n hn p (le_of_lt hp0) hp1)

theorem success_le_one (n : ℕ) (p : ℝ) (hp1 : p ≤ 1) : success n p ≤ 1 := by
  unfold success
  have h := pow_nonneg (sub_nonneg.mpr hp1) n
  linarith

theorem multiplicity_identity (n : ℕ) (hn : 0 < n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (n : ℝ) * p / success n p = 1 / H n p := by
  have hS := success_pos n hn p hp0 hp1
  have hH := H_pos n hn p (le_of_lt hp0) hp1
  apply (div_eq_div_iff (ne_of_gt hS) (ne_of_gt hH)).mpr
  simpa using H_mul n hn p

theorem multiplicity_strict (n : ℕ) (hn : 2 ≤ n) (p q : ℝ)
    (hp0 : 0 < p) (hpq : p < q) (hq1 : q ≤ 1) :
    (n : ℝ) * p / success n p < (n : ℝ) * q / success n q := by
  have hn0 : 0 < n := by omega
  have hq0 : 0 < q := lt_trans hp0 hpq
  rw [multiplicity_identity n hn0 p hp0 (le_trans (le_of_lt hpq) hq1),
    multiplicity_identity n hn0 q hq0 hq1]
  have hHp := H_pos n hn0 p (le_of_lt hp0) (le_trans (le_of_lt hpq) hq1)
  have hHq := H_pos n hn0 q (le_of_lt hq0) hq1
  apply (div_lt_div_iff₀ hHp hHq).mpr
  simpa using H_strict n hn p q hpq hq1

theorem binomial_conditional_multiplicity (n : ℕ) (hn : 0 < n)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (IndependentCounts.binomial n p (le_of_lt hp0) hp1).load /
      (IndependentCounts.binomial n p (le_of_lt hp0) hp1).success = 1 / H n p := by
  rw [IndependentCounts.binomial_load, IndependentCounts.binomial_success]
  exact multiplicity_identity n hn p hp0 hp1

end PayOnce
end FCAppendix
