import FCAppendix.Proposer.Threshold
import FCAppendix.Probability.CountLimits

namespace FCAppendix
namespace Exclusive

open scoped BigOperators

theorem power_strict {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (n : ℕ) (hn : 0 < n) :
    x ^ n < y ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  calc
    x ^ (k + 1) = x ^ k * x := pow_succ _ _
    _ ≤ y ^ k * x := mul_le_mul_of_nonneg_right (PayOnce.power_mono hx (le_of_lt hxy) k) hx
    _ < y ^ k * y := mul_lt_mul_of_pos_left hxy (pow_pos hy k)
    _ = y ^ (k + 1) := (pow_succ _ _).symm

theorem exclusive_receipt (n : ℕ) (p b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    b * (IndependentCounts.binomial n p hp0 hp1).prob (fun r => r.val = 0) =
      b * (1 - p) ^ n := by
  rw [CountLaw.zero_probability, IndependentCounts.binomial_success]
  ring

theorem receipt_strict (n : ℕ) (hn : 0 < n) (b p q : ℝ)
    (hb : 0 < b) (hpq : p < q) (hq : q ≤ 1) :
    b * (1 - q) ^ n < b * (1 - p) ^ n := by
  apply mul_lt_mul_of_pos_left _ hb
  exact power_strict (sub_nonneg.mpr hq) (by linarith) n hn

theorem unique_marginals {ι : Type*} [Fintype ι] (n : ℕ) (hn : 2 ≤ n)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (p q : ι → ℝ) (lam τ c : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hpsum : ∑ i, p i = c)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (hqsum : ∑ i, q i = c)
    (hlam : 0 ≤ lam) (hτ : 0 ≤ τ)
    (hp : Proposer.Threshold p (fun i => b i * (1 - p i) ^ (n - 1)) lam)
    (hq : Proposer.Threshold q (fun i => b i * (1 - q i) ^ (n - 1)) τ) : p = q := by
  apply Proposer.unique_marginals (fun i x => b i * (1 - x) ^ (n - 1)) _
    p q lam τ c hp0 hp1 hpsum hq0 hq1 hqsum hlam hτ hp hq
  intro i x y _ hxy hy
  exact receipt_strict (n - 1) (by omega) (b i) x y (hb i) hxy hy

end Exclusive
end FCAppendix
