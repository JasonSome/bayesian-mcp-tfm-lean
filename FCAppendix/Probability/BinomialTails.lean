import FCAppendix.Probability.IndependentCounts
import FCAppendix.Probability.Bounds

namespace FCAppendix
namespace IndependentCounts

theorem binomial_all (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).prob (fun r => r.val = n) = p ^ n := by
  classical
  induction n with
  | zero => simp [binomial, independentCount, FiniteLaw.prob]
  | succ n ih =>
    rw [FiniteLaw.prob_eq_expect]
    rw [expect_binomial_succ]
    have hf : ∀ r : Fin (n + 1),
        (if (addCount n false r).val = n + 1 then (1 : ℝ) else 0) = 0 := by
      intro r
      simp only [val_add_false]
      rw [if_neg (by omega)]
    have ht : ∀ r : Fin (n + 1),
        (if (addCount n true r).val = n + 1 then (1 : ℝ) else 0) =
          if r.val = n then 1 else 0 := by
      intro r
      simp only [val_add_true]
      by_cases h : r.val = n
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [hf, ht]
    rw [FiniteLaw.expect_zero, ← FiniteLaw.prob_eq_expect, ih, pow_succ]
    ring

theorem binomial_tail_positive (n c : ℕ) (hc : c ≤ n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 < (binomial n p (le_of_lt hp0) hp1).prob (fun r => c ≤ r.val) := by
  have h := (binomial n p (le_of_lt hp0) hp1).prob_mono
    (E := fun r => r.val = n) (F := fun r => c ≤ r.val) (by
      intro r hr
      simpa [hr] using hc)
  rw [binomial_all] at h
  exact lt_of_lt_of_le (pow_pos hp0 n) h

theorem rank_success_lt_one (n c : ℕ) (hc : c ≤ n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (binomial n p (le_of_lt hp0) hp1).prob (fun r => r.val < c) < 1 := by
  have hpos := binomial_tail_positive n c hc p hp0 hp1
  have h := (binomial n p (le_of_lt hp0) hp1).prob_compl (fun r => c ≤ r.val)
  have he : (binomial n p (le_of_lt hp0) hp1).prob (fun r => r.val < c) =
      1 - (binomial n p (le_of_lt hp0) hp1).prob (fun r => c ≤ r.val) := by
    simpa only [not_le] using h
  rw [he]
  linarith

theorem binomial_second_moment (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).expect (fun r => (r.val : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 + n * p := by
  calc
    _ = (binomial n p hp0 hp1).expect
        (fun r => (r.val : ℝ) * ((r.val : ℝ) - 1) + r.val) := by
      apply FiniteLaw.expect_congr
      intro r
      ring
    _ = (binomial n p hp0 hp1).factorialMoment + (binomial n p hp0 hp1).load := by
      rw [FiniteLaw.expect_add]
      rfl
    _ = _ := by rw [binomial_factorial, binomial_load]

theorem binomial_variance (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial n p hp0 hp1).variance (fun r => (r.val : ℝ)) = n * p * (1 - p) := by
  rw [FiniteLaw.variance_identity, binomial_second_moment]
  change _ - (binomial n p hp0 hp1).load ^ 2 = _
  rw [binomial_load]
  ring

theorem binomial_tail_chebyshev (n c : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hc : (n : ℝ) * p < c) :
    (binomial n p hp0 hp1).prob (fun r => c ≤ r.val) ≤
      (n : ℝ) * p * (1 - p) / ((c : ℝ) - n * p) ^ 2 := by
  let μ := binomial n p hp0 hp1
  have hsub : μ.prob (fun r => c ≤ r.val) ≤
      μ.prob (fun r => (c : ℝ) - n * p ≤ |(r.val : ℝ) - μ.expect (fun s => (s.val : ℝ))|) := by
    apply μ.prob_mono
    intro r hr
    have hrR : (c : ℝ) ≤ r.val := by exact_mod_cast hr
    change _ ≤ |(r.val : ℝ) - μ.load|
    rw [binomial_load]
    have habs := le_abs_self ((r.val : ℝ) - (n : ℝ) * p)
    linarith
  have h := μ.chebyshev (fun r => (r.val : ℝ)) ((c : ℝ) - n * p) (sub_pos.mpr hc)
  rw [binomial_variance] at h
  exact le_trans hsub h

end IndependentCounts
end FCAppendix
