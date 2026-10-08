import FCAppendix.PayOnce.Polynomial

namespace FCAppendix
namespace IndependentCounts

theorem binomial_generating (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    (binomial n p hp0 hp1).expect (fun r => z ^ r.val) = (1 - p + p * z) ^ n := by
  induction n with
  | zero => simp [binomial, independentCount]
  | succ n ih =>
    rw [expect_binomial_succ]
    simp only [val_add_false, val_add_true, pow_add, pow_one]
    rw [FiniteLaw.expect_const_mul, ih]
    ring

theorem expect_binomial_zero (n : ℕ) (h0 : (0 : ℝ) ≤ 0) (h1 : (0 : ℝ) ≤ 1)
    (f : ℕ → ℝ) : (binomial n 0 h0 h1).expect (fun r => f r.val) = f 0 := by
  induction n with
  | zero => simp [binomial, independentCount]
  | succ n ih =>
    rw [expect_binomial_succ]
    simpa using ih

theorem size_bias (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : ℕ → ℝ) :
    (binomial (n + 1) p hp0 hp1).expect (fun r => (r.val : ℝ) * f r.val) =
      ((n : ℝ) + 1) * p * (binomial n p hp0 hp1).expect (fun r => f (r.val + 1)) := by
  induction n generalizing f with
  | zero =>
    rw [expect_binomial_succ]
    simp [binomial, independentCount]
  | succ n ih =>
    let μ := binomial n p hp0 hp1
    let ν := binomial (n + 1) p hp0 hp1
    have hb : ν.expect (fun r => f (r.val + 1)) =
        (1 - p) * μ.expect (fun r => f (r.val + 1)) +
          p * μ.expect (fun r => f (r.val + 2)) := by
      dsimp [ν, μ]
      rw [expect_binomial_succ]
      simp only [val_add_false, val_add_true]
      congr 2
      apply FiniteLaw.expect_congr
      intro r
      congr 1
      omega
    have hshift : ν.expect (fun r => ((r.val : ℝ) + 1) * f (r.val + 1)) =
        ((n : ℝ) + 1) * p * μ.expect (fun r => f (r.val + 2)) +
          ν.expect (fun r => f (r.val + 1)) := by
      calc
        _ = ν.expect (fun r => (r.val : ℝ) * f (r.val + 1)) +
              ν.expect (fun r => f (r.val + 1)) := by
          rw [← FiniteLaw.expect_add]
          apply FiniteLaw.expect_congr
          intro r
          ring
        _ = _ := by
          rw [ih (fun k => f (k + 1))]
    rw [expect_binomial_succ]
    have htrue : (fun r : Fin (n + 2) => ((addCount (n + 1) true r).val : ℝ) *
        f (addCount (n + 1) true r).val) =
        (fun r : Fin (n + 2) => ((r.val : ℝ) + 1) * f (r.val + 1)) := by
      funext r
      simp [add_comm]
    rw [htrue]
    simp only [val_add_false]
    rw [ih f, hshift]
    change (1 - p) * (((n : ℝ) + 1) * p * μ.expect (fun r => f (r.val + 1))) +
      p * (((n : ℝ) + 1) * p * μ.expect (fun r => f (r.val + 2)) +
        ν.expect (fun r => f (r.val + 1))) = _
    rw [hb]
    push_cast
    ring

end IndependentCounts
namespace PayOnce

theorem balanced_receipt (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (IndependentCounts.binomial n p hp0 hp1).expect
      (fun r => 1 / ((r.val : ℝ) + 1)) = H (n + 1) p := by
  by_cases hp : p = 0
  · subst p
    rw [IndependentCounts.expect_binomial_zero n hp0 hp1 (fun k => 1 / ((k : ℝ) + 1))]
    simp [H_zero (n + 1) (by omega)]
  · have hp' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcoef : ((n : ℝ) + 1) * p ≠ 0 := ne_of_gt (mul_pos hn0 hp')
    have hb := IndependentCounts.size_bias n p hp0 hp1 (fun k => 1 / (k : ℝ))
    have hleft : (IndependentCounts.binomial (n + 1) p hp0 hp1).expect
        (fun r => (r.val : ℝ) * (1 / (r.val : ℝ))) = success (n + 1) p := by
      calc
        _ = (IndependentCounts.binomial (n + 1) p hp0 hp1).success := by
          apply FiniteLaw.expect_congr
          intro r
          by_cases hz : r.val = 0
          · simp [hz, successIndicator]
          · have hr : (r.val : ℝ) ≠ 0 := by exact_mod_cast hz
            simp [successIndicator, hz, hr]
        _ = _ := IndependentCounts.binomial_success _ _ _ _
    rw [hleft] at hb
    have hh := H_mul (n + 1) (by omega) p
    simp only [Nat.cast_add, Nat.cast_one] at hb hh
    exact (mul_left_cancel₀ hcoef) (hb.symm.trans hh.symm)

theorem receipt_strict (n : ℕ) (hn : 2 ≤ n) (b p q : ℝ)
    (hb : 0 < b) (hpq : p < q) (hq : q ≤ 1) : b * H n q < b * H n p :=
  mul_lt_mul_of_pos_left (H_strict n hn p q hpq hq) hb

end PayOnce
end FCAppendix
