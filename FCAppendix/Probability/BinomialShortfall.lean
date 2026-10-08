import FCAppendix.Probability.BinomialTails

namespace FCAppendix
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem expect_abs_le_sqrt (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect (fun ω => |f ω|) ≤ Real.sqrt (μ.expect (fun ω => (f ω) ^ 2)) := by
  have hs := μ.mean_sq_le (fun ω => |f ω|)
  simp only [sq_abs] at hs
  exact (Real.le_sqrt (μ.expect_nonneg (fun _ => abs_nonneg _))
    (μ.expect_nonneg (fun _ => sq_nonneg _))).mpr hs

theorem expect_shortfall_le (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => max (c - f ω) 0) ≤
      max (c - μ.expect f) 0 + Real.sqrt (μ.variance f) := by
  have h := μ.expect_mono (fun ω => show max (c - f ω) 0 ≤
      max (c - μ.expect f) 0 + |f ω - μ.expect f| from by
    apply max_le
    · have hmax := le_max_left (c - μ.expect f) 0
      have habs := neg_abs_le (f ω - μ.expect f)
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _))
  rw [μ.expect_add, μ.expect_const] at h
  exact h.trans (add_le_add (le_refl _) (μ.expect_abs_le_sqrt (fun ω => f ω - μ.expect f)))

end FiniteLaw
namespace IndependentCounts

theorem binomial_shortfall_le (m : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial m p hp0 hp1).expect (fun r => max (c - (r.val : ℝ)) 0) ≤
      max (c - m * p) 0 + Real.sqrt (m * p * (1 - p)) := by
  have h := (binomial m p hp0 hp1).expect_shortfall_le (fun r => (r.val : ℝ)) c
  change _ ≤ max (c - (binomial m p hp0 hp1).load) 0 + _ at h
  simpa only [binomial_load, binomial_variance] using h

theorem binomial_shortfall_le_sqrt (m : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (binomial m p hp0 hp1).expect (fun r => max (c - (r.val : ℝ)) 0) ≤
      max (c - m * p) 0 + Real.sqrt m / 2 := by
  apply (binomial_shortfall_le m p c hp0 hp1).trans
  apply add_le_add (le_refl _)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hs : m * p * (1 - p) ≤ (Real.sqrt m / 2) ^ 2 := by
    have he := Real.sq_sqrt hm
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩

theorem binomial_normalized_shortfall_le (m : ℕ) (hm : 0 < m)
    (p κ ρ ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hp : ρ - ε ≤ p) :
    (binomial m p hp0 hp1).expect (fun r => max ((m : ℝ) * κ - r.val) 0) / m ≤
      ε + |κ - ρ| + 1 / (2 * Real.sqrt m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmax : max ((m : ℝ) * κ - m * p) 0 ≤ m * (ε + |κ - ρ|) := by
    apply max_le
    · have hh := le_abs_self (κ - ρ)
      have hkp : κ - p ≤ ε + |κ - ρ| := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hkp hmR.le]
    · exact mul_nonneg hmR.le (add_nonneg hε (abs_nonneg _))
  have hb := binomial_shortfall_le_sqrt m p ((m : ℝ) * κ) hp0 hp1
  have hspos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hs : Real.sqrt m / 2 / m = 1 / (2 * Real.sqrt m) := by
    have he := Real.sq_sqrt hmR.le
    field_simp
    nlinarith
  calc
    _ ≤ (m * (ε + |κ - ρ|) + Real.sqrt m / 2) / m := by
      exact div_le_div_of_nonneg_right (hb.trans (add_le_add hmax (le_refl _))) hmR.le
    _ = ε + |κ - ρ| + 1 / (2 * Real.sqrt m) := by
      rw [add_div, mul_div_cancel_left₀ _ hmR.ne', hs]

end IndependentCounts
end FCAppendix
