import FCAppendix.Exclusive.Kernel
import FCAppendix.Probability.UnitInterval

namespace FCAppendix
namespace Exclusive

open MeasureTheory

theorem binomial_duplicate_lower (n : ℕ) (hn : 0 < n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((n : ℝ) - 1) * p ^ 2 ≤ (n : ℝ) * p - PayOnce.success n p := by
  have h := (IndependentCounts.binomial n p hp0 hp1).factorial_le_n_duplicates
  rw [IndependentCounts.binomial_factorial, CountLaw.duplicates,
    IndependentCounts.binomial_load, IndependentCounts.binomial_success] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 ≤
    (n : ℝ) * ((n : ℝ) * p - PayOnce.success n p) at h
  exact le_of_mul_le_mul_left (by linarith) hnR

theorem mixture_duplicate_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) - 1) * (∫ ω, p ω ∂μ) ^ 2 ≤
      (n : ℝ) * (∫ ω, p ω ∂μ) - ∫ ω, PayOnce.success n (p ω) ∂μ := by
  have hpint := UnitInterval.integrable μ p hp hp0 hp1
  have hsint := UnitInterval.integrable_success μ p hp hp0 hp1 n
  have hsqint := UnitInterval.integrable_pow μ p hp hp0 hp1 2
  have hpoint : ∀ ω, ((n : ℝ) - 1) * (p ω) ^ 2 ≤
      (n : ℝ) * p ω - PayOnce.success n (p ω) :=
    fun ω => binomial_duplicate_lower n hn (p ω) (hp0 ω) (hp1 ω)
  have h := integral_mono (hsqint.const_mul ((n : ℝ) - 1))
    ((hpint.const_mul (n : ℝ)).sub hsint) hpoint
  rw [integral_const_mul] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hpint.const_mul (n : ℝ)) hsint, integral_const_mul] at h
  have hsq := UnitInterval.pow_mean_le μ p hp hp0 hp1 2
  have hnR : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hsq hnR) h

theorem coverage_quadratic (n h Q D mean : ℝ)
    (hn : 1 ≤ n) (hh : 0 < h) (hQ : 0 ≤ Q) (_hmean : 0 ≤ mean)
    (hload : Q ≤ n * h * mean) (hdup : h * (n - 1) * mean ^ 2 ≤ D) :
    (n - 1) * Q ^ 2 / (n ^ 2 * h) ≤ D := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hsq : Q ^ 2 ≤ (n * h * mean) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hn0) (le_of_lt hh)]
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ n - 1 by linarith)
  have hbound := mul_le_mul_of_nonneg_left hdup (show 0 ≤ n ^ 2 * h by positivity)
  apply (div_le_iff₀ (show 0 < n ^ 2 * h by positivity)).mpr
  nlinarith

end Exclusive
end FCAppendix
