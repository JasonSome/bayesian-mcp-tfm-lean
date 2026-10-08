import FCAppendix.Probability.FiniteLaw

namespace FCAppendix
namespace FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem abs_expect_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  apply abs_le.mpr
  constructor
  · have h := μ.expect_mono (fun ω => neg_abs_le (f ω))
    have hn : μ.expect (fun ω => -|f ω|) = - μ.expect (fun ω => |f ω|) := by
      calc
        _ = μ.expect (fun ω => (-1) * |f ω|) := by simp
        _ = _ := by rw [μ.expect_const_mul]; ring
    rw [hn] at h
    exact h
  · exact μ.expect_mono (fun ω => le_abs_self (f ω))

theorem abs_prob_sub_le (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    |μ.prob E - μ.prob F| ≤ μ.prob (fun ω => ¬ (E ω ↔ F ω)) := by
  classical
  rw [prob, prob, ← μ.expect_sub]
  calc
    _ ≤ μ.expect (fun ω => |(if E ω then (1 : ℝ) else 0) -
        (if F ω then (1 : ℝ) else 0)|) := μ.abs_expect_le _
    _ = _ := by
      apply μ.expect_congr
      intro ω
      by_cases he : E ω <;> by_cases hf : F ω <;> simp [he, hf]

theorem coupling_event_bound {ι : Type*} (μ : FiniteLaw Ω) (X Y : Ω → ι) (i : ι) :
    |μ.prob (fun ω => X ω = i) - μ.prob (fun ω => Y ω = i)| ≤
      μ.prob (fun ω => X ω ≠ Y ω) := by
  apply le_trans (μ.abs_prob_sub_le _ _)
  apply μ.prob_mono
  intro ω hxy heq
  apply hxy
  simp [heq]

theorem markov (μ : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (t : ℝ) : t * μ.prob (fun ω => t ≤ f ω) ≤ μ.expect f := by
  classical
  change t * μ.expect (fun ω => if t ≤ f ω then (1 : ℝ) else 0) ≤ _
  rw [← μ.expect_const_mul]
  apply μ.expect_mono
  intro ω
  by_cases h : t ≤ f ω
  · simp [h]
  · simpa [h] using hf ω

noncomputable def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => (f ω - μ.expect f) ^ 2)

theorem variance_identity (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f = μ.expect (fun ω => (f ω) ^ 2) - (μ.expect f) ^ 2 := by
  unfold variance
  calc
    _ = μ.expect (fun ω => (f ω) ^ 2 - (2 * μ.expect f) * f ω + (μ.expect f) ^ 2) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = _ := by
      rw [μ.expect_add, μ.expect_sub, μ.expect_const_mul, μ.expect_const]
      ring

theorem chebyshev (μ : FiniteLaw Ω) (f : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    μ.prob (fun ω => t ≤ |f ω - μ.expect f|) ≤ μ.variance f / t ^ 2 := by
  have hevent : μ.prob (fun ω => t ≤ |f ω - μ.expect f|) ≤
      μ.prob (fun ω => t ^ 2 ≤ (f ω - μ.expect f) ^ 2) := by
    apply μ.prob_mono
    intro ω h
    have ha := abs_nonneg (f ω - μ.expect f)
    have hs := sq_abs (f ω - μ.expect f)
    nlinarith
  have hm := μ.markov (fun ω => (f ω - μ.expect f) ^ 2)
    (fun ω => sq_nonneg _) (t ^ 2)
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have hs := mul_le_mul_of_nonneg_left hevent (sq_nonneg t)
  change _ ≤ μ.variance f at hm
  nlinarith

end FiniteLaw
end FCAppendix
