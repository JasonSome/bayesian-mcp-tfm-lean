import FCAppendix.Probability.CountLaw
import FCAppendix.Probability.Bounds

namespace FCAppendix
namespace CountLaw

open Filter

variable {n : ℕ}

theorem zero_probability (μ : CountLaw n) :
    μ.prob (fun r => r.val = 0) = 1 - μ.success := by
  classical
  have h := μ.prob_compl (fun r => r.val ≠ 0)
  simpa [FiniteLaw.prob, success, successIndicator] using h

theorem multiple_probability_le_duplicates (μ : CountLaw n) :
    μ.prob (fun r => 2 ≤ r.val) ≤ μ.duplicates := by
  classical
  rw [duplicates_eq_expect]
  apply μ.expect_mono
  intro r
  by_cases hz : r.val = 0
  · simp [hz, successIndicator]
  by_cases ho : r.val = 1
  · simp [ho, successIndicator]
  · have hr : (2 : ℝ) ≤ r.val := by exact_mod_cast (show 2 ≤ r.val by omega)
    simp only [if_pos (show 2 ≤ r.val by omega), successIndicator, if_neg hz]
    linarith

theorem not_one_probability_bound (μ : CountLaw n) :
    μ.prob (fun r => r.val ≠ 1) ≤ 1 - μ.success + μ.duplicates := by
  have hsub : μ.prob (fun r => r.val ≠ 1) ≤
      μ.prob (fun r => r.val = 0 ∨ 2 ≤ r.val) := by
    apply μ.prob_mono
    intro r hr
    omega
  have hu := μ.prob_union_le (fun r => r.val = 0) (fun r => 2 ≤ r.val)
  rw [zero_probability] at hu
  have hd := μ.multiple_probability_le_duplicates
  linarith

theorem tendsto_unit_count (μ : ℕ → CountLaw n)
    (hS : Tendsto (fun m => (μ m).success) atTop (nhds 1))
    (hD : Tendsto (fun m => (μ m).duplicates) atTop (nhds 0)) :
    Tendsto (fun m => (μ m).prob (fun r => r.val ≠ 1)) atTop (nhds 0) := by
  have he : Tendsto (fun m => 1 - (μ m).success + (μ m).duplicates) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hS).add hD
  exact squeeze_zero (fun m => (μ m).prob_nonneg _) (fun m => (μ m).not_one_probability_bound) he

theorem route_count_transfer {Ω : Type*} [Fintype Ω]
    (μ : ℕ → FiniteLaw Ω) (k K : ℕ → Ω → ℕ) (j : ℕ) (π : ℝ)
    (hc : Tendsto (fun m => (μ m).prob (fun ω => k m ω ≠ K m ω)) atTop (nhds 0))
    (hk : Tendsto (fun m => (μ m).prob (fun ω => k m ω = j)) atTop (nhds π)) :
    Tendsto (fun m => (μ m).prob (fun ω => K m ω = j)) atTop (nhds π) := by
  have habs : Tendsto
      (fun m => |(μ m).prob (fun ω => K m ω = j) - (μ m).prob (fun ω => k m ω = j)|)
      atTop (nhds 0) := by
    apply squeeze_zero (fun m => abs_nonneg _)
    · intro m
      have h := (μ m).coupling_event_bound (K m) (k m) j
      simpa [ne_comm] using h
    · exact hc
  have hdiff : Tendsto
      (fun m => (μ m).prob (fun ω => K m ω = j) - (μ m).prob (fun ω => k m ω = j))
      atTop (nhds 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have h := hdiff.add hk
  simpa using h

end CountLaw
end FCAppendix
