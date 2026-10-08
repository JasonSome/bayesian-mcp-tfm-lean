import FCAppendix.Finite.Envelope
import FCAppendix.Probability.CountLimits

noncomputable section

namespace FCAppendix.CountLaw

lemma prob_nonzero_eq_success {n : ℕ} (μ : CountLaw n) :
    μ.prob (fun k => k.val ≠ 0) = μ.success := by
  unfold FiniteLaw.prob success
  apply μ.expect_congr
  intro k
  by_cases hk : k.val = 0 <;> simp [successIndicator, hk]

end FCAppendix.CountLaw

namespace FCAppendix.Interim.Problem

open Filter Topology

variable {n : ℕ}

theorem upper_secant_tendsto_zero_below_cutoff
    (P : ℕ → Interim.Problem n) (v g p : ℝ) (hvp : v - g < p)
    (hU : ∀ w, Tendsto (fun r => (P r).envelope w) atTop (𝓝 (max (w - g - p) 0))) :
    Tendsto (fun r => ((P r).envelope (v + (g + p - v) / 2) - (P r).envelope v) /
      ((g + p - v) / 2)) atTop (𝓝 0) := by
  have hv : v - g - p ≤ 0 := by linarith
  have hvh : v + (g + p - v) / 2 - g - p ≤ 0 := by linarith
  simpa only [max_eq_right hv, max_eq_right hvh, sub_self, zero_div] using
    ((hU (v + (g + p - v) / 2)).sub (hU v)).div_const ((g + p - v) / 2)

theorem supported_count_zero_limits_of_envelope
    (P : ℕ → Interim.Problem n) (act : ℕ → Game.JointAction n)
    (v g p : ℝ) (hvp : v - g < p)
    (hbr : ∀ r, (P r).BestResponse v (act r))
    (hU : ∀ w, Tendsto (fun r => (P r).envelope w) atTop (𝓝 (max (w - g - p) 0))) :
    Tendsto (fun r => ((P r).outcome (act r)).success) atTop (𝓝 0) ∧
    Tendsto (fun r => ((P r).outcome (act r)).load) atTop (𝓝 0) ∧
    Tendsto (fun r => ((P r).outcome (act r)).duplicates) atTop (𝓝 0) ∧
    Tendsto (fun r => ((P r).outcome (act r)).prob (fun k => k.val ≠ 0)) atTop (𝓝 0) := by
  have hh : 0 < (g + p - v) / 2 := by linarith
  have hsec := upper_secant_tendsto_zero_below_cutoff P v g p hvp hU
  have hS : Tendsto (fun r => ((P r).outcome (act r)).success) atTop (𝓝 0) :=
    squeeze_zero (fun r => CountLaw.success_nonneg _) (fun r =>
      ((P r).bestResponse_secants v ((g + p - v) / 2) hh (act r) (hbr r)).2) hsec
  have hL : Tendsto (fun r => ((P r).outcome (act r)).load) atTop (𝓝 0) := by
    apply squeeze_zero (fun r => CountLaw.load_nonneg _) (fun r => CountLaw.load_le_mul_success _)
    simpa only [mul_zero] using hS.const_mul (n : ℝ)
  have hD : Tendsto (fun r => ((P r).outcome (act r)).duplicates) atTop (𝓝 0) := by
    simpa only [CountLaw.duplicates, sub_self] using hL.sub hS
  refine ⟨hS, hL, hD, ?_⟩
  simpa only [CountLaw.prob_nonzero_eq_success] using hS

theorem all_bestResponses_count_zero_converge
    (P : ℕ → Interim.Problem n) (v g p : ℝ) (hvp : v - g < p)
    (hU : ∀ w, Tendsto (fun r => (P r).envelope w) atTop (𝓝 (max (w - g - p) 0))) :
    ∀ η > 0, ∀ᶠ r in atTop, ∀ act : Game.JointAction n,
      (P r).BestResponse v act →
      ((P r).outcome act).success < η ∧ ((P r).outcome act).load < η ∧
      ((P r).outcome act).duplicates < η ∧
      ((P r).outcome act).prob (fun k => k.val ≠ 0) < η := by
  have hh : 0 < (g + p - v) / 2 := by linarith
  let sec := fun r => ((P r).envelope (v + (g + p - v) / 2) - (P r).envelope v) /
    ((g + p - v) / 2)
  have hsec : Tendsto sec atTop (𝓝 0) := upper_secant_tendsto_zero_below_cutoff P v g p hvp hU
  have hnsec : Tendsto (fun r => (n : ℝ) * sec r) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsec.const_mul (n : ℝ)
  intro η hη
  filter_upwards [hsec.eventually (eventually_lt_nhds hη), hnsec.eventually (eventually_lt_nhds hη)]
    with r hsr hnr
  intro act hbr
  have hS := ((P r).bestResponse_secants v ((g + p - v) / 2) hh act hbr).2
  have hSl : ((P r).outcome act).success < η := hS.trans_lt hsr
  have hL : ((P r).outcome act).load < η :=
    ((CountLaw.load_le_mul_success _).trans
      (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg n))).trans_lt hnr
  have hD : ((P r).outcome act).duplicates < η := by
    have hS0 := CountLaw.success_nonneg ((P r).outcome act)
    dsimp only [CountLaw.duplicates]
    linarith
  refine ⟨hSl, hL, hD, ?_⟩
  simpa only [CountLaw.prob_nonzero_eq_success] using hSl

end FCAppendix.Interim.Problem
