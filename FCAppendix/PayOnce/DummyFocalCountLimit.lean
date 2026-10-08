import FCAppendix.PayOnce.DummyInterimKernel
import FCAppendix.PayOnce.FocalCountLimit

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent

theorem countMass_tendsto_of_allocation_kernel_error
    (N c : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n)
    (P : ∀ t, Measure (Fin (N t) → ℝ)) [∀ t, IsProbabilityMeasure (P t)]
    {L : ℝ} (hL : 0 < L) (x : ℕ → ℝ) {x₀ : ℝ}
    (hxx : Tendsto x atTop (𝓝 x₀))
    (herr : Tendsto (fun t => ∫ r, |allocation n (c t) hn r (x t)-kernel n (x t) L|
      ∂P t) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun t => ∫ r, ManyProposers.binomialMass n (allocation n (c t) hn r (x t)) j
      ∂P t) atTop (𝓝 (ManyProposers.binomialMass n (kernel n x₀ L) j)) := by
  have hzero : Tendsto (fun t => (∫ r, ManyProposers.binomialMass n (allocation n (c t) hn r (x t)) j
      ∂P t)-ManyProposers.binomialMass n (kernel n (x t) L) j) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun _ => abs_nonneg _) _ (by
      simpa only [mul_zero] using herr.const_mul ((n.choose j:ℝ)*((j:ℝ)+(n-j:ℕ))))
    intro t
    exact AnalyticalKernel.integral_binomialMass_error_le (P t) n j _
      (measurable_allocation_fixed_bid hn (x t))
      (fun r => allocation_bounds hn r (x t)) (kernel_bounds hn hL (x t))
  have hs := (ManyProposers.continuous_binomialMass n j).continuousAt.tendsto.comp
    ((continuous_kernel_bid hn hL).continuousAt.tendsto.comp hxx)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hzero.add hs

end FCAppendix.PayOnce.DummyKernel
