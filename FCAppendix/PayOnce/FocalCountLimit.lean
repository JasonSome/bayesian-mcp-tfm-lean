import FCAppendix.PayOnce.FocalAllocationLimit
import FCAppendix.PayOnce.BinomialContinuity

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelTailEvent

theorem integral_binomialMass_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n j : ℕ)
    (p : Ω → ℝ) (hp : Measurable p) (hpb : ∀ z, p z ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    |(∫ z, ManyProposers.binomialMass n (p z) j ∂P)-ManyProposers.binomialMass n q j| ≤
      ((n.choose j:ℝ)*((j:ℝ)+(n-j:ℕ)))*(∫ z, |p z-q| ∂P) := by
  have hpi := UnitInterval.integrable P p hp (fun z => (hpb z).1) (fun z => (hpb z).2)
  have hfi := UnitInterval.integrable P (fun z => ManyProposers.binomialMass n (p z) j)
    ((ManyProposers.continuous_binomialMass n j).measurable.comp hp)
    (fun z => (ManyProposers.binomialMass_bounds n j (hpb z)).1)
    (fun z => (ManyProposers.binomialMass_bounds n j (hpb z)).2)
  have he : (∫ z, ManyProposers.binomialMass n (p z) j ∂P)-ManyProposers.binomialMass n q j =
      ∫ z, ManyProposers.binomialMass n (p z) j-ManyProposers.binomialMass n q j ∂P := by
    rw [integral_sub hfi (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono ((hfi.sub (integrable_const _)).abs)
    (((hpi.sub (integrable_const q)).abs).const_mul ((n.choose j:ℝ)*((j:ℝ)+(n-j:ℕ))))
    (fun z => ManyProposers.binomialMass_abs_sub_le n j (hpb z) hq)
  simpa only [Pi.sub_apply,integral_const_mul] using hh

theorem countMass_tendsto_of_allocation_kernel_error
    (N c : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n)
    (hc : ∀ t, c t ≤ Fintype.card (Fin (N t))+1)
    (P : ∀ t, Measure (Fin (N t) → ℝ)) [∀ t, IsProbabilityMeasure (P t)]
    {L : ℝ} (hL : 0 < L) (x : ℕ → ℝ) (hx : ∀ t, 0 < x t) {x₀ : ℝ}
    (hxx : Tendsto x atTop (𝓝 x₀))
    (herr : Tendsto (fun t => ∫ r, |allocation n (c t) hn (hc t) r (x t)-kernel n (x t) L|
      ∂P t) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun t => ∫ r, ManyProposers.binomialMass n (allocation n (c t) hn (hc t) r (x t)) j
      ∂P t) atTop (𝓝 (ManyProposers.binomialMass n (kernel n x₀ L) j)) := by
  have hzero : Tendsto (fun t => (∫ r, ManyProposers.binomialMass n (allocation n (c t) hn (hc t) r (x t)) j
      ∂P t)-ManyProposers.binomialMass n (kernel n (x t) L) j) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun _ => abs_nonneg _) _ (by
      simpa only [mul_zero] using herr.const_mul ((n.choose j:ℝ)*((j:ℝ)+(n-j:ℕ))))
    intro t
    exact integral_binomialMass_error_le (P t) n j _ (measurable_allocation_rivals hn (hc t) (hx t))
      (fun r => allocation_bounds hn (hc t) r (x t)) (kernel_bounds hn hL (x t))
  have hs := (ManyProposers.continuous_binomialMass n j).continuousAt.tendsto.comp
    ((continuous_kernel_bid hn hL).continuousAt.tendsto.comp hxx)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hzero.add hs

end FCAppendix.PayOnce.AnalyticalKernel
