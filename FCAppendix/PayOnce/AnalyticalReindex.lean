import FCAppendix.PayOnce.KernelAgreement

noncomputable section
namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set CommonList
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem allocation_comp_equiv (e : κ ≃ ι) {n c : ℕ} (hn : 2 ≤ n)
    (hcι : c ≤ Fintype.card ι + 1) (hcκ : c ≤ Fintype.card κ + 1)
    (rivals : ι → ℝ) (b : ℝ) :
    allocation n c hn hcκ (fun j => rivals (e j)) b = allocation n c hn hcι rivals b := by
  have he : (∀ j, 0 < rivals (e j)) ↔ ∀ j, 0 < rivals j := by
    constructor
    · intro h j
      simpa only [e.apply_symm_apply] using h (e.symm j)
    · intro h j
      exact h (e j)
  by_cases h : 0 < b ∧ ∀ j, 0 < rivals j
  · obtain ⟨L, hL, hval, hcap⟩ := allocation_root hn hcι rivals h.2 h.1
    rw [hval]
    apply allocation_eq_kernel hn hcκ _ (he.mpr h.2) h.1 hL
    rw [e.sum_comp (fun j => kernel n (rivals j) L)]
    exact hcap
  · simp only [allocation, he, dif_neg h]

theorem coverage_equiv (e : κ ≃ ι) {n c : ℕ} (hn : 2 ≤ n)
    (hcι : c ≤ Fintype.card ι + 1) (hcκ : c ≤ Fintype.card κ + 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    coverage n c hn hcκ (Measure.pi (fun _ : κ => G)) b =
      coverage n c hn hcι (Measure.pi (fun _ : ι => G)) b := by
  have hm := measurePreserving_piCongrLeft (fun _ : κ => G) e.symm
  have hh := hm.integral_comp' (fun rivals : κ → ℝ =>
    success n (allocation n c hn hcκ rivals b))
  unfold coverage
  rw [← hh]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun rivals => by
    apply congrArg (success n)
    have heval : (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e.symm) rivals =
        fun j => rivals (e j) := by
      funext j
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [heval]
    exact allocation_comp_equiv e hn hcι hcκ rivals b

end FCAppendix.PayOnce.AnalyticalKernel
