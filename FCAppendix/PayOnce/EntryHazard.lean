import FCAppendix.PayOnce.EntryDerivativeLower
import FCAppendix.Probability.LocalTailHazard

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set RareSuccessSlope EntryDerivativeLower
variable {ι : Type*} [Fintype ι]

theorem coverage_le_nat_mul_mean_allocation {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (b : ℝ) :
    coverage n c hn μ b ≤ (n:ℝ)*(∫ r, allocation n c hn r b ∂μ) := by
  have hp := UnitInterval.integrable μ _ (measurable_allocation_fixed_bid hn b)
    (fun r => (allocation_bounds (c := c) hn r b).1)
    (fun r => (allocation_bounds (c := c) hn r b).2)
  have hh := integral_mono (integrable_success_allocation hn μ b) (hp.const_mul (n:ℝ))
    (fun r => BoundedEndpoint.success_le_nat_mul n (allocation_bounds hn r b).2)
  simpa only [coverage,integral_const_mul] using hh

universe u

theorem exists_entry_hazard_cutoff {n : ℕ} (hn : 2 ≤ n) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ {ι : Type u} [Fintype ι] (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
        (c : ℕ) (b bhi : ℝ), 0 < b → b ≤ bhi →
        (∀ᵐ r ∂μ, RegularClearing n c r b) →
        ∀ η ∈ Ioc (0:ℝ) η₀, ∀ rate A : ℝ, 0 < rate → 0 ≤ A →
          0 < μ.real {r | 0 < allocation n c hn r b} →
          (∀ s ∈ Ioc (0:ℝ) η,
            μ.real {r | s ≤ allocation n c hn r b}/
              μ.real {r | 0 < allocation n c hn r b} ≤ A*Real.exp (-rate*s)) →
          A*Real.exp (-rate*η) ≤ 1/2 →
          HasDerivAt (coverage n c hn μ) (deriv (coverage n c hn μ) b) b ∧
          0 < deriv (coverage n c hn μ) b ∧
          coverage n c hn μ b/deriv (coverage n c hn μ) b ≤
            (n:ℝ)*A*(1+1/η)/((entrySlopeConstant n/(2*bhi))*rate) := by
  obtain ⟨η₀,hη₀,hη₀1,hC,hcutoff⟩ := exists_entry_deriv_cutoff.{u} hn
  refine ⟨η₀,hη₀,hη₀1,?_⟩
  intro ι _ μ _ c b bhi hb hbhi hreg η hη rate A hrate hA hF htail habs
  have hd := hcutoff μ c b hb hreg η hη
  have hsmall : μ.real {r | η ≤ allocation n c hn r b} ≤
      μ.real {r | 0 < allocation n c hn r b}/2 := by
    have hh := (div_le_iff₀ hF).mp ((htail η ⟨hη.1,le_rfl⟩).trans habs)
    linarith
  have hD := absorb_bad_mass hC hb hbhi hF.le hsmall hd.2
  have hc : 0 < entrySlopeConstant n/(2*bhi) :=
    div_pos hC (mul_pos (by norm_num) (hb.trans_le hbhi))
  have hDp : 0 < deriv (coverage n c hn μ) b := (mul_pos hc hF).trans_le hD
  refine ⟨hd.1,hDp,?_⟩
  apply Probability.hazard_ratio_le_of_local_allocation_tail μ
    (measurable_allocation_fixed_bid hn b) (fun r => allocation_bounds hn r b)
    hA hrate hη.1 hc hF ?_ (coverage_le_nat_mul_mean_allocation hn μ b) hD
  intro s hs
  calc
    μ.real {r | s ≤ allocation n c hn r b} ≤
        (A*Real.exp (-rate*s))*μ.real {r | 0 < allocation n c hn r b} :=
      (div_le_iff₀ hF).mp (htail s hs)
    _ = A*μ.real {r | 0 < allocation n c hn r b}*Real.exp (-rate*s) := by ring

end FCAppendix.PayOnce.DummyKernel
