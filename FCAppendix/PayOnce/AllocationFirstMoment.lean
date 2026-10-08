import FCAppendix.PayOnce.InactiveAllocationMoments

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList
variable {N n c : ℕ}

theorem allocation_mean_error_le (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] (b q : ℝ) :
    |(∫ r, allocation n c hn r b ∂μ)-q| ≤
      ∫ r, |allocation n c hn r b-q| ∂μ := by
  have hi : Integrable (fun r : Fin N → ℝ => allocation n c hn r b) μ :=
    UnitInterval.integrable μ _ (measurable_allocation_fixed_bid hn b)
      (fun r => (allocation_bounds hn r b).1) (fun r => (allocation_bounds hn r b).2)
  have he : (∫ r, allocation n c hn r b ∂μ)-q =
      ∫ r, allocation n c hn r b-q ∂μ := by
    rw [integral_sub hi (integrable_const q)]
    simp only [integral_const,probReal_univ,one_smul]
  rw [he]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun r : Fin N → ℝ => allocation n c hn r b-q)

theorem mean_coverage_tail_le_of_error (hn : 2 ≤ n)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    {b T E : ℝ} (hT : 0 < T)
    (herr : (∫ r, |allocation n c hn r b-kernel n b T| ∂μ) ≤ E) :
    (∫ r, allocation n c hn r b ∂μ) ≤ kernel n b T+E ∧
    coverage n c hn μ b ≤ (n:ℝ)*(kernel n b T+E) ∧
    ∀ s : ℝ, 0 < s → μ.real {r | s ≤ allocation n c hn r b} ≤
      (kernel n b T+E)/s := by
  let p := fun r : Fin N → ℝ => allocation n c hn r b
  have hp : Measurable p := measurable_allocation_fixed_bid hn b
  have hpb := fun r : Fin N → ℝ => allocation_bounds (c := c) hn r b
  have hi : Integrable p μ := UnitInterval.integrable μ p hp
    (fun r => (hpb r).1) (fun r => (hpb r).2)
  have he : Integrable (fun r => |p r-kernel n b T|) μ := by
    simpa only [Real.rpow_one] using
      Bayes.integrable_focal_allocation_error_rpow hn μ hT (by norm_num : (0:ℝ) ≤ 1) b
  have hmean : (∫ r, p r ∂μ) ≤ kernel n b T+E := by
    have hh := integral_mono hi ((integrable_const (kernel n b T)).add he)
      (fun r => by dsimp only [Pi.add_apply]; linarith [le_abs_self (p r-kernel n b T)])
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) he,integral_const,probReal_univ,one_smul] at hh
    linarith
  refine ⟨hmean,?_,?_⟩
  · have hh := integral_mono (integrable_success_allocation hn μ b) (hi.const_mul (n:ℝ))
      (fun r => Limit.success_le_mul (by omega) (hpb r).1 (hpb r).2)
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg n))
  · intro s hs
    have hset : MeasurableSet {r | s ≤ p r} := measurableSet_le measurable_const hp
    have hpoint : ∀ r, {q | s ≤ p q}.indicator (fun _ => s) r ≤ p r := by
      intro r
      by_cases hr : s ≤ p r
      · simpa only [Set.indicator_of_mem (show r ∈ {q | s ≤ p q} from hr)] using hr
      · simpa only [Set.indicator_of_notMem (show r ∉ {q | s ≤ p q} from hr)] using (hpb r).1
    have hh := integral_mono ((integrable_const s).indicator hset) hi hpoint
    rw [integral_indicator hset,setIntegral_const,smul_eq_mul] at hh
    exact (le_div_iff₀ hs).mpr (hh.trans hmean)

end FCAppendix.PayOnce.DummyKernel
