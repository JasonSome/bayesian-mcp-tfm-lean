import FCAppendix.PayOnce.InactiveAllocationMoments
import FCAppendix.PayOnce.EntryDerivativeLower

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_lower_allocation_bounds
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b → b ≤ bar t →
      let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
      (∫ r, allocation (k+1) (C t) hn r b ∂μ) ≤ A*(M t:ℝ)^(-(1:ℝ)/2) ∧
      coverage (k+1) (C t) hn μ b ≤ ((k+1:ℕ):ℝ)*A*(M t:ℝ)^(-(1:ℝ)/2) ∧
      ∀ s : ℝ, 0 < s → μ.real {r | s ≤ allocation (k+1) (C t) hn r b} ≤
        A*(M t:ℝ)^(-(1:ℝ)/2)/s := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  obtain ⟨A,hA,he⟩ := payOnce_inactive_focal_allocation_moments Γ B F g ρ h 1 (by norm_num)
  refine ⟨A,hA,?_⟩
  filter_upwards [he] with t ht b hb hbT
  let μ := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let p := fun r : Fin (M t-1) → ℝ => allocation (k+1) (C t) hn r b
  have hp : Measurable p := measurable_allocation_fixed_bid hn b
  have hpb : ∀ r, p r ∈ Icc (0:ℝ) 1 := fun r => allocation_bounds hn r b
  have hi : Integrable p μ := UnitInterval.integrable μ p hp (fun r => (hpb r).1) (fun r => (hpb r).2)
  have hmean : (∫ r, p r ∂μ) ≤ A*(M t:ℝ)^(-(1:ℝ)/2) := by
    have hh := (ht b hb).2
    simp only [kernel_of_le (k+1) hbT,sub_zero,Real.rpow_one] at hh
    simpa only [abs_of_nonneg (allocation_bounds hn _ b).1] using hh
  refine ⟨hmean,?_,?_⟩
  · have hh := integral_mono (integrable_success_allocation hn μ b) (hi.const_mul ((k+1:ℕ):ℝ))
      (fun r => Limit.success_le_mul (by omega) (hpb r).1 (hpb r).2)
    rw [integral_const_mul] at hh
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (k+1)))
  · intro s hs
    have hset : MeasurableSet {r | s ≤ p r} := measurableSet_le measurable_const hp
    have hpoint : ∀ r, {q | s ≤ p q}.indicator (fun _ => s) r ≤ p r := by
      intro r
      by_cases hr : s ≤ p r
      · simpa only [Set.indicator_of_mem (show r ∈ {q | s ≤ p q} from hr)] using hr
      · simpa only [Set.indicator_of_notMem (show r ∉ {q | s ≤ p q} from hr)] using (hpb r).1
    have hh := integral_mono ((integrable_const s).indicator hset) hi hpoint
    rw [integral_indicator hset,setIntegral_const,smul_eq_mul] at hh
    apply (le_div_iff₀ hs).mpr
    exact hh.trans hmean

end FCAppendix.Bayes
