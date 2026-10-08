import FCAppendix.PayOnce.InactiveCentralMean
import FCAppendix.PayOnce.InactiveCentralDerivative
import FCAppendix.Probability.CompactSequentialUniform

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_derivative_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => deriv (coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))))
        (inactiveGaussianPrice Γ F g ρ (y t) t)) atTop
      (𝓝 ((2*((k+1:ℕ):ℝ)/((((k+1:ℕ):ℝ)-1)*
        Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))*cdf (gaussianReal 0 1) z)) := by
  apply payOnce_inactive_central_coverage_derivative Γ B F g ρ h hlocal _
    (payOnce_inactive_gaussian_bid_tendsto Γ B F g ρ h y hy)
  apply hy.congr'
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  rw [add_sub_cancel_left,mul_div_cancel_left₀ _ hs.ne']

theorem payOnce_inactive_central_test_mean_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {D : ℝ}
    (hD : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ D)
    {d K : ℝ} (hK : 0 ≤ K) (hquad : ∀ p ∈ Icc (0:ℝ) 1, |ψ p-d*p| ≤ K*p^2)
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0<ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := d*(2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    ∀ᶠ t in atTop, ∀ y ∈ S,
      |(∫ r, ψ (allocation (k+1) (C t) hn r (inactiveGaussianPrice Γ F g ρ y t))
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))/
          inactiveGaussianScale M F (k+1) g ρ t-a*gaussianSuccessPrimitive y| < ε := by
  dsimp only
  apply eventually_uniform_abs_lt_of_compact_sequences hS _ _ ?_ ?_ hε
  · exact ((continuous_iff_continuousAt.mpr fun y =>
      (hasDerivAt_gaussianSuccessPrimitive y).continuousAt).const_mul _).continuousOn
  · intro φ hφ y z _hz _hyS hy
    exact payOnce_inactive_central_test_mean (fun t => Γ (φ t)) (fun t => B (φ t))
      F g ρ (h.along φ hφ) hlocal y hy ψ hψ hD hK hquad

theorem payOnce_inactive_central_derivative_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0<ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := 2*((k+1:ℕ):ℝ)/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    ∀ᶠ t in atTop, ∀ y ∈ S,
      |deriv (coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))))
          (inactiveGaussianPrice Γ F g ρ y t)-a*cdf (gaussianReal 0 1) y| < ε := by
  dsimp only
  apply eventually_uniform_abs_lt_of_compact_sequences hS _ _ (continuous_Φ.const_mul _).continuousOn ?_ hε
  intro φ hφ y z _hz _hyS hy
  exact payOnce_inactive_central_derivative_tendsto (fun t => Γ (φ t)) (fun t => B (φ t))
    F g ρ (h.along φ hφ) hlocal y hy

theorem payOnce_inactive_central_allocation_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0<ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := 2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    ∀ᶠ t in atTop, ∀ y ∈ S,
      |(∫ r, allocation (k+1) (C t) hn r (inactiveGaussianPrice Γ F g ρ y t)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))/
          inactiveGaussianScale M F (k+1) g ρ t-a*gaussianSuccessPrimitive y| < ε := by
  have hh := payOnce_inactive_central_test_mean_uniform Γ B F g ρ h hlocal
    id measurable_id (D := 1) (fun p hp => by simpa only [id_eq,abs_of_nonneg hp.1] using hp.2)
    (d := 1) (K := 0) (by norm_num) (fun p _ => by simp) hS hε
  simpa only [id_eq,one_mul] using hh

theorem payOnce_inactive_central_coverage_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {S : Set ℝ} (hS : IsCompact S) {ε : ℝ} (hε : 0<ε) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := ((k+1:ℕ):ℝ)*(2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    ∀ᶠ t in atTop, ∀ y ∈ S,
      |coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
          (inactiveGaussianPrice Γ F g ρ y t)/inactiveGaussianScale M F (k+1) g ρ t-
            a*gaussianSuccessPrimitive y| < ε := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  exact payOnce_inactive_central_test_mean_uniform Γ B F g ρ h hlocal
    (success (k+1)) (continuous_success _).measurable (D := 1) (fun p hp => by
      have hpos : 0 ≤ success (k+1) p := by
        unfold success
        exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))
      rw [abs_of_nonneg hpos]
      exact success_le_one _ _ hp.2)
    (d := ((k+1:ℕ):ℝ)) (K := ((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)-1)/2)
    (by
      have hnR : (2:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by norm_num))
    (fun p hp => KernelEntryExpansion.success_linear_error_le _ hp) hS hε

theorem payOnce_inactive_central_coverage_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := ((k+1:ℕ):ℝ)*(2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    Tendsto (fun t => coverage (k+1) (C t) hn
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
          (inactiveGaussianPrice Γ F g ρ (y t) t)/inactiveGaussianScale M F (k+1) g ρ t)
      atTop (𝓝 (a*gaussianSuccessPrimitive z)) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  exact payOnce_inactive_central_test_mean Γ B F g ρ h hlocal y hy
    (success (k+1)) (continuous_success _).measurable (D := 1) (fun p hp => by
      have hpos : 0 ≤ success (k+1) p := by
        unfold success
        exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))
      rw [abs_of_nonneg hpos]
      exact success_le_one _ _ hp.2)
    (d := ((k+1:ℕ):ℝ)) (K := ((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)-1)/2)
    (by
      have hnR : (2:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by norm_num))
    (fun p hp => KernelEntryExpansion.success_linear_error_le _ hp)

end FCAppendix.Bayes
