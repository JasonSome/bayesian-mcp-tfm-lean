import FCAppendix.PayOnce.InactiveCentralLimits

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_test_mean_of_normalized_bid
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) {y : ℝ}
    (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 y))
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) {D : ℝ}
    (hD : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ D)
    {d K : ℝ} (hK : 0 ≤ K) (hquad : ∀ p ∈ Icc (0:ℝ) 1, |ψ p-d*p| ≤ K*p^2) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => (∫ r, ψ (allocation (k+1) (C t) hn r (b t))
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))/
        inactiveGaussianScale M F (k+1) g ρ t) atTop
      (𝓝 ((d*(2/((((k+1:ℕ):ℝ)-1)*
        Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))*gaussianSuccessPrimitive y)) := by
  have hh := payOnce_inactive_central_test_mean Γ B F g ρ h hlocal _ hy ψ hψ hD hK hquad
  apply hh.congr'
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
  have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht
  have he : KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))+
      inactiveGaussianScale M F (k+1) g ρ t*((b t-KernelDemand.populationPrice (k+1)
        (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)=b t := by
    rw [mul_div_cancel₀ _ hs.ne',add_sub_cancel]
  rw [he]

theorem payOnce_inactive_central_coverage_of_normalized_bid
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) {y : ℝ}
    (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 y)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := ((k+1:ℕ):ℝ)*(2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    Tendsto (fun t => coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) (b t)/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 (a*gaussianSuccessPrimitive y)) := by
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  exact payOnce_inactive_central_test_mean_of_normalized_bid Γ B F g ρ h hlocal b hy
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

theorem payOnce_inactive_central_utility_of_normalized_bid
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (w b : ℕ → ℝ) {x y : ℝ}
    (hx : Tendsto (fun t => (w t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 x))
    (hy : Tendsto (fun t => (b t-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/inactiveGaussianScale M F (k+1) g ρ t)
        atTop (𝓝 y)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let a := ((k+1:ℕ):ℝ)*(2/((((k+1:ℕ):ℝ)-1)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    Tendsto (fun t => (w t-b t)*coverage (k+1) (C t) hn
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))) (b t)/
        (inactiveGaussianScale M F (k+1) g ρ t)^2) atTop
      (𝓝 ((x-y)*(a*gaussianSuccessPrimitive y))) := by
  have hh := (hx.sub hy).mul (payOnce_inactive_central_coverage_of_normalized_bid Γ B F g ρ h hlocal b hy)
  apply hh.congr
  intro t
  ring

end FCAppendix.Bayes
