import FCAppendix.PayOnce.InactivePriceRecentering
import FCAppendix.PayOnce.InactiveSourceCentering

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_price_centering_normalized
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    Tendsto (fun t => (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-inactiveValuePrice M C F (k+1) g t)/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) := by
  exact payOnce_inactive_gaussian_recenter_shift_of_isLittleO Γ B F g ρ h hlocal
    (inactiveValuePrice M C F (k+1) g) (payOnce_inactive_price_centering Γ B F g ρ h hlocal)

theorem payOnce_inactive_focal_price_value_center_gaussian_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (focalPrice (k+1) (C t) hn b r-inactiveValuePrice M C F (k+1) g t)/
          inactiveGaussianScale M F (k+1) g ρ t)) x-cdf (gaussianReal 0 1) x| < ε := by
  exact payOnce_inactive_focal_price_gaussian_uniform_of_shift Γ B F g ρ h hlocal
    (inactiveValuePrice M C F (k+1) g) (payOnce_inactive_price_centering_normalized Γ B F g ρ h hlocal) x

theorem payOnce_inactive_profile_price_value_center_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
      (fun r => (sampleProfilePrice (k+1) (C t) hn r-inactiveValuePrice M C F (k+1) g t)/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  exact payOnce_inactive_profile_price_gaussian_cdf_of_shift Γ B F g ρ h hlocal
    (inactiveValuePrice M C F (k+1) g) (payOnce_inactive_price_centering_normalized Γ B F g ρ h hlocal) x

theorem payOnce_inactive_focal_price_value_center_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (b : ℕ → ℝ) (hb : ∀ᶠ t in atTop, 0 < b t) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
      (fun r => (focalPrice (k+1) (C t) hn (b t) r-inactiveValuePrice M C F (k+1) g t)/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  dsimp only
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [payOnce_inactive_focal_price_value_center_gaussian_uniform Γ B F g ρ h hlocal x ε hε,hb]
    with t ht hbt
  simpa only [Real.dist_eq] using ht (b t) hbt

theorem payOnce_inactive_price_limit_centering_normalized
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (hcapacity : (fun t => (C t:ℝ)/(M t)-ρ) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) :
    Tendsto (fun t => (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))-Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)/
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) := by
  apply payOnce_inactive_gaussian_recenter_shift_of_isLittleO Γ B F g ρ h hlocal
  have hh := (payOnce_inactive_price_centering Γ B F g ρ h hlocal).add
    (payOnce_inactive_value_price_difference_isLittleO Γ B F g ρ h hlocal hcapacity)
  simpa only [Pi.add_apply,sub_add_sub_cancel] using hh

theorem payOnce_inactive_focal_price_limit_center_gaussian_uniform
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (hcapacity : (fun t => (C t:ℝ)/(M t)-ρ) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |cdf ((Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
        (fun r => (focalPrice (k+1) (C t) hn b r-
          Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)/
          inactiveGaussianScale M F (k+1) g ρ t)) x-cdf (gaussianReal 0 1) x| < ε := by
  exact payOnce_inactive_focal_price_gaussian_uniform_of_shift Γ B F g ρ h hlocal _
    (payOnce_inactive_price_limit_centering_normalized Γ B F g ρ h hlocal hcapacity) x

theorem payOnce_inactive_profile_price_limit_center_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (hcapacity : (fun t => (C t:ℝ)/(M t)-ρ) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2))) (x : ℝ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map
      (fun r => (sampleProfilePrice (k+1) (C t) hn r-
        Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  exact payOnce_inactive_profile_price_gaussian_cdf_of_shift Γ B F g ρ h hlocal _
    (payOnce_inactive_price_limit_centering_normalized Γ B F g ρ h hlocal hcapacity) x

end FCAppendix.Bayes
