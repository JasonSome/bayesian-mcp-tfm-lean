import FCAppendix.PayOnce.InactivePriceThresholds
import FCAppendix.PayOnce.ProfilePriceCLT
import FCAppendix.PayOnce.ActualProfilePrice
import FCAppendix.PayOnce.InactiveRivalUnderfill

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_price_gaussian_uniform
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      |(Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | (focalPrice (k+1) (C t) (by have hk := h.proposers_two; omega) b r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
            ((C t:ℝ)/(N t+1:ℕ)))/
          inactiveGaussianScale (fun t => N t+1) F (k+1) g ρ t ≤ x} -
        cdf (gaussianReal 0 1) x| < ε := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hv := GaussianParameters.variance_pos μW (n := k+1) (by omega) hL hlocal
  have hT := payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x
  have hbound := focalPrice_probability_uniform_of_kernel_CLT (by omega : 2 ≤ k+1)
    (fun t => BidScaling.realBidLaw (Γ t)) (inactiveGaussianPrice Γ F g ρ x)
    (hT.eventually (eventually_gt_nhds hL)) N C h.rivals_grow hv
    (payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h hT)
    (by simpa only [sub_zero] using
      payOnce_inactive_rival_price_threshold_tendsto Γ B F g ρ h hlocal x 0)
    (payOnce_inactive_rival_underfill_tendsto_zero Γ B F g ρ h)
  intro ε hε
  filter_upwards [hbound ε hε] with t ht b hb
  have he (r : Fin (N t) → ℝ) :
      (focalPrice (k+1) (C t) (by omega) b r -
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
          ((C t:ℝ)/(N t+1:ℕ)))/inactiveGaussianScale (fun t => N t+1) F (k+1) g ρ t ≤ x ↔
      focalPrice (k+1) (C t) (by omega) b r ≤ inactiveGaussianPrice Γ F g ρ x t := by
    have hs := payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal (t := t) (by omega)
    rw [div_le_iff₀ hs]
    unfold inactiveGaussianPrice
    constructor <;> intro hr <;> linarith
  simpa only [he] using ht b hb

variable {M : ℕ → ℕ}

theorem payOnce_inactive_profile_price_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    Tendsto (fun t => cdf ((Measure.pi (fun _ : Fin (M t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).map (fun r =>
        (sampleProfilePrice (k+1) (C t) (by have hk := h.proposers_two; omega) r -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
        inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hv := GaussianParameters.variance_pos μW (n := k+1) (by omega) hL hlocal
  have hT := payOnce_inactive_gaussian_price_tendsto Γ B F g ρ h x
  have hh := sampleProfilePrice_probability_tendsto_of_kernel_CLT (by omega : 2 ≤ k+1)
    (fun t => BidScaling.realBidLaw (Γ t)) (inactiveGaussianPrice Γ F g ρ x)
    (hT.eventually (eventually_gt_nhds hL)) M C h.population_grows hv
    (payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h hT)
    (by simpa only [sub_zero] using
      payOnce_inactive_population_price_threshold_tendsto Γ B F g ρ h hlocal x 0)
    (payOnce_inactive_profile_underfill_tendsto_zero Γ B F g ρ h)
  apply hh.congr'
  filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
  exact (cdf_standardized_sampleProfilePrice_eq (by omega) _ _ x
    (payOnce_inactive_gaussian_scale_pos Γ B F g ρ h hlocal ht)).symm

theorem payOnce_inactive_actual_price_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    Tendsto (fun t => cdf ((userProfileLaw (Γ t)).map (fun d =>
      (actualSampleProfilePrice (Γ t) h.proposers_two d -
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))/
      inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  apply (payOnce_inactive_profile_price_gaussian_cdf Γ B F g ρ h hlocal x).congr
  intro t
  congr 1
  rw [← (effectiveBid_profile_measurePreserving (Γ t)).map_eq,
    Measure.map_map (((measurable_sampleProfilePrice (by have hk := h.proposers_two; omega)).sub_const _).div_const _)
      (effectiveBid_profile_measurePreserving (Γ t)).measurable]
  rfl

end FCAppendix.Bayes
