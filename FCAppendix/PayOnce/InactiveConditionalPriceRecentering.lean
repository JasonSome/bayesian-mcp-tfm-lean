import FCAppendix.PayOnce.ConditionalProfilePrice
import FCAppendix.PayOnce.InactiveValuePriceCLT

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actualSampleProfilePrice_standardized_map_eq
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (center scale : ℝ) :
    (userProfileLaw Γ).map (fun d => (actualSampleProfilePrice Γ hk d-center)/scale) =
      (Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (fun r => (sampleProfilePrice (k+1) c (by omega) r-center)/scale) := by
  rw [← (effectiveBid_profile_measurePreserving Γ).map_eq,
    Measure.map_map (((measurable_sampleProfilePrice (by omega)).sub_const center).div_const scale)
      (effectiveBid_profile_measurePreserving Γ).measurable]
  rfl

theorem cdf_actualSampleProfilePrice_standardized_eq
    (Γ : FiniteGame m (k+1) c Seed) (hk : 1 ≤ k) (center scale x : ℝ) :
    cdf ((userProfileLaw Γ).map (fun d => (actualSampleProfilePrice Γ hk d-center)/scale)) x =
      cdf ((Measure.pi (fun _ : Fin m => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (fun r => (sampleProfilePrice (k+1) c (by omega) r-center)/scale)) x := by
  rw [actualSampleProfilePrice_standardized_map_eq]

variable {R M C : ℕ → ℕ}

theorem payOnce_inactive_conditional_price_value_center_gaussian_uniform
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i : Fin (R t+1), ∀ u : UserDraw (k+1),
      0 < effectiveBid u.1.2 →
      |cdf ((userProfileLaw (Γ t)).map (fun d =>
        (conditionalProfilePrice (Γ t) h.proposers_two i u d -
          inactiveValuePrice (fun t => R t+1) C F (k+1) g t)/
          inactiveGaussianScale (fun t => R t+1) F (k+1) g ρ t)) x -
        cdf (gaussianReal 0 1) x| < ε := by
  intro ε hε
  filter_upwards [payOnce_inactive_focal_price_value_center_gaussian_uniform
    Γ B F g ρ h hlocal x ε hε] with t ht
  intro i u hu
  rw [conditionalProfilePrice_standardized_map_eq]
  have hh := ht (effectiveBid u.1.2) hu
  convert hh using 1
  congr 5

theorem payOnce_inactive_conditional_price_value_center_gaussian_cdf
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ)
    (i : ∀ t, Fin (R t+1)) (u : ℕ → UserDraw (k+1))
    (hu : ∀ᶠ t in atTop, 0 < effectiveBid (u t).1.2) :
    Tendsto (fun t => cdf ((userProfileLaw (Γ t)).map (fun d =>
      (conditionalProfilePrice (Γ t) h.proposers_two (i t) (u t) d -
        inactiveValuePrice (fun t => R t+1) C F (k+1) g t)/
        inactiveGaussianScale (fun t => R t+1) F (k+1) g ρ t)) x)
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [payOnce_inactive_conditional_price_value_center_gaussian_uniform
    Γ B F g ρ h hlocal x ε hε,hu] with t ht hut
  simpa only [Real.dist_eq] using ht (i t) (u t) hut

theorem payOnce_inactive_actual_price_value_center_gaussian_cdf
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    Tendsto (fun t => cdf ((userProfileLaw (Γ t)).map (fun d =>
      (actualSampleProfilePrice (Γ t) h.proposers_two d -
        inactiveValuePrice M C F (k+1) g t)/
      inactiveGaussianScale M F (k+1) g ρ t)) x) atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  apply (payOnce_inactive_profile_price_value_center_gaussian_cdf Γ B F g ρ h hlocal x).congr
  intro t
  exact (cdf_actualSampleProfilePrice_standardized_eq (Γ t) h.proposers_two _ _ x).symm

end FCAppendix.Bayes
