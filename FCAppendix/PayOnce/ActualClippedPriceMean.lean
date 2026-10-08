import FCAppendix.PayOnce.InactiveClippedPriceMean
import FCAppendix.PayOnce.ActualClippedPriceMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_actual_clipped_price_mean_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => (∫ d, clipToInterval ℓ u
      (actualSampleProfilePrice (Γ t) h.proposers_two d)-bar t ∂userProfileLaw (Γ t)) /
        inactiveGaussianScale M F (k+1) g ρ t) atTop (𝓝 0) := by
  dsimp only
  have hh := payOnce_inactive_clipped_profile_price_mean_tendsto Γ B F g ρ h hlocal ℓ u hℓ hu
  apply hh.congr'
  filter_upwards [] with t
  congr 1
  exact (integral_actualSampleProfilePrice (Γ t) h.proposers_two
    (fun x => clipToInterval ℓ u x-KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))
    ((measurable_clipToInterval ℓ u).sub_const _)).symm

theorem payOnce_inactive_conditional_clipped_price_mean_small {R : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(R t+1:ℕ))
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i : Fin (R t+1), ∀ a : UserDraw (k+1),
      0 < effectiveBid a.1.2 →
      |∫ d, clipToInterval ℓ u
        (conditionalProfilePrice (Γ t) h.proposers_two i a d)-bar t ∂userProfileLaw (Γ t)| ≤
          ε*inactiveGaussianScale (fun t => R t+1) F (k+1) g ρ t := by
  dsimp only
  intro ε hε
  filter_upwards [payOnce_inactive_clipped_focal_price_mean_small Γ B F g ρ h hlocal ℓ u hℓ hu ε hε]
    with t ht
  intro i a ha
  rw [integral_conditionalProfilePrice (Γ t) h.proposers_two i a _
    ((measurable_clipToInterval ℓ u).sub_const _)]
  exact ht (effectiveBid a.1.2) ha

end FCAppendix.Bayes
