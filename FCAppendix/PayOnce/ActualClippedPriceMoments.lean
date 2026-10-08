import FCAppendix.PayOnce.ActualProfilePrice
import FCAppendix.PayOnce.ConditionalProfilePrice
import FCAppendix.PayOnce.InactiveClippedPriceMoments

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel Probability
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem integral_conditionalProfilePrice {N c : ℕ}
    (Γ : FiniteGame (N+1) (k+1) c Seed) (hk : 1 ≤ k)
    (i : Fin (N+1)) (u : UserDraw (k+1)) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ d, f (conditionalProfilePrice Γ hk i u d) ∂userProfileLaw Γ) =
      ∫ z, f (focalPrice (k+1) c (by omega) (effectiveBid u.1.2) z)
        ∂(Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  rw [← integral_map (measurable_conditionalProfilePrice Γ hk i u).aemeasurable
      hf.aestronglyMeasurable, conditionalProfilePrice_map_eq Γ hk i u,
    integral_map (measurable_focalPrice (by omega) _).aemeasurable hf.aestronglyMeasurable]

theorem integrable_conditionalProfilePrice_iff {N c : ℕ}
    (Γ : FiniteGame (N+1) (k+1) c Seed) (hk : 1 ≤ k)
    (i : Fin (N+1)) (u : UserDraw (k+1)) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun d => f (conditionalProfilePrice Γ hk i u d)) (userProfileLaw Γ) ↔
      Integrable (fun z => f (focalPrice (k+1) c (by omega) (effectiveBid u.1.2) z))
        (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  change Integrable (f ∘ conditionalProfilePrice Γ hk i u) _ ↔
    Integrable (f ∘ focalPrice (k+1) c (by omega) (effectiveBid u.1.2)) _
  rw [← integrable_map_measure hf.aestronglyMeasurable
      (measurable_conditionalProfilePrice Γ hk i u).aemeasurable,
    conditionalProfilePrice_map_eq Γ hk i u,
    integrable_map_measure hf.aestronglyMeasurable (measurable_focalPrice (by omega) _).aemeasurable]

theorem payOnce_inactive_actual_clipped_price_moments
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop,
      Integrable (fun d => |clipToInterval ℓ u
        (actualSampleProfilePrice (Γ t) h.proposers_two d)-bar t|^r) (userProfileLaw (Γ t)) ∧
      (∫ d, |clipToInterval ℓ u (actualSampleProfilePrice (Γ t) h.proposers_two d)-bar t|^r
        ∂userProfileLaw (Γ t)) ≤ K*(M t:ℝ)^(-r/2) := by
  dsimp only
  obtain ⟨K,hK,he⟩ := payOnce_inactive_clipped_profile_price_moments Γ B F g ρ h ℓ u hℓ hu hr
  refine ⟨K,hK,?_⟩
  filter_upwards [he] with t ht
  let f : ℝ → ℝ := fun x => |clipToInterval ℓ u x-
    KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|^r
  have hf : Measurable f := ((measurable_clipToInterval ℓ u).sub_const _).abs.pow_const r
  exact ⟨(integrable_actualSampleProfilePrice_iff (Γ t) h.proposers_two f hf).mpr ht.1,
    (integral_actualSampleProfilePrice (Γ t) h.proposers_two f hf).trans_le ht.2⟩

theorem payOnce_inactive_conditional_clipped_price_moments {R : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (ℓ u : ℝ)
    (hℓ : ℓ < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hu : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < u)
    {r : ℝ} (hr : 1 ≤ r) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(R t+1:ℕ))
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in atTop, ∀ i : Fin (R t+1), ∀ a : UserDraw (k+1),
      0 < effectiveBid a.1.2 →
      Integrable (fun d => |clipToInterval ℓ u
        (conditionalProfilePrice (Γ t) h.proposers_two i a d)-bar t|^r) (userProfileLaw (Γ t)) ∧
      (∫ d, |clipToInterval ℓ u (conditionalProfilePrice (Γ t) h.proposers_two i a d)-bar t|^r
        ∂userProfileLaw (Γ t)) ≤ K*(R t+1:ℕ)^(-r/2) := by
  dsimp only
  obtain ⟨K,hK,he⟩ := payOnce_inactive_clipped_focal_price_moments Γ B F g ρ h ℓ u hℓ hu hr
  refine ⟨K,hK,?_⟩
  filter_upwards [he] with t ht
  intro i a ha
  have hm := ht (effectiveBid a.1.2) ha
  let f : ℝ → ℝ := fun x => |clipToInterval ℓ u x-
    KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(R t+1:ℕ))|^r
  have hf : Measurable f := ((measurable_clipToInterval ℓ u).sub_const _).abs.pow_const r
  exact ⟨(integrable_conditionalProfilePrice_iff (Γ t) h.proposers_two i a f hf).mpr hm.1,
    (integral_conditionalProfilePrice (Γ t) h.proposers_two i a f hf).trans_le hm.2⟩

end FCAppendix.Bayes
