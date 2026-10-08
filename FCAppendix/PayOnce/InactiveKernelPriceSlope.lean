import FCAppendix.PayOnce.InactivePopulationPrice
import FCAppendix.PayOnce.KernelPriceSlope

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.OwnImpact
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem inactive_limit_bid_ae_avoids_clipping
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ v ∂F, Limit.bidStar (k+1) L (max (v-g) 0) ≠ L ∧
      Limit.bidStar (k+1) L (max (v-g) 0) ≠ ((k+1:ℕ):ℝ)*L := by
  have hk := h.proposers_two
  have hatom : F {g+L} = 0 := by
    have hh := h.positive_values_atomless 0 (g+L)
    rw [h.common_fee 0,h.common_values 0] at hh
    exact hh (by linarith)
  have hae : ∀ᵐ v ∂F, v ≠ g+L := by
    simpa only [mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.mp hatom)
  filter_upwards [hae] with v hv
  apply bidStar_avoids_clipping (by omega) hL
  intro he
  by_cases hnet : 0 ≤ v-g
  · rw [max_eq_left hnet] at he
    exact hv (by linarith)
  · rw [max_eq_right (le_of_not_ge hnet)] at he
    exact hL.ne he

theorem payOnce_inactive_kernel_price_slope_tendsto_of_price_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {Ls : ℕ → ℝ}
    (hLs : Tendsto Ls atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    Tendsto (fun t => ∫ b, kernelPriceSlope (k+1) b (Ls t)
      ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)) atTop
        (𝓝 (EndpointVariance.priceSlope μW (k+1) L)) := by
  dsimp only
  let μW := F.map (fun v => max (v-g) 0)
  let L := Limit.capRoot μW (k+1) ρ
  have hk := h.proposers_two
  obtain ⟨hL,_,b,_,hb,_,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hp : Tendsto Ls atTop (𝓝 L) := hLs
  have hpos : ∀ᶠ t in atTop, 0 < Ls t := hp.eventually (eventually_gt_nhds hL)
  have ha := inactive_limit_bid_ae_avoids_clipping Γ B F g ρ h hL
  have hs := tendsto_integral_kernelPriceSlope F (by omega : 2 ≤ k+1) hL b hb
    (fun v => Limit.bidStar (k+1) L (max (v-g) 0)) hlim ha hp
  have htarget : (∫ v, kernelPriceSlope (k+1) (Limit.bidStar (k+1) L (max (v-g) 0)) L ∂F) =
      EndpointVariance.priceSlope μW (k+1) L := by
    rw [GaussianParameters.priceSlope_eq_integral]
    change _ = ∫ w, GaussianParameters.priceDensity (k+1) L w ∂F.map (fun v => max (v-g) 0)
    rw [integral_map (show Measurable (fun v : ℝ => max (v-g) 0) from
      (measurable_id.sub_const g).max measurable_const).aemeasurable
      (GaussianParameters.measurable_priceDensity (k+1) L).aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun v => kernelPriceSlope_bidStar (by omega) hL _)
  rw [htarget] at hs
  apply hs.congr'
  filter_upwards [heq,hpos] with t ht hLt
  rw [realEffectiveBidLaw_eq_pure_map (Γ t) (b t) (hb t) ht,h.common_values t,
    integral_map (hb t).aemeasurable (measurable_kernelPriceSlope (by omega) hLt).aestronglyMeasurable]

theorem payOnce_inactive_kernel_price_slope_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    let Lm := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => ∫ b, kernelPriceSlope (k+1) b (Lm t)
      ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)) atTop
        (𝓝 (EndpointVariance.priceSlope μW (k+1) L)) :=
  payOnce_inactive_kernel_price_slope_tendsto_of_price_tendsto Γ B F g ρ h
    (payOnce_inactive_population_price Γ B F g ρ h).2

theorem payOnce_inactive_eventually_ae_kernel_price_derivative
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᶠ t in atTop, ∀ L, 0 < L →
      ∀ᵐ b ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ),
        HasDerivAt (kernel (k+1) b) (-kernelPriceSlope (k+1) b L) L := by
  have hk := h.proposers_two
  filter_upwards [h.eventually_scarce] with t ht
  intro L hL
  have ha (b : ℝ) (hb : 0 < b) : (BidScaling.realBidLaw (Γ t) : Measure ℝ) {b} = 0 :=
    realEffectiveBidLaw_positive_atomless (Γ t) ht.1 ht.2 (h.action_schedule t)
      (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
      (h.positive_values_atomless t) (h.visible_atomless t) hb
  have hnL : 0 < ((k+1:ℕ):ℝ)*L := mul_pos (Nat.cast_pos.mpr (by omega)) hL
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (ha L hL),
    measure_eq_zero_iff_ae_notMem.mp (ha (((k+1:ℕ):ℝ)*L) hnL)] with b hb0 hb1
  exact hasDerivAt_kernel_price_slope (by omega) hL
    (by simpa only [mem_singleton_iff] using hb0)
    (by simpa only [mem_singleton_iff] using hb1)

theorem payOnce_inactive_mean_price_derivative_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    let Lm := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => ∫ b, -deriv (kernel (k+1) b) (Lm t)
      ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)) atTop
        (𝓝 (EndpointVariance.priceSlope μW (k+1) L)) := by
  dsimp only
  have hp := payOnce_inactive_population_price Γ B F g ρ h
  have hs := payOnce_inactive_kernel_price_slope_tendsto Γ B F g ρ h
  apply hs.congr'
  filter_upwards [hp.1,payOnce_inactive_eventually_ae_kernel_price_derivative Γ B F g ρ h]
    with t ht hd
  apply integral_congr_ae
  filter_upwards [hd _ (KernelDemand.populationPrice_spec ht.exists).1] with b hb
  rw [hb.deriv,neg_neg]

end FCAppendix.Bayes
