import FCAppendix.PayOnce.KernelDemandDerivative
import FCAppendix.PayOnce.InactiveKernelPriceSlope
import FCAppendix.PayOnce.InactiveKernelCLT

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.OwnImpact
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_eventually_real_bid_positive_atomless
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b → (BidScaling.realBidLaw (Γ t) : Measure ℝ) {b} = 0 := by
  filter_upwards [h.eventually_scarce] with t ht
  intro b hb
  exact realEffectiveBidLaw_positive_atomless (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t) (h.visible_atomless t) hb

theorem payOnce_inactive_eventually_hasDerivAt_demand
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᶠ t in atTop, ∀ L, 0 < L →
      HasDerivAt (KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal))
        (-(∫ b, kernelPriceSlope (k+1) b L ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))) L := by
  have hk := h.proposers_two
  filter_upwards [payOnce_inactive_eventually_real_bid_positive_atomless Γ B F g ρ h] with t ht
  intro L hL
  have hd := KernelDemand.hasDerivAt_integral_kernel (BidScaling.realBidLaw (Γ t) : Measure ℝ)
    (by omega : 2 ≤ k+1) hL (ht L hL)
    (ht (((k+1:ℕ):ℝ)*L) (mul_pos (Nat.cast_pos.mpr (by omega)) hL))
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hL] with T hT
  exact (realBidLaw_kernel_mean_eq_demand (Γ t) (by omega) hT).symm

theorem payOnce_inactive_demand_increment_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {S δ : ℕ → ℝ}
    (hS : Tendsto S atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))
    (hδ : Tendsto δ atTop (𝓝 0)) (hδne : ∀ᶠ t in atTop, δ t ≠ 0) :
    let μW := F.map (fun v => max (v-g) 0)
    let L := Limit.capRoot μW (k+1) ρ
    Tendsto (fun t => (KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t+δ t) -
      KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) (S t))/(δ t)) atTop
        (𝓝 (-EndpointVariance.priceSlope μW (k+1) L)) := by
  dsimp only
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  have hk := h.proposers_two
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hU : Tendsto (fun t => S t+δ t) atTop (𝓝 L) := by
    simpa only [add_zero] using hS.add hδ
  have hne : ∀ᶠ t in atTop, S t ≠ S t+δ t := by
    filter_upwards [hδne] with t ht he
    exact ht (by linarith)
  have hi := KernelDemand.tendsto_integral_kernel_increment
    (fun t => (BidScaling.realBidLaw (Γ t) : Measure ℝ)) (by omega : 2 ≤ k+1) hL
    (payOnce_inactive_eventually_real_bid_positive_atomless Γ B F g ρ h)
    (fun T hT => payOnce_inactive_kernel_price_slope_tendsto_of_price_tendsto Γ B F g ρ h hT)
    hS hU hne
  apply hi.congr'
  filter_upwards [hS.eventually (eventually_gt_nhds hL),
    hU.eventually (eventually_gt_nhds hL)] with t htS htU
  rw [realBidLaw_kernel_mean_eq_demand (Γ t) (by omega) htU,
    realBidLaw_kernel_mean_eq_demand (Γ t) (by omega) htS,add_sub_cancel_left]

end FCAppendix.Bayes
