import FCAppendix.PayOnce.InactiveBelowEntry

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_fixed_below_response
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) (b : ℕ → ℝ) {w : ℝ}
    (hw : w < Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)
    (hb : Tendsto b atTop (𝓝 (Limit.bidStar (k+1)
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) w))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => Real.sqrt (M t:ℝ)*
      ((∫ r, allocation (k+1) (C t) hn r (b t)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))-
          Limit.pStar (k+1) (bar t) w)) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbid := hb
  rw [Limit.bidStar_of_le hw.le] at hbid
  have hsmall := payOnce_inactive_below_entry_scaled_mean_tendsto Γ B F g ρ h b hbid
    (max_lt hw hL)
  apply hsmall.congr'
  filter_upwards [(payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hw,
    (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_const_lt hL] with t ht htp
  rw [Limit.pStar_eq_zero_of_le hn htp.le ht.le,sub_zero]

end FCAppendix.Bayes
