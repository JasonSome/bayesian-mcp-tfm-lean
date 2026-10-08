import FCAppendix.PayOnce.LowerEntryResponse
import FCAppendix.PayOnce.InactivePureFirstOrder
import FCAppendix.PayOnce.MonotoneEntryBarrier

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_lower_response_error
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1)
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0)))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ᵐ v ∂F, g < v → b t v ≤ bar t →
      |(∫ r, allocation (k+1) (C t) hn r (b t v) ∂μ t)-
        Limit.pStar (k+1) (bar t) (max (v-g) 0)| ≤ D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  obtain ⟨η,D,hη,hD,herror⟩ := payOnce_inactive_lower_entry_response_error Γ B F g ρ h hlocal
  obtain ⟨A,hA,halloc⟩ := payOnce_inactive_lower_allocation_bounds Γ B F g ρ h
  have hbarrier := monotone_entry_barrier F hL hlocal b hmono hlim bar hbar η hη
  have hFOC := payOnce_inactive_eventual_pure_first_order Γ B F g ρ h b heq
  refine ⟨max A D,lt_max_of_lt_left hA,?_⟩
  filter_upwards [herror,halloc,hbarrier,hFOC,hbar.eventually (eventually_gt_nhds hL)]
    with t herr ha hwindow hf hbarpos
  filter_upwards [hf] with v hv hvg hbid
  have hpos := (hv hvg).1
  rw [max_eq_left (sub_pos.mpr hvg).le]
  have hδ : 0 ≤ (M t:ℝ)^(-(1:ℝ)/2) := rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hw : v-g ≤ bar t
  · rw [Limit.pStar_eq_zero_of_le hn hbarpos.le hw,sub_zero,
      abs_of_nonneg (integral_nonneg (fun r => (allocation_bounds hn r (b t v)).1))]
    exact (ha (b t v) hpos hbid).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left A D) hδ)
  · have hnear : b t v ∈ Icc (bar t-η) (bar t) :=
      ⟨(hwindow v (le_of_not_ge hw)).le,hbid⟩
    exact (herr (v-g) (b t v) hnear (hv hvg).2.2).trans
      (mul_le_mul_of_nonneg_right (le_max_right A D) hδ)

end FCAppendix.Bayes
