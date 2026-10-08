import FCAppendix.PayOnce.InactiveDerivativeMean
import FCAppendix.PayOnce.InteriorFOCResponse
import FCAppendix.PayOnce.InactiveInteriorExpectation

namespace FCAppendix.PayOnce.Limit
open Set CommonList

theorem bidStar_mem_Ioo {n : ℕ} (hn : 2 ≤ n) {L w : ℝ}
    (hL : 0 < L) (hw : L < w) : bidStar n L w ∈ Ioo L ((n:ℝ)*L) := by
  apply (OwnImpact.kernel_interior_iff hn hL).mp
  rw [kernel_bidStar hn hL]
  exact ⟨(pStar_pos_iff hn hL.le).mpr hw,pStar_lt_one hn hL hw⟩

end FCAppendix.PayOnce.Limit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.KernelTailEvent
open PayOnce.RareSuccessSlope PayOnce.KernelTaylor
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_derivative_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) {β : ℝ} (hb : Tendsto b atTop (𝓝 β))
    (hlo : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < β)
    (hhi : β < ((k+1:ℕ):ℝ)*Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let Q := fun t => coverage (k+1) (C t) hn (Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
    Tendsto (fun t => Real.sqrt (M t:ℝ)*(b t*deriv (Q t) (b t)-
      phi (k+1) (kernel (k+1) (b t) (bar t)))) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  have hcorr := payOnce_inactive_derivative_phi_mean_sqrt Γ B F g ρ h b hb hlo
  have hphi := payOnce_inactive_focal_phi_mean_sqrt Γ B F g ρ h hlocal b hb hlo hhi
  simpa only [← mul_add,sub_add_sub_cancel,zero_add] using hcorr.add hphi

theorem payOnce_inactive_fixed_served_mean_response_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ) {w : ℝ}
    (hw : Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ < w)
    (hb : Tendsto b atTop (𝓝 (Limit.bidStar (k+1)
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) w)))
    (hFOC : ∀ᶠ t in atTop,
      let Q := coverage (k+1) (C t) (by have := h.proposers_two; omega)
        (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))
      Q (b t)=(w-b t)*deriv Q (b t)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => Real.sqrt (M t:ℝ)*((∫ r, allocation (k+1) (C t) hn r (b t)
      ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))-
        Limit.pStar (k+1) (bar t) w)) atTop (𝓝 0) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  let mean := fun t => ∫ r, allocation (k+1) (C t) hn r (b t) ∂μ t
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar : Tendsto bar atTop (𝓝 L) := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hbet := Limit.bidStar_mem_Ioo hn hL hw
  have hmean := payOnce_inactive_focal_allocation_mean_sqrt Γ B F g ρ h hlocal b hb hbet.1 hbet.2
  have hQ := payOnce_inactive_focal_coverage_mean_sqrt Γ B F g ρ h hlocal b hb hbet.1 hbet.2
  have hR := payOnce_inactive_focal_derivative_sqrt Γ B F g ρ h hlocal b hb hbet.1 hbet.2
  have hFOC' : ∀ᶠ t in atTop, b t*Q t (b t)=(w-b t)*(b t*deriv (Q t) (b t)) := by
    filter_upwards [hFOC] with t ht
    change Q t (b t)=(w-b t)*deriv (Q t) (b t) at ht
    rw [ht]
    ring
  exact InteriorFOCResponse.mean_response_scaled_tendsto hn hL hw bar b
    (fun t => Q t (b t)) (fun t => b t*deriv (Q t) (b t)) mean
    (fun t => Real.sqrt (M t:ℝ)) hbar hb hFOC' hQ hR hmean

end FCAppendix.Bayes
