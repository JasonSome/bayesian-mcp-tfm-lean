import FCAppendix.PayOnce.InactiveLowerResponse
import FCAppendix.PayOnce.InactiveUpperEntryResponse
import FCAppendix.PayOnce.InactiveFarAboveResponse

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_response_error_for_pure
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ) (hmono : ∀ t, Monotone (b t))
    (hbound : ∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1)
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0)))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ᵐ v ∂F,
      |(∫ r, allocation (k+1) (C t) hn r (b t v) ∂μ t)-
        Limit.pStar (k+1) (bar t) (max (v-g) 0)| ≤ D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  obtain ⟨D₀,hD₀,hlower⟩ := payOnce_inactive_lower_response_error Γ B F g ρ h hlocal
    b hmono heq hlim
  obtain ⟨ε,D₁,hε,hD₁,hnear⟩ := payOnce_inactive_upper_entry_response_error Γ B F g ρ h hlocal
  obtain ⟨D₂,hD₂,hfar⟩ := payOnce_inactive_far_above_response Γ B F g ρ h hε
  have hFOC := payOnce_inactive_eventual_pure_first_order Γ B F g ρ h b heq
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbarpos := (payOnce_inactive_population_price Γ B F g ρ h).2.eventually
    (eventually_gt_nhds hL)
  refine ⟨D₀+D₁+D₂,by positivity,?_⟩
  filter_upwards [hlower,hnear,hfar,hFOC,hbarpos] with t hlo hnwin hfw hf hbp
  filter_upwards [hlo,hf] with v hlv hfv
  have hδ : 0 ≤ (M t:ℝ)^(-(1:ℝ)/2) := rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hvg : g < v
  · by_cases hbl : b t v ≤ bar t
    · exact (hlv hvg hbl).trans (mul_le_mul_of_nonneg_right (by linarith) hδ)
    · have hbw := max_eq_left (sub_pos.mpr hvg).le
      rw [hbw]
      by_cases hbnear : b t v ≤ bar t+ε
      · exact (hnwin (v-g) (b t v) ⟨le_of_not_ge hbl,hbnear⟩ (hfv hvg).2.2).trans
          (mul_le_mul_of_nonneg_right (by linarith) hδ)
      · exact (hfw (v-g) (b t v) (le_of_not_ge hbnear) (hfv hvg).2.2).2.trans
          (mul_le_mul_of_nonneg_right (by linarith) hδ)
  · have hw : max (v-g) 0 = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt hvg))
    have hbzero : b t v=0 := le_antisymm (by simpa only [hw] using (hbound t v).2) (hbound t v).1
    rw [hw,hbzero,Limit.pStar_eq_zero_of_le hn hbp.le hbp.le]
    simp only [allocation_eq_zero_of_nonpos hn _ (le_refl (0:ℝ)),integral_zero,sub_zero,abs_zero]
    positivity

theorem payOnce_inactive_uniform_response_error
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    ∃ b : ℕ → ℝ → ℝ, (∀ t, Monotone (b t)) ∧ (∀ t, Measurable (b t)) ∧
      (∀ t v, 0 ≤ b t v ∧ b t v ≤ max (v-g) 0) ∧
      (∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1) ∧
      (∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop (𝓝 (Limit.bidStar (k+1) L (max (v-g) 0)))) ∧
      ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ᵐ v ∂F,
        |(∫ r, allocation (k+1) (C t) hn r (b t v) ∂μ t)-
          Limit.pStar (k+1) (bar t) (max (v-g) 0)| ≤ D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  obtain ⟨_,_,b,hmono,hmeas,hbound,heq,hlim⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  exact ⟨b,hmono,hmeas,hbound,heq,hlim,
    payOnce_inactive_response_error_for_pure Γ B F g ρ h hlocal b hmono hbound heq hlim⟩

end FCAppendix.Bayes
