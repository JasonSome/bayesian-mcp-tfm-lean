import FCAppendix.PayOnce.InactiveServedMean
import FCAppendix.PayOnce.InactiveFixedBelowResponse
import FCAppendix.PayOnce.InactiveRegularTypes
import FCAppendix.PayOnce.InactiveDemandResidual
import FCAppendix.PayOnce.InactiveValuePrice

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_ae_response_error_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (b : ℕ → ℝ → ℝ)
    (heq : ∀ᶠ t in atTop, ∀ᵐ z ∂((Γ t).F ⊗ₘ (Γ t).σ), effectiveBid z.2 = b t z.1)
    (hlim : ∀ᵐ v ∂F, Tendsto (fun t => b t v) atTop
      (𝓝 (Limit.bidStar (k+1)
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) (max (v-g) 0)))) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∀ᵐ v ∂F, Tendsto (fun t => sqrt (M t:ℝ)*
      ((∫ r : Fin (M t-1) → ℝ, allocation (k+1) (C t) hn r (b t v)
        ∂Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ)))-
          Limit.pStar (k+1) (bar t) (max (v-g) 0))) atTop (𝓝 0) := by
  dsimp only
  have hL := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  filter_upwards [hlim,payOnce_inactive_ae_ne_entry_value Γ B F g ρ h,
    payOnce_inactive_ae_eventually_pure_first_order Γ B F g ρ h b heq] with v hv hne hFOC
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · exact payOnce_inactive_fixed_below_response Γ B F g ρ h (fun t => b t v) hlo hv
  · have hvg : g < v := by
      have hh := hL.trans hhi
      simp only [lt_max_iff,lt_self_iff_false,or_false] at hh
      linarith
    apply payOnce_inactive_fixed_served_mean_response_sqrt Γ B F g ρ h hlocal
      (fun t => b t v) hhi hv
    filter_upwards [hFOC hvg] with t ht
    simpa only [max_eq_left (sub_nonneg.mpr hvg.le)] using ht.2.2

theorem payOnce_inactive_demand_residual
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    (fun t => Limit.demand (F.map (fun v => max (v-g) 0)) (k+1)
      (KernelDemand.populationPrice (k+1)
        (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))-(C t:ℝ)/(M t))
          =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2)) := by
  obtain ⟨_hL,_hd,b,hmono,_hmeas,hbound,heq,hlim⟩ :=
    payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  apply payOnce_inactive_demand_residual_of_pointwise Γ B F g ρ h hlocal
    b hmono hbound heq hlim
  filter_upwards [payOnce_inactive_ae_response_error_sqrt Γ B F g ρ h hlocal b heq hlim]
    with v hv
  convert hv using 1
  funext t
  rw [neg_div,rpow_neg (Nat.cast_nonneg (M t)),← sqrt_eq_rpow,div_inv_eq_mul,mul_comm]

theorem payOnce_inactive_price_centering
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    (fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))-
        inactiveValuePrice M C F (k+1) g t) =o[atTop] (fun t => (M t:ℝ)^(-(1:ℝ)/2)) :=
  payOnce_inactive_price_centering_of_demand_residual Γ B F g ρ h hlocal
    (payOnce_inactive_demand_residual Γ B F g ρ h hlocal)

theorem payOnce_inactive_price_centering_sqrt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    Tendsto (fun t => sqrt (M t:ℝ)*(KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))-
        inactiveValuePrice M C F (k+1) g t)) atTop (𝓝 0) := by
  have hnz : ∀ᶠ t in atTop, (M t:ℝ)^(-(1:ℝ)/2) ≠ 0 := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    exact (rpow_pos_of_pos (Nat.cast_pos.mpr ht) _).ne'
  have hh := (Asymptotics.isLittleO_iff_tendsto' (hnz.mono fun _ ht hz => (ht hz).elim)).mp
    (payOnce_inactive_price_centering Γ B F g ρ h hlocal)
  convert hh using 1
  funext t
  rw [neg_div,rpow_neg (Nat.cast_nonneg (M t)),← sqrt_eq_rpow,div_inv_eq_mul,mul_comm]

end FCAppendix.Bayes
