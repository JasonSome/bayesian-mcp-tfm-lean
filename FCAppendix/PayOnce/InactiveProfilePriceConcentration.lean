import FCAppendix.PayOnce.ProfilePriceConcentration
import FCAppendix.PayOnce.InactivePriceConcentration

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.PriceConcentration
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_profile_price_concentration
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ ε : ℝ, 0 ≤ ε →
      (Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | ε ≤ |DummyKernel.sampleProfilePrice (k+1) (C t)
          (by have := h.proposers_two; omega) r-
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|} ≤
        6*Real.exp (-d*(M t:ℝ))+
          (2*Real.exp 8)*Real.exp (-(M t:ℝ)*ε^2/(2*K^2)) := by
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let G := fun t => BidScaling.realBidLaw (Γ t)
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop
      (𝓝 (inactiveLimitBidLaw F (k+1) g
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) := by
    simpa only [G,BidScaling.scaled_realBidLaw_one] using hweak
  obtain ⟨hL,hroot,huniq,a,z,ha,haz,hz,hwin⟩ :=
    payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  obtain ⟨ℓ,u,q,d,hℓ,hℓL,hLu,hua,hzℓ,hq,hd,he⟩ :=
    exists_eventually_price_concentration M h.population_grows hn G
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hL hroot huniq
      h.capacity_ratio ha haz hz hwin
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hzpos : 0 < z := ((hL.trans hLu).trans hua).trans haz
  refine ⟨((k+1:ℕ):ℝ)*z/q,d,by positivity,hd,?_⟩
  filter_upwards [he,hbar.eventually_const_lt hℓL,hbar.eventually_lt_const hLu,
    payOnce_inactive_population_kernel_mean Γ B F g ρ h,
    h.population_grows.eventually_gt_atTop 0] with t ht htlo hthi htmean htM
  intro ε hε
  have hbias : |(∫ b, kernel (k+1) b (bar t) ∂(G t : Measure ℝ))-(C t:ℝ)/(M t:ℝ)| ≤
      1/(M t:ℝ) := by rw [htmean,sub_self,abs_zero]; positivity
  have hh := profilePrice_tail_le_bad_add_gaussian hn htM (G t : Measure ℝ)
    hℓ ⟨htlo.le,hthi.le⟩ hua haz hzℓ hq hbias hε
  simp only [DummyKernel.sampleProfilePrice_eq hn htM]
  change (Measure.pi (fun _ : Fin (M t) => (G t : Measure ℝ))).real
      {r | ε ≤ |DummyKernel.profilePrice (k+1) (C t) hn htM r-bar t|} ≤ _
  have hbad := ht.1
  linarith

end FCAppendix.Bayes
