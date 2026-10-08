import FCAppendix.PayOnce.PopulationPrice
import FCAppendix.PayOnce.InactiveBidLawConvergence

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_limit_root_window_of_scarce
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      (∀ T, 0 < T → KernelDemand.demand (k+1) (G₀ : Measure ENNReal) T = ρ → T = L) ∧
      ∃ a z : ℝ, L < a ∧ a < z ∧ z < ((k+1:ℕ):ℝ)*L ∧
        0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)) := by
  obtain ⟨N,hN,rfl⟩ := exists_successor_population h.population_grows
    (fun t => (hc t).trans (hcm t))
  have hρ : Tendsto (fun t => (C t:ℝ)/(N t+1)) atTop (𝓝 ρ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using h.capacity_ratio
  have hv := payOnce_inactive_bid_graph_at_value_root Γ h.proposers_two hc hcm hN
    h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values
    h.common_fee hρ h.capacity_bounds hweak
  obtain ⟨_,R,hR,huniq⟩ := payOnce_inactive_positive_capacity_root Γ h.proposers_two hc hcm
    h.population_grows h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values
    h.common_fee h.capacity_ratio h.capacity_bounds hweak
  obtain ⟨S,hS,_⟩ := payOnce_inactive_interior_bid_window Γ h.proposers_two hc hcm
    h.population_grows h.action_schedule h.base_schedule h.users B h.proposers h.symmetry
    h.positive_values_atomless h.visible_atomless h.inactive_abstain F h.common_values
    h.common_fee h.capacity_ratio h.capacity_bounds hweak
  have hLR := huniq _ ⟨hv.1,hv.2.2.1⟩
  have hSR := huniq S ⟨hS.1,hS.2.1⟩
  refine ⟨hv.1,hv.2.2.1,fun T hT hd => (huniq T ⟨hT,hd⟩).trans hLR.symm,?_⟩
  simpa only [hLR,hSR] using hS.2.2.2

theorem payOnce_inactive_limit_root_window
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    0 < L ∧ KernelDemand.demand (k+1) (G₀ : Measure ENNReal) L = ρ ∧
      (∀ T, 0 < T → KernelDemand.demand (k+1) (G₀ : Measure ENNReal) T = ρ → T = L) ∧
      ∃ a z : ℝ, L < a ∧ a < z ∧ z < ((k+1:ℕ):ℝ)*L ∧
        0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp h.eventually_scarce
  exact payOnce_inactive_limit_root_window_of_scarce (fun t => Γ (t+T)) (fun t => B (t+T)) F g ρ
    (h.along (fun t => t+T) (tendsto_add_atTop_nat T))
    (fun t => (hT (t+T) (by omega)).1) (fun t => (hT (t+T) (by omega)).2)
    (hweak.comp (tendsto_add_atTop_nat T))

theorem payOnce_inactive_population_price_of_weak
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => bidLaw (Γ t)) atTop (𝓝 G₀)) :
    (∀ᶠ t in atTop, ∃! L, 0 < L ∧
      KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) L = (C t:ℝ)/(M t)) ∧
    Tendsto (fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))) atTop
        (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
  have hk := h.proposers_two
  obtain ⟨hL,hroot,huniq,hwindow⟩ := payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  exact ⟨KernelDemand.eventually_unique_population_price (by omega) hweak h.capacity_ratio
    hL hroot huniq hwindow, KernelDemand.tendsto_population_price (by omega)
    hweak h.capacity_ratio hL hroot huniq⟩

theorem payOnce_inactive_population_price
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    (∀ᶠ t in atTop, ∃! L, 0 < L ∧
      KernelDemand.demand (k+1) (bidLaw (Γ t) : Measure ENNReal) L = (C t:ℝ)/(M t)) ∧
    Tendsto (fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))) atTop
        (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :=
  payOnce_inactive_population_price_of_weak Γ B F g ρ h
    (payOnce_inactive_bidLaw_tendsto Γ B F g ρ h)

end FCAppendix.Bayes
