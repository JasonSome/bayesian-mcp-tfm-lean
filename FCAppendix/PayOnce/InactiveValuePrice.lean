import FCAppendix.PayOnce.ValueRootRates
import FCAppendix.PayOnce.InactivePopulationPrice

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def inactiveValuePrice (M C : ℕ → ℕ) (F : Measure ℝ)
    (n : ℕ) (g : ℝ) (t : ℕ) : ℝ :=
  Limit.capRoot (F.map (fun v => max (v-g) 0)) n ((C t:ℝ)/(M t))

theorem payOnce_inactive_value_price
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    (∀ᶠ t in atTop, 0 < inactiveValuePrice M C F (k+1) g t ∧
      Limit.demand (F.map (fun v => max (v-g) 0)) (k+1)
        (inactiveValuePrice M C F (k+1) g t) = (C t:ℝ)/(M t)) ∧
    Tendsto (inactiveValuePrice M C F (k+1) g) atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  obtain ⟨hL,hroot,_⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hρW : ρ < μW.real (Ioi 0) := by
    rw [← hroot]
    exact Limit.demand_lt_positive_mass μW (by omega) hL (by rw [hroot]; exact h.capacity_bounds.1)
  refine ⟨?_,(Limit.continuousAt_capRoot μW (by omega) h.capacity_bounds.1 hρW).tendsto.comp h.capacity_ratio⟩
  filter_upwards [h.capacity_ratio.eventually (Ioo_mem_nhds h.capacity_bounds.1 hρW)] with t ht
  exact Limit.capRoot_spec μW (by omega) ht.1 ht.2

theorem payOnce_inactive_value_price_difference_isLittleO
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {s : ℕ → ℝ} (hsmall : (fun t => (C t:ℝ)/(M t)-ρ) =o[atTop] s) :
    (fun t => inactiveValuePrice M C F (k+1) g t-
      Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ) =o[atTop] s := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  obtain ⟨hL,hroot,_⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hρW : ρ < μW.real (Ioi 0) := by
    rw [← hroot]
    exact Limit.demand_lt_positive_mass μW (by omega) hL (by rw [hroot]; exact h.capacity_bounds.1)
  exact Limit.capRoot_difference_isLittleO μW (by omega) h.capacity_bounds.1 hρW
    hlocal h.capacity_ratio hsmall

theorem payOnce_inactive_price_centering_of_demand_residual
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {s : ℕ → ℝ}
    (herr : (fun t => Limit.demand (F.map (fun v => max (v-g) 0)) (k+1)
      (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))) -
        (C t:ℝ)/(M t)) =o[atTop] s) :
    (fun t => KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))-
      inactiveValuePrice M C F (k+1) g t) =o[atTop] s := by
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hk := h.proposers_two
  obtain ⟨hL,hroot,_⟩ := payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h
  have hρW : ρ < μW.real (Ioi 0) := by
    rw [← hroot]
    exact Limit.demand_lt_positive_mass μW (by omega) hL (by rw [hroot]; exact h.capacity_bounds.1)
  exact Limit.root_error_isLittleO_of_demand_error μW (by omega) h.capacity_bounds.1 hρW
    hlocal h.capacity_ratio (payOnce_inactive_population_price Γ B F g ρ h).2 herr

end FCAppendix.Bayes
