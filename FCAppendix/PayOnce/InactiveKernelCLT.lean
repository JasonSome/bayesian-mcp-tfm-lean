import FCAppendix.PayOnce.InactiveKernelVariance
import FCAppendix.Probability.TriangularBoundedCLT

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.KernelLawConvergence PayOnce.KernelTailEvent
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem realBidLaw_kernel_mean_eq_demand {m n c : ℕ}
    (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    (∫ b, kernel n b T ∂(BidScaling.realBidLaw Γ : Measure ℝ)) =
      KernelDemand.demand n (bidLaw Γ : Measure ENNReal) T := by
  rw [KernelDemand.demand, compactifiedBidLaw_eq_map_effectiveBidLaw,
    integral_map ENNReal.measurable_ofReal.aemeasurable
      (continuous_compactKernel hn hT).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_realEffectiveBidLaw_nonneg Γ] with b hb
  exact (compactKernel_ofReal n hb T).symm

theorem realBidLaw_kernel_variance {m n c : ℕ}
    (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    variance (fun b => kernel n b T) (BidScaling.realBidLaw Γ : Measure ℝ) =
      variance (fun b => compactKernel n b T) (bidLaw Γ : Measure ENNReal) := by
  rw [compactifiedBidLaw_eq_map_effectiveBidLaw,
    variance_map (continuous_compactKernel hn hT).measurable.aemeasurable
      ENNReal.measurable_ofReal.aemeasurable]
  apply variance_congr
  filter_upwards [ae_realEffectiveBidLaw_nonneg Γ] with b hb
  exact (compactKernel_ofReal n hb T).symm

theorem payOnce_inactive_real_kernel_variance_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) {T : ℕ → ℝ}
    (hT : Tendsto T atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) :
    Tendsto (fun t => variance (fun b => kernel (k+1) b (T t))
      (BidScaling.realBidLaw (Γ t) : Measure ℝ)) atTop
        (𝓝 (variance (Limit.pStar (k+1)
          (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
          (F.map (fun v => max (v-g) 0)))) := by
  have hk := h.proposers_two
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hL := (payOnce_inactive_limit_root_window Γ B F g ρ h hweak).1
  have hpos := (tendsto_order.mp hT).1 0 hL
  have hv := KernelDemand.tendsto_kernel_variance_of_eventually_pos (n := k+1) (by omega)
    hweak hpos hL hT
  rw [inactiveLimitBidLaw_kernel_variance F g (n := k+1) (by omega) hL] at hv
  apply hv.congr'
  filter_upwards [hpos] with t ht
  exact (realBidLaw_kernel_variance (Γ t) (by omega) ht).symm

theorem payOnce_inactive_kernel_probability_le_tendsto_gaussian
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {x : ℕ → ℝ} {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (N t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Probability.iidStandardizedSum (BidScaling.realBidLaw (Γ t) : Measure ℝ)
          (fun b => kernel (k+1) b (T t)) (N t) r ≤ x t})
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) := by
  have hk := h.proposers_two
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL := (payOnce_inactive_limit_root_window Γ B F g ρ h
    (payOnce_inactive_bidLaw_tendsto Γ B F g ρ h)).1
  have hv := GaussianParameters.variance_pos μW (n := k+1) (by omega) hL hlocal
  have hvar := payOnce_inactive_real_kernel_variance_tendsto Γ B F g ρ h hT
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp ((tendsto_order.mp hT).1 0 hL)
  apply (tendsto_add_atTop_iff_nat t₀).mp
  exact Probability.iid_unitInterval_probability_le_tendsto_gaussian
    (fun t => (BidScaling.realBidLaw (Γ (t+t₀)) : Measure ℝ))
    (fun t b => kernel (k+1) b (T (t+t₀))) (fun t => N (t+t₀))
    (fun t => (continuous_kernel_bid (by omega) (ht₀ (t+t₀) (by omega))).measurable)
    (fun t => Eventually.of_forall fun b => kernel_bounds (by omega) (ht₀ (t+t₀) (by omega)) b)
    (hN.comp (tendsto_add_atTop_nat t₀)) hv
    (hvar.comp (tendsto_add_atTop_nat t₀)) (hx.comp (tendsto_add_atTop_nat t₀))

theorem payOnce_inactive_population_kernel_mean
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∀ᶠ t in atTop,
      (∫ b, kernel (k+1) b (KernelDemand.populationPrice (k+1)
        (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))
        ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ)) = (C t:ℝ)/(M t) := by
  have hk := h.proposers_two
  filter_upwards [(payOnce_inactive_population_price Γ B F g ρ h).1] with t ht
  have hp := KernelDemand.populationPrice_spec ht.exists
  rw [realBidLaw_kernel_mean_eq_demand (Γ t) (by omega) hp.1]
  exact hp.2

theorem payOnce_inactive_population_kernel_probability_le_tendsto_gaussian
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {x : ℕ → ℝ} {z : ℝ} (hx : Tendsto x atTop (𝓝 z)) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (N t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Probability.iidStandardizedSum (BidScaling.realBidLaw (Γ t) : Measure ℝ)
          (fun b => kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))) (N t) r ≤ x t})
      atTop (𝓝 (cdf (gaussianReal 0 1) z)) :=
  payOnce_inactive_kernel_probability_le_tendsto_gaussian Γ B F g ρ h hlocal
    (payOnce_inactive_population_price Γ B F g ρ h).2 N hN hx

end FCAppendix.Bayes
