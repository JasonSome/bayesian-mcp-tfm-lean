import FCAppendix.PayOnce.InactivePopulationPrice
import FCAppendix.PayOnce.KernelMomentConvergence
import FCAppendix.PayOnce.GaussianParameters

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.KernelLawConvergence
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem inactiveLimitBidLaw_kernel_variance
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ) {n : ℕ} (hn : 2 ≤ n)
    {L : ℝ} (hL : 0 < L) :
    variance (fun b => compactKernel n b L) (inactiveLimitBidLaw F n g L : Measure ENNReal) =
      variance (Limit.pStar n L) (F.map (fun v => max (v-g) 0)) := by
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  have hbid : Measurable (fun v : ℝ => ENNReal.ofReal (Limit.bidStar n L (max (v-g) 0))) :=
    ENNReal.measurable_ofReal.comp (measurable_inactiveLimitBid n g L)
  rw [inactiveLimitBidLaw_toMeasure,
    variance_map (continuous_compactKernel hn hL).measurable.aemeasurable
      hbid.aemeasurable,
    variance_map (Limit.measurable_pStar n L).aemeasurable hnet.aemeasurable]
  congr 1
  funext v
  simp only [Function.comp_apply,compactKernel_ofReal n (Limit.bidStar_nonneg hn hL _),
    Limit.kernel_bidStar hn hL]

theorem payOnce_inactive_kernel_variance_tendsto
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let Lm := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    Tendsto (fun t => variance (fun b => compactKernel (k+1) b (Lm t))
      (bidLaw (Γ t) : Measure ENNReal)) atTop
        (𝓝 (variance (Limit.pStar (k+1) L) (F.map (fun v => max (v-g) 0)))) := by
  have hk := h.proposers_two
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hroot := payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  have hp := payOnce_inactive_population_price Γ B F g ρ h
  have hpos : ∀ᶠ t in atTop, 0 < KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)) := by
    filter_upwards [hp.1] with t ht
    exact (KernelDemand.populationPrice_spec ht.exists).1
  have hv := KernelDemand.tendsto_kernel_variance_of_eventually_pos (n := k+1) (by omega)
    hweak hpos hroot.1 hp.2
  rwa [inactiveLimitBidLaw_kernel_variance F g (n := k+1) (by omega) hroot.1] at hv

theorem payOnce_inactive_kernel_variance_eventually_pos
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let v := variance (Limit.pStar (k+1) L) (F.map (fun v => max (v-g) 0))
    0 < v ∧ ∀ᶠ t in atTop, v/2 ≤ variance (fun b => compactKernel (k+1) b
      (KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))))
        (bidLaw (Γ t) : Measure ENNReal) := by
  have hk := h.proposers_two
  let μW := F.map (fun v => max (v-g) 0)
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  have hL := (payOnce_inactive_limit_root_window Γ B F g ρ h
    (payOnce_inactive_bidLaw_tendsto Γ B F g ρ h)).1
  have hv := GaussianParameters.variance_pos μW (n := k+1) (by omega) hL hlocal
  exact ⟨hv,(payOnce_inactive_kernel_variance_tendsto Γ B F g ρ h).eventually_const_le (by linarith)⟩

end FCAppendix.Bayes
