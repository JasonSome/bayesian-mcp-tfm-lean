import FCAppendix.PayOnce.ValueDemandIdentification

namespace FCAppendix.PayOnce.AnalyticalRareSuccess
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open CompactifiedBidLaws AnalyticalKernel KernelTailEvent

theorem value_demand_eq_of_graph_limit_nonneg
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (b w : ∀ t, Ω t → ℝ) (hb : ∀ t, Measurable (b t)) (hw : ∀ t, Measurable (w t))
    (G : ℕ → ProbabilityMeasure ℝ) (hbLaw : ∀ t, (G t : Measure ℝ) = (P t).map (b t))
    (hnonneg : ∀ t, ∀ᵐ x ∂(G t : Measure ℝ), 0 ≤ x)
    (μW : Measure ℝ) [IsProbabilityMeasure μW] (hwLaw : ∀ t, μW = (P t).map (w t))
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {n : ℕ} (hn : 2 ≤ n) {L ρ : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hgraph : ∀ f : ℝ × ℝ → ℝ, Continuous f →
      (∀ w : ℝ, 0 ≤ w → f (w,Limit.bidStar n L w) = 0) →
      ∀ δ : ℝ, 0 < δ → Tendsto (fun t => P t {x | δ ≤ f (w t x,b t x)}) atTop (𝓝 0)) :
    Limit.demand μW n L = ρ := by
  have herr := kernel_error_tendsto_zero_of_graph_limit P b w hb hw hn hL hgraph
  have hK t : Integrable (fun x => kernel n (b t x) L) (P t) :=
    UnitInterval.integrable _ _ ((continuous_kernel_bid hn hL).measurable.comp (hb t))
      (fun x => (kernel_bounds hn hL (b t x)).1) (fun x => (kernel_bounds hn hL (b t x)).2)
  have hp t : Integrable (fun x => Limit.pStar n L (w t x)) (P t) :=
    UnitInterval.integrable _ _ ((Limit.measurable_pStar n L).comp (hw t))
      (fun _ => Limit.pStar_nonneg) (fun _ => Limit.pStar_le_one hL.le)
  have he t : (∫ x, kernel n x L ∂(G t : Measure ℝ))-Limit.demand μW n L =
      ∫ x, kernel n (b t x) L-Limit.pStar n L (w t x) ∂P t := by
    rw [hbLaw t,integral_map (hb t).aemeasurable (continuous_kernel_bid hn hL).aestronglyMeasurable]
    unfold Limit.demand
    rw [hwLaw t,integral_map (hw t).aemeasurable (Limit.continuous_pStar hn hL).aestronglyMeasurable,
      integral_sub (hK t) (hp t)]
  have ht : Tendsto (fun t => ∫ x, kernel n x L ∂(G t : Measure ℝ)) atTop
      (𝓝 (Limit.demand μW n L)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq,he]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun _ => abs_integral_le_integral_abs) herr
  have hlim := tendsto_rival_kernel_mean_nonneg hn G hnonneg hweak hL
  rw [hroot] at hlim
  exact tendsto_nhds_unique ht hlim

end FCAppendix.PayOnce.AnalyticalRareSuccess
