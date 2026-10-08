import FCAppendix.PayOnce.CompactifiedBidLaws
import FCAppendix.PayOnce.KernelDemand
import FCAppendix.Probability.EmpiricalMean

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open KernelLawConvergence KernelTailEvent CompactifiedBidLaws
open scoped BigOperators

theorem tendsto_rival_kernel_mean_nonneg
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t => ∫ b, kernel n b T ∂(G t : Measure ℝ)) atTop
      (𝓝 (KernelDemand.demand n (G₀ : Measure ENNReal) T)) := by
  let f := KernelDemand.boundedKernel hn hT
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f
  have he t : (∫ b, f b ∂(scaledLaw (G t) 1 : Measure ENNReal)) =
      ∫ b, kernel n b T ∂(G t : Measure ℝ) := by
    change (∫ b, f b ∂Measure.map (fun b : ℝ => ENNReal.ofReal (b/1)) (G t : Measure ℝ)) = _
    simp only [div_one]
    rw [integral_map ENNReal.measurable_ofReal.aemeasurable f.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hpos t] with b hb
    exact compactKernel_ofReal n hb T
  simp_rw [he] at ht
  exact ht

theorem tendsto_rival_kernel_error_nonneg
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 ≤ b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      |(∑ j, kernel n (r j) T)/(N t:ℝ)-KernelDemand.demand n (G₀ : Measure ENNReal) T|
        ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) atTop (𝓝 0) := by
  let D := KernelDemand.demand n (G₀ : Measure ENNReal) T
  let a := fun t => ∫ b, kernel n b T ∂(G t : Measure ℝ)
  have ha : Tendsto a atTop (𝓝 D) := tendsto_rival_kernel_mean_nonneg hn G hpos hweak hT
  have hi := Probability.iid_empiricalMean_L1_tendsto_zero (fun t => (G t : Measure ℝ))
    (fun _ b => kernel n b T) (fun _ => (continuous_kernel_bid hn hT).aestronglyMeasurable)
    1 zero_le_one (fun _ => Eventually.of_forall fun b => by
      rw [abs_of_nonneg (kernel_bounds hn hT b).1]
      exact (kernel_bounds hn hT b).2) N hN
  have hI t (u : ℝ) : Integrable (fun r : Fin (N t) → ℝ => |(∑ j, kernel n (r j) T)/(N t:ℝ)-u|)
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) := by
    apply Integrable.abs
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.div_const
    apply integrable_finsetSum
    intro j _
    exact UnitInterval.integrable _ _ ((continuous_kernel_bid hn hT).measurable.comp (measurable_pi_apply j))
      (fun r => (kernel_bounds hn hT (r j)).1) (fun r => (kernel_bounds hn hT (r j)).2)
  have ht := hi.add ((ha.sub_const D).abs)
  simp only [sub_self, abs_zero, add_zero] at ht
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ ht
  intro t
  have hh := integral_mono (hI t D) ((hI t (a t)).add (integrable_const |a t-D|))
    (fun r => abs_sub_le ((∑ j, kernel n (r j) T)/(N t:ℝ)) (a t) D)
  simpa only [Pi.add_apply, integral_add (hI t (a t)) (integrable_const _),
    integral_const, probReal_univ, one_smul] using hh

theorem tendsto_rival_kernel_mean
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t => ∫ b, kernel n b T ∂(G t : Measure ℝ)) atTop
      (𝓝 (KernelDemand.demand n (G₀ : Measure ENNReal) T)) :=
  tendsto_rival_kernel_mean_nonneg hn G (fun t => (hpos t).mono fun _ hb => hb.le) hweak hT

theorem tendsto_rival_kernel_error
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      |(∑ j, kernel n (r j) T)/(N t:ℝ)-KernelDemand.demand n (G₀ : Measure ENNReal) T|
        ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) atTop (𝓝 0) :=
  tendsto_rival_kernel_error_nonneg N hN hn G
    (fun t => (hpos t).mono fun _ hb => hb.le) hweak hT

end FCAppendix.PayOnce.AnalyticalKernel
