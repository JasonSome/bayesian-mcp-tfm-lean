import FCAppendix.Probability.L1WeakConvergence

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Filter Topology

theorem tendstoInDistribution_congr_eventually
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X Y : (t : ℕ) → Ω t → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ t, Measurable (X t)) (hY : TendstoInDistribution Y atTop Z μ ν)
    (he : ∀ᶠ t in atTop, X t =ᵐ[μ t] Y t) :
    TendstoInDistribution X atTop Z μ ν := by
  refine ⟨fun t => (hX t).aemeasurable,hY.aemeasurable_limit,?_⟩
  apply hY.tendsto.congr'
  filter_upwards [he] with t ht
  apply Subtype.ext
  exact (Measure.map_congr ht).symm

end FCAppendix.Probability
