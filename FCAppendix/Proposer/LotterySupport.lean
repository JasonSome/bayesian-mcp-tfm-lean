import FCAppendix.Proposer.MeasurableLotteryPolicy

namespace FCAppendix.FiniteLaw

open MeasureTheory Filter Set

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

theorem probabilityMeasure_ofMeasure (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → α) (hf : Measurable f) :
    probabilityMeasure (ofMeasure ν f hf) = ν.map f := by
  apply Measure.ext_of_singleton
  intro a
  rw [probabilityMeasure_singleton, ofMeasure_mass,
    Measure.map_apply hf (measurableSet_singleton a)]
  exact ENNReal.ofReal_toReal (measure_ne_top ν _)

theorem ae_ofMeasure_mass_ne_zero (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → α) (hf : Measurable f) :
    ∀ᵐ ω ∂ν, (ofMeasure ν f hf).mass (f ω) ≠ 0 := by
  have h := probabilityMeasure_ae_mass_ne_zero (ofMeasure ν f hf)
  rw [probabilityMeasure_ofMeasure] at h
  exact (ae_map_iff hf.aemeasurable ((Set.to_countable _).measurableSet)).mp h

theorem ae_property_of_ofMeasure (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → α) (hf : Measurable f) (μ : FiniteLaw α)
    (hlaw : ofMeasure ν f hf = μ) (P : α → Prop)
    (hP : ∀ a, μ.mass a ≠ 0 → P a) : ∀ᵐ ω ∂ν, P (f ω) := by
  filter_upwards [ae_ofMeasure_mass_ne_zero ν f hf] with ω hω
  rw [hlaw] at hω
  exact hP (f ω) hω

end FCAppendix.FiniteLaw
