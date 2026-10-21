import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace MeasureTheory.MeasurePreserving

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {T : X→ Y}

theorem integral_comp_ae_real (hT : MeasurePreserving T μ ν)
    {f : Y→ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ x,f (T x) ∂μ)=∫ y,f y ∂ν := by
  have hf' : AEStronglyMeasurable f (μ.map T) := by
    simpa only [hT.map_eq] using hf
  have h := integral_map hT.measurable.aemeasurable hf'
  rw [hT.map_eq] at h
  exact h.symm

end MeasureTheory.MeasurePreserving
