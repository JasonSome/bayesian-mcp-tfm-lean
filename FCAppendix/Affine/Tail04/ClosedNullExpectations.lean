import FCAppendix.Affine.LowBody.DeviationWeakPayoff
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.ClosedNullExpectations
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

private theorem weak_integral_metrizable {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] [MetrizableSpace Y]
    (g : Y→ℝ) (hg : Measurable g) (S : Set Y) (hS : IsClosed S)
    (hc : ∀ y∉S,ContinuousAt g y) {C : ℝ} (hC : 0≤C)
    (hb : ∀ y,|g y|≤C)
    (ν : ℕ→ProbabilityMeasure Y) (ν₀ : ProbabilityMeasure Y)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hn : (ν₀ : Measure Y) S=0) :
    Tendsto (fun n=>∫ y,g y ∂(ν n : Measure Y)) atTop
      (𝓝 (∫ y,g y ∂(ν₀ : Measure Y))) := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact LowBody.tendsto_integral_of_closed_null_discontinuities g hg S hS hc hC hb ν ν₀ hν hn

variable {P X : Type*}
  [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
  [CompactSpace P] [MetrizableSpace P]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [MetrizableSpace X]

def experiment (p : P) (μ : ProbabilityMeasure X) : ProbabilityMeasure (P×X) :=
  productLaw (diracProba p) μ

lemma continuous_experiment :
    Continuous (fun z : P×ProbabilityMeasure X => experiment z.1 z.2) :=
  continuous_productLaw.comp ((continuous_diracProba.comp continuous_fst).prodMk continuous_snd)

omit [BorelSpace X] in
lemma integral_experiment (p : P) (μ : ProbabilityMeasure X) (f : P×X→ℝ)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ z,|f z|≤ C) :
    (∫ z,f z ∂(experiment p μ : Measure _))=∫ x,f (p,x) ∂(μ : Measure _) := by
  have hi : Integrable f ((Measure.dirac p).prod (μ : Measure X)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound z)
  change (∫ z,f z ∂((Measure.dirac p).prod (μ : Measure X)))=_
  rw [integral_prod _ hi]
  simp

set_option maxHeartbeats 800000 in
theorem tendsto_localized
    (f : P×X→ℝ) (hf : Measurable f)
    (S : Set (P×X)) (hS : IsClosed S)
    (hcont : ∀ z∉S,ContinuousAt f z)
    {C : ℝ} (hC : 0≤ C) (hbound : ∀ z,|f z|≤ C)
    (p : ℕ→ P) (p₀ : P) (hp : Tendsto p atTop (𝓝 p₀))
    (μ : ℕ→ ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (hnull : (experiment p₀ μ₀ : Measure _) S=0)
    (a : C(P×X,ℝ)) :
    Tendsto (fun n=>∫ x,a (p n,x)*f (p n,x) ∂(μ n : Measure _)) atTop
      (𝓝 (∫ x,a (p₀,x)*f (p₀,x) ∂(μ₀ : Measure _))) := by
  have hb (z : P×X) : |a z*f z|≤‖a‖*C := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z)
      (hbound z) (abs_nonneg _) (norm_nonneg _)
  have hc (z : P×X) (hz : z∉S) : ContinuousAt (fun z=> a z*f z) z :=
    a.continuous.continuousAt.mul (hcont z hz)
  have hm : Measurable (fun z : P×X=> a z*f z) := a.continuous.measurable.mul hf
  have hpμ : Tendsto (fun n => (p n,μ n)) atTop (𝓝 (p₀,μ₀)) := hp.prodMk_nhds hμ
  let E : P×ProbabilityMeasure X → ProbabilityMeasure (P×X) :=
    fun z => experiment z.1 z.2
  have hEc : Continuous E := continuous_experiment
  have ht₀ := hEc.tendsto (p₀,μ₀)
  have ht := ht₀.comp hpμ
  have h := weak_integral_metrizable
    (fun z : P×X=> a z*f z) hm S hS hc (mul_nonneg (norm_nonneg _) hC) hb
    (fun n=> experiment (p n) (μ n)) (experiment p₀ μ₀) ht hnull
  have he (q : P) (ν : ProbabilityMeasure X) :
      (∫ z,a z*f z ∂(experiment q ν : Measure (P×X))) =
        ∫ x,a (q,x)*f (q,x) ∂(ν : Measure X) :=
    integral_experiment q ν (fun z => a z*f z) hm hb
  simp_rw [he] at h
  exact h

theorem tendsto_integral
    (f : P×X→ℝ) (hf : Measurable f)
    (S : Set (P×X)) (hS : IsClosed S)
    (hcont : ∀ z∉S,ContinuousAt f z)
    {C : ℝ} (hC : 0≤ C) (hbound : ∀ z,|f z|≤ C)
    (p : ℕ→ P) (p₀ : P) (hp : Tendsto p atTop (𝓝 p₀))
    (μ : ℕ→ ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 μ₀))
    (hnull : (experiment p₀ μ₀ : Measure _) S=0) :
    Tendsto (fun n=>∫ x,f (p n,x) ∂(μ n : Measure _)) atTop
      (𝓝 (∫ x,f (p₀,x) ∂(μ₀ : Measure _))) := by
  simpa only [ContinuousMap.const_apply,one_mul] using
    tendsto_localized f hf S hS hcont hC hbound p p₀ hp μ μ₀ hμ hnull
      (ContinuousMap.const _ (1:ℝ))

end FCAppendix.Affine.Tail04.ClosedNullExpectations
