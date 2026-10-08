import FCAppendix.PayOnce.ProfileConcentration
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def populationLaw (P : Measure Ω) : Measure (Ω × ι) :=
  P.prod (uniformOn (Set.univ : Set ι))

instance populationLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P] [Nonempty ι] :
    IsProbabilityMeasure (populationLaw (ι := ι) P) := inferInstanceAs (IsProbabilityMeasure (P.prod _))

theorem integral_uniform_population (f : ι → ℝ) :
    (∫ i, f i ∂uniformOn (Set.univ : Set ι)) = populationMean f := by
  have he : uniformOn (Set.univ : Set ι) = (Fintype.card ι : ENNReal)⁻¹ • Measure.count := by
    ext s hs
    rw [uniformOn_univ, Measure.smul_apply]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, integral_smul_measure, integral_count]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, populationMean, div_eq_mul_inv, mul_comm]

theorem integral_populationLaw (P : Measure Ω) [SFinite P] [Nonempty ι]
    (f : Ω → ι → ℝ) (hf : Integrable (fun z : Ω × ι => f z.1 z.2) (populationLaw P)) :
    (∫ z, f z.1 z.2 ∂populationLaw P) = ∫ ω, populationMean (f ω) ∂P := by
  rw [populationLaw, integral_prod _ hf]
  simp_rw [integral_uniform_population]

theorem integrable_populationLaw_of_bound (P : Measure Ω) [IsProbabilityMeasure P] [Nonempty ι]
    (f : Ω → ι → ℝ) (hf : ∀ i, Measurable (fun ω => f ω i)) {C : ℝ}
    (hb : ∀ ω i, ‖f ω i‖ ≤ C) :
    Integrable (fun z : Ω × ι => f z.1 z.2) (populationLaw P) :=
  Integrable.of_bound (measurable_from_prod_countable_left hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => hb z.1 z.2)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem integral_populationMean (P : Measure Ω) (f : Ω → ι → ℝ)
    (hf : ∀ i, Integrable (fun ω => f ω i) P) :
    (∫ ω, populationMean (f ω) ∂P) = populationMean (fun i => ∫ ω, f ω i ∂P) := by
  unfold populationMean
  rw [integral_div, integral_finsetSum _ (fun i _ => hf i)]

end FCAppendix.PayOnce.CovarianceConcentration
