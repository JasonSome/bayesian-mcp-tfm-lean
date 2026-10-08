import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem integral_prod_uniform_fin {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ}
    (f : Ω → Fin m → ℝ) (hf : ∀ i, Measurable (fun ω => f ω i))
    (C : ℝ) (hb : ∀ ω i, ‖f ω i‖ ≤ C) :
    (∫ z : Ω × Fin m, f z.1 z.2 ∂P.prod (uniformOn univ)) =
      ∫ ω, (∑ i, f ω i)/m ∂P := by
  classical
  have hu : (uniformOn (univ : Set (Fin m))) = (m : ℝ≥0∞)⁻¹ • Measure.count := by
    ext s hs
    simp only [uniformOn_univ, Fintype.card_fin, Measure.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  have hI : Integrable (fun z : Ω × Fin m => f z.1 z.2) (P.prod (uniformOn univ)) :=
    Integrable.of_bound (measurable_from_prod_countable_left hf).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hb z.1 z.2)
  rw [integral_prod _ hI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    change (∫ i, f ω i ∂uniformOn univ) = (∑ i, f ω i)/m
    rw [hu, integral_smul_measure, integral_count]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]

end FCAppendix.Probability
