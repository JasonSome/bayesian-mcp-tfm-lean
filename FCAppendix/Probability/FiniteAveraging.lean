import FCAppendix.Probability.Bounds

noncomputable section

namespace FCAppendix.FiniteLaw

open MeasureTheory
open scoped BigOperators

variable {Ω α : Type*} [Fintype Ω] [MeasurableSpace α]

lemma mass_le_one (μ : FiniteLaw Ω) (ω : Ω) : μ.mass ω ≤ 1 := by
  classical
  rw [← μ.total]
  exact Finset.single_le_sum (fun x _ => μ.nonneg x) (Finset.mem_univ ω)

lemma norm_expect_le_sum_norm (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ‖μ.expect f‖ ≤ ∑ ω, ‖f ω‖ := by
  unfold expect
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ω _
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg ω)]
  exact mul_le_of_le_one_left (norm_nonneg _) (μ.mass_le_one ω)

lemma measurable_expect (μ : α → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) (f : Ω → ℝ) :
    Measurable (fun x => (μ x).expect f) := by
  unfold expect
  exact Finset.measurable_sum _ (fun ω _ => (hμ ω).mul_const _)

lemma integrable_expect (ν : Measure α) [IsFiniteMeasure ν] (μ : α → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) (f : Ω → ℝ) :
    Integrable (fun x => (μ x).expect f) ν :=
  Integrable.of_bound (measurable_expect μ hμ f).aestronglyMeasurable
    (∑ ω, ‖f ω‖) (Filter.Eventually.of_forall fun x => (μ x).norm_expect_le_sum_norm f)

lemma integrable_mass (ν : Measure α) [IsFiniteMeasure ν] (μ : α → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) (ω : Ω) :
    Integrable (fun x => (μ x).mass ω) ν := by
  apply Integrable.of_bound (hμ ω).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg ((μ x).nonneg ω)]
  exact (μ x).mass_le_one ω

def average (ν : Measure α) [IsProbabilityMeasure ν] (μ : α → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) : FiniteLaw Ω where
  mass ω := ∫ x, (μ x).mass ω ∂ν
  nonneg ω := integral_nonneg (fun x => (μ x).nonneg ω)
  total := by
    rw [← integral_finsetSum _ (fun ω _ => integrable_mass ν μ hμ ω)]
    simp only [FiniteLaw.total, integral_const, probReal_univ, one_smul]

lemma expect_average (ν : Measure α) [IsProbabilityMeasure ν] (μ : α → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) (f : Ω → ℝ) :
    (average ν μ hμ).expect f = ∫ x, (μ x).expect f ∂ν := by
  unfold expect average
  simp only [← integral_mul_const]
  rw [integral_finsetSum]
  intro ω _
  exact (integrable_mass ν μ hμ ω).mul_const (f ω)

def uniformAverage {m : ℕ} (hm : 0 < m) (μ : Fin m → FiniteLaw Ω) : FiniteLaw Ω where
  mass ω := (∑ i, (μ i).mass ω) / m
  nonneg ω := div_nonneg (Finset.sum_nonneg fun i _ => (μ i).nonneg ω) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [FiniteLaw.total, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast hm.ne')

lemma expect_uniformAverage {m : ℕ} (hm : 0 < m) (μ : Fin m → FiniteLaw Ω) (f : Ω → ℝ) :
    (uniformAverage hm μ).expect f = (∑ i, (μ i).expect f) / m := by
  unfold expect uniformAverage
  simp only [div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]

end FCAppendix.FiniteLaw
