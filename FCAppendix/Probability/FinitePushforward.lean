import FCAppendix.Probability.CountPushforward
import Mathlib.MeasureTheory.Constructions.Pi

namespace FCAppendix
namespace FiniteLaw

open MeasureTheory
open scoped BigOperators

variable {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

omit [Fintype α] in
theorem integrable_finite_fiber [DecidableEq α] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → α) (hf : Measurable f) (a : α) :
    Integrable (fun ω => if f ω = a then (1 : ℝ) else 0) μ := by
  classical
  have h := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).indicator
    (hf (measurableSet_singleton a))
  convert h using 1 <;> first | rfl | (ext ω; simp [Set.indicator])

noncomputable def ofMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → α) (hf : Measurable f) : FiniteLaw α := by
  classical
  exact
    { mass a := ∫ ω, (if f ω = a then (1 : ℝ) else 0) ∂μ
      nonneg a := integral_nonneg (fun ω => by split <;> norm_num)
      total := by
        rw [← integral_finsetSum Finset.univ (fun a _ => integrable_finite_fiber μ f hf a)]
        simp [eq_comm] }

theorem ofMeasure_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → α) (hf : Measurable f) (a : α) :
    (ofMeasure μ f hf).mass a = (μ {ω | f ω = a}).toReal := by
  classical
  simpa only [ofMeasure, Set.indicator, Set.mem_setOf_eq, Pi.one_apply,
    measureReal_def, Set.preimage, Set.mem_singleton_iff] using integral_indicator_one (μ := μ) (hf (measurableSet_singleton a))

theorem expect_ofMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → α) (hf : Measurable f) (g : α → ℝ) :
    (ofMeasure μ f hf).expect g = ∫ ω, g (f ω) ∂μ := by
  classical
  unfold expect ofMeasure
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum Finset.univ
    (fun a _ => (integrable_finite_fiber μ f hf a).mul_const (g a))]
  simp [ite_mul, eq_comm]

theorem ofMeasure_congr_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → α) (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    ofMeasure μ f hf = ofMeasure μ g hg := by
  classical
  apply FiniteLaw.ext
  intro a
  apply integral_congr_ae
  filter_upwards [h] with ω hω
  rw [hω]

theorem ofMeasure_map [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → α) (hf : Measurable f) (g : α → β) (hg : Measurable g) :
    (ofMeasure μ f hf).map g = ofMeasure μ (g ∘ f) (hg.comp hf) := by
  apply ext_expect
  intro h
  rw [expect_map, expect_ofMeasure, expect_ofMeasure]
  rfl

theorem ofMeasure_eq_of_map_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (f : Ω → α) (hf : Measurable f) (g : Ω' → α) (hg : Measurable g)
    (h : μ.map f = ν.map g) : ofMeasure μ f hf = ofMeasure ν g hg := by
  apply FiniteLaw.ext
  intro a
  rw [ofMeasure_mass, ofMeasure_mass]
  have he := congrArg (fun ξ : Measure α => ξ {a}) h
  simpa only [Measure.map_apply hf (measurableSet_singleton a),
    Measure.map_apply hg (measurableSet_singleton a), Set.preimage, Set.mem_singleton_iff] using congrArg ENNReal.toReal he

theorem ofMeasure_comp_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (T : Ω → Ω') (hT : MeasurePreserving T μ ν) (f : Ω' → α) (hf : Measurable f) :
    ofMeasure μ (f ∘ T) (hf.comp hT.measurable) = ofMeasure ν f hf := by
  apply ofMeasure_eq_of_map_eq μ ν _ _ _ _
  rw [← Measure.map_map hf hT.measurable, hT.map_eq]

end FiniteLaw

namespace FiniteLaw

variable {α : Type*} [Fintype α]

theorem expect_le_const_of_support (μ : FiniteLaw α) (f : α → ℝ) (a : ℝ)
    (h : ∀ x, μ.mass x ≠ 0 → f x ≤ a) : μ.expect f ≤ a := by
  rw [← μ.expect_const a]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : μ.mass x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)

theorem const_le_expect_of_support (μ : FiniteLaw α) (f : α → ℝ) (a : ℝ)
    (h : ∀ x, μ.mass x ≠ 0 → a ≤ f x) : a ≤ μ.expect f := by
  rw [← μ.expect_const a]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : μ.mass x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (μ.nonneg x)

end FiniteLaw
end FCAppendix
