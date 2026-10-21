import FCAppendix.Affine.Tail04.OriginalCompactLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalValues
open MeasureTheory ProbabilityTheory Set

instance compactConditional_atomless (μ : Measure ℝ) [NullSingletonClass μ]
    (l u : ℝ) (hlu : l ≤ u) : NullSingletonClass (compactConditional μ l u hlu) := by
  constructor
  intro x
  have hz : cond μ (Icc l u) ({x.1} : Set ℝ) = 0 := by
    rw [cond_apply measurableSet_Icc]
    rw [measure_mono_null inter_subset_right (measure_singleton x.1),mul_zero]
  have he := congrArg (fun ν : Measure ℝ => ν ({x.1} : Set ℝ))
    (compactConditional_real μ l u hlu)
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton x.1)] at he
  have hp : Subtype.val ⁻¹' ({x.1} : Set ℝ) = ({x} : Set (Icc l u)) := by
    ext y
    simp only [mem_preimage,mem_singleton_iff,Subtype.ext_iff]
  rw [hp] at he
  exact he.trans hz

end FCAppendix.Affine.Tail04.OriginalValues

namespace FCAppendix.Affine.Tail04.ValueParameters
open MeasureTheory
variable (P : ValueParameters)

instance originalLowLaw_atomless : NullSingletonClass P.originalLowLaw := by
  dsimp only [originalLowLaw]
  infer_instance

instance originalPartialLaw_atomless : NullSingletonClass P.originalPartialLaw := by
  dsimp only [originalPartialLaw]
  infer_instance

instance originalMovingActiveLaw_atomless (t : ℝ) (ht : P.M ≤ t) :
    NullSingletonClass (P.originalMovingActiveLaw t ht) := by
  dsimp only [originalMovingActiveLaw]
  infer_instance

end FCAppendix.Affine.Tail04.ValueParameters
