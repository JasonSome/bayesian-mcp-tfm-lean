import FCAppendix.Affine.Uniform07.OutcomeIntegrals

namespace FCAppendix.Affine.Uniform07
open MeasureTheory Set

theorem source_profile_coverage_integral (i : Row) :
    1-cutoff i+
      (∫ v in entry i..cutoff i,
        2*activeMarginal (entry i) v-(activeMarginal (entry i) v)^2) =
      limitCoverage i := by
  have ht := cutoff_pos i
  have hx : x i ∈ Ioo (0:ℝ) 1 := by cases i <;> norm_num [x,xQ]
  have hl : 0 < entry i := mul_pos hx.1 ht
  have hlt : entry i ≤ cutoff i := by unfold entry; nlinarith [hx.2]
  have hc : ContinuousOn (activeMarginal (entry i)) (uIcc (entry i) (cutoff i)) := by
    unfold activeMarginal
    refine continuousOn_const.sub (continuousOn_const.div continuousOn_id ?_)
    intro v hv
    rw [uIcc_of_le hlt] at hv
    exact (hl.trans_le hv.1).ne'
  rw [intervalIntegral.integral_sub
    (f := fun v => 2*activeMarginal (entry i) v)
    (g := fun v => (activeMarginal (entry i) v)^2)
    (hc.const_mul 2).intervalIntegrable (hc.pow 2).intervalIntegrable,
    intervalIntegral.integral_const_mul]
  have h := source_profile_integrals i
  rw [h.1]
  unfold limitCoverage
  linarith [h.2]

theorem source_profile_strict_comparisons :
    (∫ v in entry .first..cutoff .first,(activeMarginal (entry .first) v)^2) <
      (∫ v in entry .second..cutoff .second,(activeMarginal (entry .second) v)^2) ∧
    1-cutoff .second+
      (∫ v in entry .second..cutoff .second,
        2*activeMarginal (entry .second) v-(activeMarginal (entry .second) v)^2) <
      1-cutoff .first+
      (∫ v in entry .first..cutoff .first,
        2*activeMarginal (entry .first) v-(activeMarginal (entry .first) v)^2) := by
  rw [(source_profile_integrals .first).1, (source_profile_integrals .second).1,
    source_profile_coverage_integral, source_profile_coverage_integral]
  exact strict_aggregates

theorem source_test_type_predictions :
    entry .second < testValue ∧ testValue < cutoff .second ∧
    (49009354366/10^11:ℝ) < testSuccess ∧ testSuccess < 49009354367/10^11 ∧
    (116680848997/10^11:ℝ) < testMultiplicity ∧
      testMultiplicity < 116680848998/10^11 := by
  exact ⟨entry_test_order, cutoff_test_order.2, pointwise_numbers⟩

end FCAppendix.Affine.Uniform07
