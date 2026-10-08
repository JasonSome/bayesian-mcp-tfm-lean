import FCAppendix.PayOnce.ActualConcentration
import FCAppendix.PayOnce.ActivePairCovariance

namespace FCAppendix.Bayes
open MeasureTheory Set
open PayOnce.CovarianceConcentration

theorem boundedTypeStatistic_pos (v : ℝ) : 0 < boundedTypeStatistic v := by
  have h := div_lt_div_of_pos_right (Real.neg_pi_div_two_lt_arctan v) Real.pi_pos
  have he : -(Real.pi/2)/Real.pi = -(1/2:ℝ) := by field_simp
  rw [he] at h
  dsimp only [boundedTypeStatistic]
  linarith

noncomputable def activeTypeStatistic (g v : ℝ) : ℝ :=
  if g < v then boundedTypeStatistic v else 0

theorem measurable_activeTypeStatistic (g : ℝ) : Measurable (activeTypeStatistic g) :=
  boundedTypeStatistic_measurable.ite measurableSet_Ioi measurable_const

theorem activeTypeStatistic_bounds (g v : ℝ) : activeTypeStatistic g v ∈ Icc (0:ℝ) 1 := by
  unfold activeTypeStatistic
  split_ifs
  · exact boundedTypeStatistic_bounds v
  · exact ⟨le_rfl,zero_le_one⟩

theorem activeTypeStatistic_pos_iff (g v : ℝ) : 0 < activeTypeStatistic g v ↔ g < v := by
  by_cases hv : g < v
  · simp only [activeTypeStatistic,hv,if_true,iff_true]
    exact boundedTypeStatistic_pos v
  · simp [activeTypeStatistic,hv]

theorem activeTypeStatistic_monotone (g : ℝ) : Monotone (activeTypeStatistic g) := by
  intro v w hvw
  by_cases hv : g < v
  · simp only [activeTypeStatistic,if_pos hv,if_pos (hv.trans_le hvw)]
    exact boundedTypeStatistic_strictMono.monotone hvw
  · rw [activeTypeStatistic,if_neg hv]
    exact (activeTypeStatistic_bounds g w).1

theorem positiveMask_activeTypeStatistic (g v : ℝ) :
    positiveMask (activeTypeStatistic g v) = if g < v then 1 else 0 := by
  simp only [positiveMask,activeTypeStatistic_pos_iff]

theorem activeTypeStatistic_map_positive_atomless (F : Measure ℝ) (g : ℝ)
    (hatom : ∀ v : ℝ, g < v → F {v} = 0) {b : ℝ} (hb : 0 < b) :
    (F.map (activeTypeStatistic g)) {b} = 0 := by
  rw [Measure.map_apply (measurable_activeTypeStatistic g) (measurableSet_singleton b)]
  let S := (activeTypeStatistic g) ⁻¹' {b}
  change F S = 0
  by_cases hS : S.Nonempty
  · obtain ⟨v,hv⟩ := hS
    have hve : activeTypeStatistic g v = b := hv
    have hvpos : g < v := (activeTypeStatistic_pos_iff g v).mp (hve ▸ hb)
    apply measure_mono_null (t := {v}) ?_ (hatom v hvpos)
    intro u hu
    have hue : activeTypeStatistic g u = b := hu
    have hupos : g < u := (activeTypeStatistic_pos_iff g u).mp (hue ▸ hb)
    apply boundedTypeStatistic_strictMono.injective
    simpa only [activeTypeStatistic,if_pos hupos,if_pos hvpos] using hue.trans hve.symm
  · rw [Set.not_nonempty_iff_eq_empty.mp hS,measure_empty]

end FCAppendix.Bayes
