import FCAppendix.Affine.Uniform07.ProfileCertificate
import FCAppendix.Affine.Uniform07.SourceLaw
import FCAppendix.Probability.PiBinomial
import FCAppendix.Probability.FiniteAveraging

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

theorem source_entry_pos (i : Uniform07.Row) : 0 < Uniform07.entry i := by
  unfold Uniform07.entry
  exact mul_pos (by cases i <;> norm_num [Uniform07.x, Uniform07.xQ])
    (Uniform07.cutoff_pos i)

theorem source_entry_lt_cutoff (i : Uniform07.Row) :
    Uniform07.entry i < Uniform07.cutoff i := by
  have ht := Uniform07.cutoff_pos i
  cases i <;> norm_num [Uniform07.entry, Uniform07.x, Uniform07.xQ] <;> nlinarith

theorem active_probability_bounds (i : Uniform07.Row) {v : ℝ}
    (hv : Uniform07.entry i ≤ v) : 1 - Uniform07.entry i / v ∈ Icc (0 : ℝ) 1 := by
  have hpos := (source_entry_pos i).trans_le hv
  have hdiv : Uniform07.entry i / v ≤ 1 := (div_le_one hpos).mpr hv
  exact ⟨by linarith, by linarith [div_nonneg (source_entry_pos i).le hpos.le]⟩

def sourceLimitLaw (i : Uniform07.Row) (v : ℝ) : CountLaw 2 :=
  if h : v < Uniform07.entry i then FiniteLaw.dirac 0
  else if v < Uniform07.cutoff i then
    IndependentCounts.binomial 2 (1 - Uniform07.entry i / v)
      (active_probability_bounds i (le_of_not_gt h)).1
      (active_probability_bounds i (le_of_not_gt h)).2
  else FiniteLaw.dirac 1

def sourceLimitMass (i : Uniform07.Row) (v : ℝ) (r : Fin 3) : ℝ :=
  if v < Uniform07.entry i then if r.val = 0 then 1 else 0
  else if v < Uniform07.cutoff i then
    let p := 1 - Uniform07.entry i / v
    if r.val = 0 then (1-p)^2 else if r.val = 1 then 2*p*(1-p) else p^2
  else if r.val = 1 then 1 else 0

theorem sourceLimitLaw_mass (i : Uniform07.Row) (v : ℝ) (r : Fin 3) :
    (sourceLimitLaw i v).mass r = sourceLimitMass i v r := by
  by_cases hv : v < Uniform07.entry i
  · rw [sourceLimitLaw, dif_pos hv, sourceLimitMass, if_pos hv]
    fin_cases r <;> norm_num [FiniteLaw.dirac]
  · rw [sourceLimitLaw, dif_neg hv, sourceLimitMass, if_neg hv]
    by_cases ht : v < Uniform07.cutoff i
    · rw [if_pos ht, if_pos ht, PiBinomial.binomial_mass]
      fin_cases r <;> norm_num [PiBinomial.pmf]
    · rw [if_neg ht, if_neg ht]
      fin_cases r <;> norm_num [FiniteLaw.dirac]

theorem sourceLimitLaw_mass_measurable (i : Uniform07.Row) (r : Fin 3) :
    Measurable (fun v => (sourceLimitLaw i v).mass r) := by
  simp_rw [sourceLimitLaw_mass]
  unfold sourceLimitMass
  apply Measurable.ite measurableSet_Iio measurable_const
  apply Measurable.ite measurableSet_Iio
  · fin_cases r <;> dsimp <;> fun_prop
  · exact measurable_const

theorem sourceLimitLaw_below (i : Uniform07.Row) {v : ℝ}
    (hv : v < Uniform07.entry i) : sourceLimitLaw i v = FiniteLaw.dirac 0 := by
  simp [sourceLimitLaw, hv]

theorem sourceLimitLaw_above (i : Uniform07.Row) {v : ℝ}
    (hv : Uniform07.cutoff i ≤ v) : sourceLimitLaw i v = FiniteLaw.dirac 1 := by
  have hl : ¬ v < Uniform07.entry i :=
    not_lt.mpr ((source_entry_lt_cutoff i).le.trans hv)
  simp [sourceLimitLaw, hl, not_lt.mpr hv]

theorem source_active_moments (i : Uniform07.Row) {v : ℝ}
    (hv : v ∈ Ico (Uniform07.entry i) (Uniform07.cutoff i)) :
    (sourceLimitLaw i v).load = 2 * Uniform07.activeMarginal (Uniform07.entry i) v ∧
    (sourceLimitLaw i v).success =
      2 * Uniform07.activeMarginal (Uniform07.entry i) v -
        (Uniform07.activeMarginal (Uniform07.entry i) v)^2 ∧
    (sourceLimitLaw i v).duplicates = (Uniform07.activeMarginal (Uniform07.entry i) v)^2 := by
  rw [sourceLimitLaw, dif_neg (not_lt.mpr hv.1), if_pos hv.2]
  have hl := IndependentCounts.binomial_load 2 (1 - Uniform07.entry i / v)
    (active_probability_bounds i hv.1).1 (active_probability_bounds i hv.1).2
  have hs := IndependentCounts.binomial_success 2 (1 - Uniform07.entry i / v)
    (active_probability_bounds i hv.1).1 (active_probability_bounds i hv.1).2
  dsimp only [Uniform07.activeMarginal]
  refine ⟨by simpa using hl, ?_, ?_⟩
  · rw [hs]
    ring
  · unfold CountLaw.duplicates
    rw [hl, hs]
    norm_num
    ring

theorem uniform_band_integral (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (f : ℝ → ℝ) :
    (∫ v, (Ioc a b).indicator f v ∂Uniform07.uniformLaw) = ∫ v in a..b, f v := by
  rw [integral_indicator measurableSet_Ioc]
  unfold Uniform07.uniformLaw
  rw [Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc a b ∩ Icc (0 : ℝ) 1 = Ioc a b := by
    apply inter_eq_left.mpr
    intro v hv
    exact ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  rw [hs, intervalIntegral.integral_of_le hab]

private theorem ae_avoid (b : ℝ) : ∀ᵐ v ∂Uniform07.uniformLaw, v ≠ b := by
  apply measure_eq_zero_iff_ae_notMem.mp
  change Uniform07.uniformLaw {b} = 0
  unfold Uniform07.uniformLaw
  exact measure_singleton b

private def activeLoad (i : Uniform07.Row) (v : ℝ) : ℝ :=
  (Ioc (Uniform07.entry i) (Uniform07.cutoff i)).indicator
    (fun w => 2 * Uniform07.activeMarginal (Uniform07.entry i) w) v

private def activeDup (i : Uniform07.Row) (v : ℝ) : ℝ :=
  (Ioc (Uniform07.entry i) (Uniform07.cutoff i)).indicator
    (fun w => (Uniform07.activeMarginal (Uniform07.entry i) w)^2) v

private def upperOne (i : Uniform07.Row) (v : ℝ) : ℝ :=
  (Ioc (Uniform07.cutoff i) 1).indicator (fun _ => (1 : ℝ)) v

private theorem profile_ae (i : Uniform07.Row) :
    ∀ᵐ v ∂Uniform07.uniformLaw,
      (sourceLimitLaw i v).load = activeLoad i v + upperOne i v ∧
      (sourceLimitLaw i v).duplicates = activeDup i v := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc,
    ae_avoid (Uniform07.entry i), ae_avoid (Uniform07.cutoff i)] with v hv hl ht
  by_cases hlow : v < Uniform07.entry i
  · have hnA : v ∉ Ioc (Uniform07.entry i) (Uniform07.cutoff i) := fun h => by linarith [h.1]
    have hnH : v ∉ Ioc (Uniform07.cutoff i) 1 := fun h =>
      (not_lt_of_ge ((source_entry_lt_cutoff i).le.trans h.1.le)) hlow
    rw [sourceLimitLaw_below i hlow]
    simp [activeLoad, activeDup, upperOne, hnA, hnH,
      CountLaw.load, CountLaw.success, CountLaw.duplicates, FiniteLaw.expect_dirac, successIndicator]
  · have hvl : Uniform07.entry i < v := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hl)
    by_cases hactive : v < Uniform07.cutoff i
    · have hA : v ∈ Ioc (Uniform07.entry i) (Uniform07.cutoff i) := ⟨hvl, hactive.le⟩
      have hnH : v ∉ Ioc (Uniform07.cutoff i) 1 := fun h => by linarith [h.1]
      have hm := source_active_moments i ⟨hvl.le, hactive⟩
      simpa [activeLoad, activeDup, upperOne, hA, hnH] using ⟨hm.1, hm.2.2⟩
    · have hvt : Uniform07.cutoff i < v := lt_of_le_of_ne (le_of_not_gt hactive) (Ne.symm ht)
      have hnA : v ∉ Ioc (Uniform07.entry i) (Uniform07.cutoff i) := fun h => by linarith [h.2]
      have hH : v ∈ Ioc (Uniform07.cutoff i) 1 := ⟨hvt, hv.2⟩
      rw [sourceLimitLaw_above i hvt.le]
      simp [activeLoad, activeDup, upperOne, hnA, hH,
        CountLaw.load, CountLaw.success, CountLaw.duplicates, FiniteLaw.expect_dirac, successIndicator]

private theorem activeLoad_integrable (i : Uniform07.Row) :
    Integrable (activeLoad i) Uniform07.uniformLaw := by
  have hm : Measurable (activeLoad i) := by
    unfold activeLoad Uniform07.activeMarginal
    exact (measurable_const.mul (measurable_const.sub (measurable_const.div measurable_id))).indicator measurableSet_Ioc
  apply Integrable.of_bound hm.aestronglyMeasurable 2
  apply Eventually.of_forall
  intro v
  by_cases hv : v ∈ Ioc (Uniform07.entry i) (Uniform07.cutoff i)
  · have hp := active_probability_bounds i hv.1.le
    simp only [activeLoad, indicator_of_mem hv, Uniform07.activeMarginal, Real.norm_eq_abs]
    rw [abs_of_nonneg (by nlinarith [hp.1])]
    nlinarith [hp.2]
  · simp [activeLoad, hv]

theorem source_actual_profile_integrals (i : Uniform07.Row) :
    (∫ v, (sourceLimitLaw i v).load ∂Uniform07.uniformLaw) = 1 - Uniform07.delta ∧
    (∫ v, (sourceLimitLaw i v).duplicates ∂Uniform07.uniformLaw) = Uniform07.limitDup i ∧
    (∫ v, (sourceLimitLaw i v).success ∂Uniform07.uniformLaw) = Uniform07.limitCoverage i := by
  have he := source_entry_lt_cutoff i
  have hL : (∫ v, (sourceLimitLaw i v).load ∂Uniform07.uniformLaw) = 1 - Uniform07.delta := by
    rw [integral_congr_ae ((profile_ae i).mono (fun _ h => h.1))]
    unfold upperOne
    rw [integral_add (activeLoad_integrable i)
        ((integrable_const (1 : ℝ)).indicator measurableSet_Ioc)]
    unfold activeLoad
    rw [uniform_band_integral _ _ (source_entry_pos i).le he.le (Uniform07.cutoff_lt_one i).le,
      uniform_band_integral _ _ (Uniform07.cutoff_pos i).le (Uniform07.cutoff_lt_one i).le le_rfl,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    linarith [(Uniform07.source_profile_integrals i).2]
  have hD : (∫ v, (sourceLimitLaw i v).duplicates ∂Uniform07.uniformLaw) = Uniform07.limitDup i := by
    rw [integral_congr_ae ((profile_ae i).mono (fun _ h => h.2))]
    unfold activeDup
    rw [uniform_band_integral _ _ (source_entry_pos i).le he.le (Uniform07.cutoff_lt_one i).le]
    exact (Uniform07.source_profile_integrals i).1
  have hiL : Integrable (fun v => (sourceLimitLaw i v).load) Uniform07.uniformLaw :=
    FiniteLaw.integrable_expect _ _ (sourceLimitLaw_mass_measurable i) _
  have hiS : Integrable (fun v => (sourceLimitLaw i v).success) Uniform07.uniformLaw :=
    FiniteLaw.integrable_expect _ _ (sourceLimitLaw_mass_measurable i) _
  refine ⟨hL, hD, ?_⟩
  have h := hD
  unfold CountLaw.duplicates at h
  rw [integral_sub hiL hiS, hL] at h
  unfold Uniform07.limitCoverage
  linarith

theorem source_test_first : sourceLimitLaw .first Uniform07.testValue = FiniteLaw.dirac 1 :=
  sourceLimitLaw_above .first Uniform07.cutoff_test_order.1.le

theorem source_test_second :
    (sourceLimitLaw .second Uniform07.testValue).success = Uniform07.testSuccess ∧
    conditionalMultiplicity (sourceLimitLaw .second Uniform07.testValue).success
      (sourceLimitLaw .second Uniform07.testValue).load = Uniform07.testMultiplicity ∧
    0 < (sourceLimitLaw .second Uniform07.testValue).success := by
  have htpos : (0 : ℝ) < Uniform07.testValue := by norm_num [Uniform07.testValue]
  have hp0 : 0 < 1 - Uniform07.entry .second / Uniform07.testValue := by
    have h := (div_lt_one htpos).mpr Uniform07.entry_test_order
    linarith
  have hp1 := (active_probability_bounds .second Uniform07.entry_test_order.le).2
  have hm := source_active_moments .second
    ⟨Uniform07.entry_test_order.le, Uniform07.cutoff_test_order.2⟩
  have hs : (sourceLimitLaw .second Uniform07.testValue).success = Uniform07.testSuccess := by
    rw [hm.2.1]
    unfold Uniform07.activeMarginal Uniform07.testSuccess
    ring
  have hbin := Uniform07.binomial_pair_outcomes ⟨hp0, hp1⟩
  refine ⟨hs, ?_, ?_⟩
  · unfold conditionalMultiplicity
    rw [hm.1, hm.2.1]
    unfold Uniform07.activeMarginal
    rw [hbin.2.1]
    unfold Uniform07.testMultiplicity
    congr 1
    ring
  · rw [hm.2.1]
    exact hbin.1

end FCAppendix.Affine.Uniform07Finishing
