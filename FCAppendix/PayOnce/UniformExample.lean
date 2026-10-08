import FCAppendix.PayOnce.LimitFormulas

namespace FCAppendix
namespace PayOnce
namespace Limit

open MeasureTheory Set Filter

noncomputable def uniformLaw : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniformLaw := ⟨by simp [uniformLaw]⟩

instance : NullSingletonClass uniformLaw := by
  unfold uniformLaw
  infer_instance

theorem uniformLaw_positive_mass : uniformLaw.real (Ioi 0) = 1 := by
  have hset : Ioi (0 : ℝ) ∩ Icc 0 1 = Ioc 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, h.1.le, h.2⟩
  rw [measureReal_def, uniformLaw, Measure.restrict_apply measurableSet_Ioi, hset,
    Real.volume_Ioc]
  norm_num

theorem pStar_two {t w : ℝ} (ht : 0 ≤ t) (htw : t < w) : pStar 2 t w = 1 - t / w := by
  rw [pStar_of_lt le_rfl ht htw]
  norm_num

theorem uniform_demand {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    demand uniformLaw 2 t = 1 - t + t * Real.log t := by
  unfold demand uniformLaw
  have hEq : EqOn (pStar 2 t) ((Ioc t 1).indicator (fun w => 1 - t / w)) (Icc 0 1) := by
    intro w hw
    by_cases htw : t < w
    · rw [indicator_of_mem (show w ∈ Ioc t 1 from ⟨htw, hw.2⟩), pStar_two ht0.le htw]
    · rw [indicator_of_notMem (show w ∉ Ioc t 1 from fun h => htw h.1),
        pStar_eq_zero_of_le le_rfl ht0.le (not_lt.mp htw)]
  rw [setIntegral_congr_fun measurableSet_Icc hEq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht0.le le_rfl)),
    ← intervalIntegral.integral_of_le ht1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun w => w - t * Real.log w)]
  · simp only [Real.log_one]
    ring
  · intro x hx
    rw [uIcc_of_le ht1] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ht0 hx.1).ne'
    exact ((hasDerivAt_id' x).sub ((Real.hasDerivAt_log hx0).const_mul t)).congr_deriv
      (by rw [div_eq_mul_inv])
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact (lt_of_lt_of_le ht0 hx.1).ne'

theorem uniform_coverage {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    coverage uniformLaw 2 t = (1 - t) ^ 2 := by
  unfold coverage uniformLaw
  have hEq : EqOn (fun w => success 2 (pStar 2 t w))
      ((Ioc t 1).indicator (fun w => 1 - (t / w) ^ 2)) (Icc 0 1) := by
    intro w hw
    by_cases htw : t < w
    · rw [indicator_of_mem (show w ∈ Ioc t 1 from ⟨htw, hw.2⟩)]
      simp only
      rw [pStar_two ht0.le htw]
      unfold success
      ring
    · rw [indicator_of_notMem (show w ∉ Ioc t 1 from fun h => htw h.1)]
      exact success_pStar_of_le le_rfl ht0.le (not_lt.mp htw)
  rw [setIntegral_congr_fun measurableSet_Icc hEq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht0.le le_rfl)),
    ← intervalIntegral.integral_of_le ht1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun w => w + t ^ 2 * w⁻¹)]
  · field_simp
    ring
  · intro x hx
    rw [uIcc_of_le ht1] at hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le ht0 hx.1).ne'
    exact ((hasDerivAt_id' x).add ((hasDerivAt_inv hx0).const_mul (t ^ 2))).congr_deriv
      (by field_simp; ring)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht1]
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    exact (lt_of_lt_of_le ht0 hx.1).ne'

section Numerics

theorem exp_lower_certificate :
    Real.exp (-167834699012 / 10 ^ 11) < 18668230884 / 10 ^ 11 := by
  have hx : |(-83917349506 / 10 ^ 11 : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> norm_num
  have h := Real.exp_bound hx (n := 16) (by norm_num)
  have habs : |(-83917349506 / 10 ^ 11 : ℝ)| = 83917349506 / 10 ^ 11 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  rw [habs] at h
  have hup := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at hup
  have he : Real.exp (-167834699012 / 10 ^ 11) = Real.exp (-83917349506 / 10 ^ 11) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  have hpos := Real.exp_pos (-83917349506 / 10 ^ 11)
  nlinarith

theorem exp_upper_certificate :
    18668230886 / 10 ^ 11 < Real.exp (-167834698992 / 10 ^ 11) := by
  have hx : |(-83917349496 / 10 ^ 11 : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> norm_num
  have h := Real.exp_bound hx (n := 16) (by norm_num)
  have habs : |(-83917349496 / 10 ^ 11 : ℝ)| = 83917349496 / 10 ^ 11 := by
    rw [abs_of_neg (by norm_num)]
    norm_num
  rw [habs] at h
  have hlo := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo
  have he : Real.exp (-167834698992 / 10 ^ 11) = Real.exp (-83917349496 / 10 ^ 11) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  nlinarith

theorem log_lower_certificate :
    (-167834699012 / 10 ^ 11 : ℝ) < Real.log (18668230884 / 10 ^ 11) :=
  (Real.lt_log_iff_exp_lt (by norm_num)).mpr exp_lower_certificate

theorem log_upper_certificate :
    Real.log (18668230886 / 10 ^ 11) < (-167834698992 / 10 ^ 11 : ℝ) :=
  (Real.log_lt_iff_lt_exp (by norm_num)).mpr exp_upper_certificate

theorem uniform_demand_lower : 1 / 2 < demand uniformLaw 2 (18668230884 / 10 ^ 11) := by
  rw [uniform_demand (by norm_num) (by norm_num)]
  have h := mul_lt_mul_of_pos_left log_lower_certificate
    (show (0 : ℝ) < 18668230884 / 10 ^ 11 by norm_num)
  norm_num at h ⊢
  linarith

theorem uniform_demand_upper : demand uniformLaw 2 (18668230886 / 10 ^ 11) < 1 / 2 := by
  rw [uniform_demand (by norm_num) (by norm_num)]
  have h := mul_lt_mul_of_pos_left log_upper_certificate
    (show (0 : ℝ) < 18668230886 / 10 ^ 11 by norm_num)
  norm_num at h ⊢
  linarith

end Numerics

theorem uniform_root :
    18668230884 / 10 ^ 11 < capRoot uniformLaw 2 (1 / 2) ∧
    capRoot uniformLaw 2 (1 / 2) < 18668230886 / 10 ^ 11 ∧
    1 - capRoot uniformLaw 2 (1 / 2) +
      capRoot uniformLaw 2 (1 / 2) * Real.log (capRoot uniformLaw 2 (1 / 2)) = 1 / 2 ∧
    coverage uniformLaw 2 (capRoot uniformLaw 2 (1 / 2)) =
      (1 - capRoot uniformLaw 2 (1 / 2)) ^ 2 := by
  obtain ⟨hr, hd⟩ := capRoot_spec uniformLaw le_rfl (ρ := 1 / 2) (by norm_num)
    (by rw [uniformLaw_positive_mass]; norm_num)
  set T := capRoot uniformLaw 2 (1 / 2)
  have hlo : 18668230884 / 10 ^ 11 < T := by
    by_contra hle
    have := demand_antitone uniformLaw le_rfl hr.le (not_lt.mp hle)
    linarith [uniform_demand_lower]
  have hhi : T < 18668230886 / 10 ^ 11 := by
    by_contra hle
    have := demand_antitone uniformLaw le_rfl (by norm_num) (not_lt.mp hle)
    linarith [uniform_demand_upper]
  have hT1 : T ≤ 1 := by linarith
  refine ⟨hlo, hhi, ?_, uniform_coverage hr hT1⟩
  rw [← uniform_demand hr hT1]
  exact hd

theorem uniform_multiplicity_eq :
    multiplicity uniformLaw 2 1 = 1 / (1 - capRoot uniformLaw 2 (1 / 2)) ^ 2 := by
  unfold multiplicity
  have h2 : (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [h2, uniform_root.2.2.2]

theorem uniform_multiplicity_bounds :
    15117485536 / 10 ^ 10 < multiplicity uniformLaw 2 1 ∧
    multiplicity uniformLaw 2 1 < 15117485538 / 10 ^ 10 := by
  rw [uniform_multiplicity_eq]
  obtain ⟨hlo, hhi, _, _⟩ := uniform_root
  set T := capRoot uniformLaw 2 (1 / 2)
  have h1 : (0 : ℝ) < (1 - T) ^ 2 := by
    have : 0 < 1 - T := by linarith
    positivity
  constructor
  · have hlt : (1 - T) ^ 2 < (1 - 18668230884 / 10 ^ 11) ^ 2 := by nlinarith
    have := one_div_lt_one_div_of_lt h1 hlt
    have hnum : (15117485536 / 10 ^ 10 : ℝ) < 1 / (1 - 18668230884 / 10 ^ 11) ^ 2 := by
      norm_num
    linarith
  · have hlt : (1 - 18668230886 / 10 ^ 11) ^ 2 < (1 - T) ^ 2 := by nlinarith
    have := one_div_lt_one_div_of_lt (by norm_num) hlt
    have hnum : 1 / (1 - 18668230886 / 10 ^ 11) ^ 2 < (15117485538 / 10 ^ 10 : ℝ) := by
      norm_num
    linarith

theorem uniform_paper_digits :
    1866823088 / 10 ^ 10 < capRoot uniformLaw 2 (1 / 2) ∧
    capRoot uniformLaw 2 (1 / 2) < 1866823089 / 10 ^ 10 ∧
    15117485536 / 10 ^ 10 < multiplicity uniformLaw 2 1 ∧
    multiplicity uniformLaw 2 1 < 15117485538 / 10 ^ 10 ∧
    (4 : ℝ) / 3 < multiplicity uniformLaw 2 1 := by
  obtain ⟨hlo, hhi, _, _⟩ := uniform_root
  obtain ⟨hm1, hm2⟩ := uniform_multiplicity_bounds
  refine ⟨by linarith, by linarith, hm1, hm2, by linarith⟩

theorem uniform_jensen_gap :
    1 / success 2 (1 / (2 : ℕ)) = (4 : ℝ) / 3 ∧
    1 / success 2 (1 / (2 : ℕ)) < multiplicity uniformLaw 2 1 := by
  have hval : 1 / success 2 (1 / (2 : ℕ)) = (4 : ℝ) / 3 := by
    unfold success
    norm_num
  refine ⟨hval, ?_⟩
  exact (strict_boundary_gap uniformLaw le_rfl
    (by rw [uniformLaw_positive_mass]; norm_num)).2

end Limit
end PayOnce
end FCAppendix
