import FCAppendix.PayOnce.LimitFormulas

namespace FCAppendix
namespace PayOnce
namespace Limit

open MeasureTheory Set Filter

noncomputable def tailProfile (q t w : ℝ) : ℝ := if t < w then 1 - (t / w) ^ q else 0

section Profile

variable {q t : ℝ}

theorem tailProfile_nonneg (ht : 0 ≤ t) (hq : 0 < q) (w : ℝ) : 0 ≤ tailProfile q t w := by
  unfold tailProfile
  split_ifs with h
  · have hw : 0 < w := lt_of_le_of_lt ht h
    have : (t / w) ^ q ≤ 1 :=
      Real.rpow_le_one (div_nonneg ht hw.le) ((div_le_one hw).mpr h.le) hq.le
    linarith
  · exact le_rfl

theorem tailProfile_le_one (ht : 0 ≤ t) (w : ℝ) : tailProfile q t w ≤ 1 := by
  unfold tailProfile
  split_ifs with h
  · have := Real.rpow_nonneg (div_nonneg ht (lt_of_le_of_lt ht h).le) q
    linarith
  · exact zero_le_one

theorem measurable_tailProfile (q t : ℝ) : Measurable (tailProfile q t) := by
  unfold tailProfile
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

theorem tailProfile_level (ht : 0 < t) (hq : 0 < q) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    {w | s < tailProfile q t w} = Ioi (t / (1 - s) ^ q⁻¹) := by
  have hc : 0 < (1 - s) ^ q⁻¹ := Real.rpow_pos_of_pos (by linarith) _
  have hc1 : (1 - s) ^ q⁻¹ ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) (inv_nonneg.mpr hq.le)
  ext w
  simp only [mem_setOf_eq, mem_Ioi]
  unfold tailProfile
  constructor
  · intro h
    split_ifs at h with htw
    · have hw : 0 < w := lt_trans ht htw
      have h1 : (t / w) ^ q < 1 - s := by linarith
      have h2 : t / w < (1 - s) ^ q⁻¹ := by
        have := Real.rpow_lt_rpow (Real.rpow_nonneg (div_nonneg ht.le hw.le) q) h1
          (inv_pos.mpr hq)
        rwa [Real.rpow_rpow_inv (div_nonneg ht.le hw.le) hq.ne'] at this
      rw [div_lt_iff₀ hc]
      rw [div_lt_iff₀ hw] at h2
      linarith
    · linarith
  · intro h
    have htw : t < w := lt_of_le_of_lt (le_div_self ht.le hc hc1) h
    rw [if_pos htw]
    have hw : 0 < w := lt_trans ht htw
    have h2 : t / w < (1 - s) ^ q⁻¹ := by
      rw [div_lt_iff₀ hc] at h
      rw [div_lt_iff₀ hw]
      linarith
    have := Real.rpow_lt_rpow (div_nonneg ht.le hw.le) h2 hq
    rw [Real.rpow_inv_rpow (by linarith) hq.ne'] at this
    linarith

theorem tailProfile_level_empty (ht : 0 ≤ t) {s : ℝ} (hs : 1 ≤ s) :
    {w | s < tailProfile q t w} = ∅ := by
  ext w
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
  exact le_trans (tailProfile_le_one ht w) hs

theorem integral_tailProfile (μW : Measure ℝ) [IsProbabilityMeasure μW] {w₀ α : ℝ}
    (hw0 : 0 < w₀) (hα : 0 < α) (hP : ∀ w, w₀ ≤ w → μW.real (Ioi w) = (w₀ / w) ^ α)
    (hq : 0 < q) (ht : w₀ ≤ t) :
    ∫ w, tailProfile q t w ∂μW = (w₀ / t) ^ α / (α / q + 1) := by
  have ht0 : 0 < t := lt_of_lt_of_le hw0 ht
  have hint : Integrable (tailProfile q t) μW :=
    UnitInterval.integrable μW _ (measurable_tailProfile q t)
      (tailProfile_nonneg ht0.le hq) (tailProfile_le_one ht0.le)
  rw [hint.integral_eq_integral_meas_lt (Eventually.of_forall (tailProfile_nonneg ht0.le hq))]
  have hlevel : ∀ s ∈ Ioo (0 : ℝ) 1, μW.real {w | s < tailProfile q t w} =
      (w₀ / t) ^ α * (1 - s) ^ (α / q) := by
    intro s hs
    rw [tailProfile_level ht0 hq hs.1 hs.2]
    have hc : 0 < (1 - s) ^ q⁻¹ := Real.rpow_pos_of_pos (by linarith [hs.2]) _
    have hc1 : (1 - s) ^ q⁻¹ ≤ 1 :=
      Real.rpow_le_one (by linarith [hs.2]) (by linarith [hs.1]) (inv_nonneg.mpr hq.le)
    rw [hP _ (le_trans ht (le_div_self ht0.le hc hc1)), div_div_eq_mul_div, mul_div_right_comm,
      Real.mul_rpow (div_nonneg hw0.le ht0.le) hc.le, ← Real.rpow_mul (by linarith [hs.2]),
      inv_mul_eq_div]
  have hr : 0 < α / q := div_pos hα hq
  calc ∫ s in Ioi 0, μW.real {w | s < tailProfile q t w}
      = ∫ s in Ioc 0 1, μW.real {w | s < tailProfile q t w} := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          Ioc_subset_Ioi_self
        intro s hs
        have hs1 : 1 < s := by
          simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hs
          exact hs.2 hs.1
        rw [tailProfile_level_empty ht0.le hs1.le, measureReal_empty]
    _ = ∫ s in Ioo 0 1, μW.real {w | s < tailProfile q t w} := integral_Ioc_eq_integral_Ioo
    _ = ∫ s in Ioo 0 1, (w₀ / t) ^ α * (1 - s) ^ (α / q) :=
        setIntegral_congr_fun measurableSet_Ioo hlevel
    _ = ∫ s in Ioc 0 1, (w₀ / t) ^ α * (1 - s) ^ (α / q) := integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ s in (0 : ℝ)..1, (w₀ / t) ^ α * (1 - s) ^ (α / q) :=
        (intervalIntegral.integral_of_le zero_le_one).symm
    _ = (w₀ / t) ^ α * ∫ s in (0 : ℝ)..1, (1 - s) ^ (α / q) :=
        intervalIntegral.integral_const_mul _ _
    _ = (w₀ / t) ^ α * ∫ x in (0 : ℝ)..1, x ^ (α / q) := by
        rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (α / q)) 1]
        norm_num
    _ = _ := by
        rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow,
          Real.zero_rpow (by linarith)]
        ring

end Profile

section Pareto

variable (μW : Measure ℝ) [IsProbabilityMeasure μW] {n : ℕ} {w₀ α : ℝ}

def ParetoTail (μW : Measure ℝ) (w₀ α : ℝ) : Prop :=
  ∀ w, w₀ ≤ w → μW.real (Ioi w) = (w₀ / w) ^ α

theorem pStar_eq_tailProfile (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) :
    pStar n t w = tailProfile (1 / ((n : ℝ) - 1)) t w := by
  unfold tailProfile
  split_ifs with h
  · exact pStar_of_lt hn ht h
  · exact pStar_eq_zero_of_le hn ht (not_lt.mp h)

theorem success_pStar_eq_tailProfile (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) :
    success n (pStar n t w) = tailProfile ((n : ℝ) / ((n : ℝ) - 1)) t w := by
  unfold tailProfile
  split_ifs with h
  · exact success_pStar hn ht h
  · exact success_pStar_of_le hn ht (not_lt.mp h)

theorem pareto_demand (hn : 2 ≤ n) (hw0 : 0 < w₀) (hα : 0 < α) (hP : ParetoTail μW w₀ α)
    {t : ℝ} (ht : w₀ ≤ t) :
    demand μW n t = μW.real (Ioi t) / (1 + α * ((n : ℝ) - 1)) := by
  have ht0 : 0 < t := lt_of_lt_of_le hw0 ht
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold demand
  simp_rw [pStar_eq_tailProfile hn ht0.le]
  rw [integral_tailProfile μW hw0 hα hP (exponent_pos hn) ht, hP t ht]
  congr 1
  field_simp
  ring

theorem pareto_coverage (hn : 2 ≤ n) (hw0 : 0 < w₀) (hα : 0 < α) (hP : ParetoTail μW w₀ α)
    {t : ℝ} (ht : w₀ ≤ t) :
    coverage μW n t = n * μW.real (Ioi t) / (n + α * ((n : ℝ) - 1)) := by
  have ht0 : 0 < t := lt_of_lt_of_le hw0 ht
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hq : (0 : ℝ) < (n : ℝ) / ((n : ℝ) - 1) := div_pos (by linarith) hn1
  unfold coverage
  simp_rw [success_pStar_eq_tailProfile hn ht0.le]
  rw [integral_tailProfile μW hw0 hα hP hq ht, hP t ht]
  have hden : (0 : ℝ) < n + α * ((n : ℝ) - 1) := by positivity
  field_simp
  ring

theorem pareto_capacity_root (hn : 2 ≤ n) (hw0 : 0 < w₀) (hα : 0 < α)
    (hP : ParetoTail μW w₀ α) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < n / (1 + α * ((n : ℝ) - 1))) :
    w₀ < w₀ * (n / ((1 + α * ((n : ℝ) - 1)) * β)) ^ (1 / α) ∧
    μW.real (Ioi (w₀ * (n / ((1 + α * ((n : ℝ) - 1)) * β)) ^ (1 / α))) =
      (1 + α * ((n : ℝ) - 1)) * β / n ∧
    demand μW n (w₀ * (n / ((1 + α * ((n : ℝ) - 1)) * β)) ^ (1 / α)) = β / n ∧
    capRoot μW n (β / n) = w₀ * (n / ((1 + α * ((n : ℝ) - 1)) * β)) ^ (1 / α) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : 0 < 1 + α * ((n : ℝ) - 1) := by nlinarith
  set A := 1 + α * ((n : ℝ) - 1) with hA_def
  have hX : 1 < (n : ℝ) / (A * β) := by
    rw [one_lt_div (mul_pos hA hβ0)]
    rw [lt_div_iff₀ hA] at hβ
    linarith
  have hY : 1 < ((n : ℝ) / (A * β)) ^ (1 / α) := Real.one_lt_rpow hX (by positivity)
  have ht0 : w₀ < w₀ * ((n : ℝ) / (A * β)) ^ (1 / α) := by nlinarith
  have htail : μW.real (Ioi (w₀ * ((n : ℝ) / (A * β)) ^ (1 / α))) = A * β / n := by
    rw [hP _ ht0.le]
    have hYpos : 0 < ((n : ℝ) / (A * β)) ^ (1 / α) := by linarith
    have hsimp : w₀ / (w₀ * ((n : ℝ) / (A * β)) ^ (1 / α)) =
        (((n : ℝ) / (A * β)) ^ (1 / α))⁻¹ := by
      field_simp
    rw [hsimp, Real.inv_rpow hYpos.le, one_div, Real.rpow_inv_rpow (by linarith) hα.ne']
    rw [inv_div]
  have hd : demand μW n (w₀ * ((n : ℝ) / (A * β)) ^ (1 / α)) = β / n := by
    rw [pareto_demand μW hn hw0 hα hP ht0.le, htail, ← hA_def]
    field_simp
  refine ⟨ht0, htail, hd, ?_⟩
  exact capRoot_eq μW hn (div_pos hβ0 (by linarith)) (lt_trans hw0 ht0) hd

theorem pareto_multiplicity (hn : 2 ≤ n) (hw0 : 0 < w₀) (hα : 0 < α)
    (hP : ParetoTail μW w₀ α) {β : ℝ} (hβ0 : 0 < β)
    (hβ : β < n / (1 + α * ((n : ℝ) - 1))) :
    multiplicity μW n β = 1 + 1 / (α + 1 / ((n : ℝ) - 1)) := by
  obtain ⟨ht0, htail, _, hroot⟩ := pareto_capacity_root μW hn hw0 hα hP hβ0 hβ
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  unfold multiplicity
  rw [hroot, pareto_coverage μW hn hw0 hα hP ht0.le, htail]
  have hA : 0 < 1 + α * ((n : ℝ) - 1) := by positivity
  have hden : (0 : ℝ) < n + α * ((n : ℝ) - 1) := by positivity
  field_simp
  ring

end Pareto

section ParetoWitness

variable {n : ℕ} {w₀ α : ℝ}

theorem paretoMeasure_tail (hw0 : 0 < w₀) (hα : 0 < α) :
    ParetoTail (ProbabilityTheory.paretoMeasure w₀ α) w₀ α := by
  intro w hw
  have hw' : 0 < w := lt_of_lt_of_le hw0 hw
  rw [measureReal_def, ProbabilityTheory.paretoMeasure, withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ x in Ioi w, ENNReal.ofReal (ProbabilityTheory.paretoPDFReal w₀ α x)).toReal = _
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => ProbabilityTheory.paretoPDFReal_nonneg hw0.le hα.le x)
    (ProbabilityTheory.measurable_paretoPDFReal w₀ α).aestronglyMeasurable]
  have hcongr : EqOn (ProbabilityTheory.paretoPDFReal w₀ α)
      (fun x => α * w₀ ^ α * x ^ (-(α + 1))) (Ioi w) := by
    intro x hx
    have hx' : w₀ ≤ x := le_trans hw (le_of_lt hx)
    simp only [ProbabilityTheory.paretoPDFReal, if_pos hx']
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hw']
  have he : -(α + 1) + 1 = -α := by ring
  rw [he, Real.div_rpow hw0.le hw'.le, Real.rpow_neg hw'.le]
  have hpos : 0 < w ^ α := Real.rpow_pos_of_pos hw' α
  field_simp

theorem paretoMeasure_multiplicity (hn : 2 ≤ n) (hw0 : 0 < w₀) (hα : 0 < α) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β < n / (1 + α * ((n : ℝ) - 1))) :
    multiplicity (ProbabilityTheory.paretoMeasure w₀ α) n β =
      1 + 1 / (α + 1 / ((n : ℝ) - 1)) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_paretoMeasure hw0 hα
  exact pareto_multiplicity _ hn hw0 hα (paretoMeasure_tail hw0 hα) hβ0 hβ

end ParetoWitness

end Limit
end PayOnce
end FCAppendix
