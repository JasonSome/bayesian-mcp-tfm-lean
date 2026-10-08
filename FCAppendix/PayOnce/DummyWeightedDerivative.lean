import FCAppendix.PayOnce.DummyCoverageDerivative
import FCAppendix.PayOnce.WeightedDerivative

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList OwnImpact RareSuccessSlope
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem exists_measurable_weight_coverage_derivative {n c : ℕ} (hn : 2 ≤ n)
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) (hreg : ∀ᵐ rivals ∂μ, RegularClearing n c rivals b) :
    ∃ weight : (ι → ℝ) → ℝ, Measurable weight ∧
      (∀ rivals, weight rivals ∈ Icc (0 : ℝ) 1) ∧
      (∀ rivals, 1 / ((n : ℝ)^3+1) ≤ 1-weight rivals) ∧
      (∀ᵐ rivals ∂μ,
        b * deriv (fun x => success n (allocation n c hn rivals x)) b =
          weightedSlope n (allocation n c hn rivals b) (weight rivals)) ∧
      HasDerivAt (coverage n c hn μ)
        ((∫ rivals, weightedSlope n (allocation n c hn rivals b) (weight rivals) ∂μ) / b) b := by
  let p := fun rivals : ι → ℝ => allocation n c hn rivals b
  let d := fun rivals : ι → ℝ => deriv (fun x => success n (allocation n c hn rivals x)) b
  have hd := aestronglyMeasurable_success_deriv hn μ hb hreg
  let dm := hd.mk d
  let κ : ℝ := 1 / ((n : ℝ)^3+1)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp only [κ]
    apply (div_le_one (by positivity : 0 < (n : ℝ)^3+1)).mpr
    linarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3]
  let weight := fun rivals : ι → ℝ => max 0 (min (1-κ) (1-b*dm rivals/phi n (p rivals)))
  have hw : Measurable weight := by
    exact measurable_const.max (measurable_const.min
      (measurable_const.sub ((hd.measurable_mk.const_mul b).div
        ((measurable_phi n).comp (measurable_allocation_fixed_bid hn b)))))
  have hw0 (rivals : ι → ℝ) : 0 ≤ weight rivals := le_max_left _ _
  have hwcap (rivals : ι → ℝ) : weight rivals ≤ 1-κ :=
    max_le (sub_nonneg.mpr hκ1) (min_le_left _ _)
  have hw1 (rivals : ι → ℝ) : weight rivals ≤ 1 := (hwcap rivals).trans (by linarith)
  have he : ∀ᵐ rivals ∂μ, b*d rivals = weightedSlope n (p rivals) (weight rivals) := by
    filter_upwards [hreg, hd.ae_eq_mk] with rivals hrr hdme
    obtain ⟨w, hwbound, hwgap, hderiv⟩ := AnalyticalKernel.exists_weight_success_derivative_of_regular
      hn (min_le_right c (Fintype.card (Active rivals)+1)) (fun j : Active rivals => rivals j.val) hb hrr
    change b*d rivals = weightedSlope n (p rivals) w at hderiv
    by_cases hi : 0 < p rivals ∧ p rivals < 1
    · have hφ := AnalyticalKernel.phi_pos_interior hn hi
      have hsolve : 1-b*dm rivals/phi n (p rivals) = w := by
        change d rivals = dm rivals at hdme
        rw [← hdme, hderiv, weightedSlope, if_pos hi]
        field_simp
        ring
      have hweight : weight rivals = w := by
        change max 0 (min (1-κ) (1-b*dm rivals/phi n (p rivals))) = w
        rw [hsolve, min_eq_right (by linarith [hwgap hi]), max_eq_right hwbound.1]
      rw [hweight]
      exact hderiv
    · simpa only [weightedSlope, if_neg hi] using hderiv
  refine ⟨weight, hw, fun rivals => ⟨hw0 rivals, hw1 rivals⟩,
    fun rivals => by linarith [hwcap rivals], he, ?_⟩
  have hderiv := hasDerivAt_coverage_of_regular hn μ hb hreg
  have hint : (∫ rivals, weightedSlope n (p rivals) (weight rivals) ∂μ) =
      b * ∫ rivals, d rivals ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [he] with rivals hr
    exact hr.symm
  change HasDerivAt _ ((∫ rivals, weightedSlope n (p rivals) (weight rivals) ∂μ) / b) b
  rw [hint, mul_div_cancel_left₀ _ hb.ne']
  exact hderiv.2

end FCAppendix.PayOnce.DummyKernel
