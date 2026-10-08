import FCAppendix.PayOnce.InactiveDerivativeApproximation

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Set TruncatedFOC

theorem weightedSlope_entry_error_le {n : ℕ} (hn : 2 ≤ n) {p w K : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) (hK : 0 ≤ K)
    (hlip : |phi n p-phi n 0| ≤ K*p) :
    |weightedSlope n p w-(if 0<p then phi n 0 else 0)| ≤ (n:ℝ)^2*w+K*p := by
  by_cases hp0 : 0 < p
  · have hbase : baseSlope n p=phi n p := by
      by_cases hp1 : p<1
      · simp [baseSlope,weightedSlope,hp0,hp1]
      · have he : p=1 := le_antisymm hp.2 (le_of_not_gt hp1)
        simp [he,baseSlope,weightedSlope,ResponseFactor.phi_one hn]
    have hc := AnalyticalKernel.slope_correction_bounds hn hp hw
    have hco : |weightedSlope n p w-phi n p| ≤ (n:ℝ)^2*w := by
      rw [← hbase,abs_sub_comm,abs_of_nonneg hc.1]
      exact hc.2
    rw [if_pos hp0]
    exact (abs_sub_le _ _ _).trans (add_le_add hco hlip)
  · simp only [weightedSlope,hp0,false_and,if_false,sub_zero,abs_zero]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hw.1) (mul_nonneg hK hp.1)

theorem integral_weightedSlope_entry_error_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n) {p w : Ω → ℝ} (hp : Measurable p) (hw : Measurable w)
    (hpb : ∀ x, p x ∈ Icc (0:ℝ) 1) (hwb : ∀ x, w x ∈ Icc (0:ℝ) 1)
    {K : ℝ} (hK : 0 ≤ K) (hlip : ∀ x, |phi n (p x)-phi n 0| ≤ K*p x) :
    |(∫ x, weightedSlope n (p x) (w x) ∂μ)-phi n 0*μ.real {x | 0<p x}| ≤
      (n:ℝ)^2*(∫ x, w x ∂μ)+K*(∫ x, p x ∂μ) := by
  have hi := integrable_weightedSlope μ hn hp hw hpb (fun x _ => hwb x)
  have hwi := UnitInterval.integrable μ w hw (fun x => (hwb x).1) (fun x => (hwb x).2)
  have hpi := UnitInterval.integrable μ p hp (fun x => (hpb x).1) (fun x => (hpb x).2)
  let E := {x | 0<p x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hp
  have hEi : Integrable (E.indicator (fun _ => phi n 0)) μ := (integrable_const _).indicator hE
  have hid : (∫ x, E.indicator (fun _ => phi n 0) x ∂μ)=phi n 0*μ.real E := by
    rw [integral_indicator_const _ hE]
    simp only [smul_eq_mul,mul_comm]
  rw [← hid,← integral_sub hi hEi]
  have hbound (x : Ω) : |weightedSlope n (p x) (w x)-E.indicator (fun _ => phi n 0) x| ≤
      (n:ℝ)^2*w x+K*p x := by
    simpa only [E,indicator,mem_setOf_eq] using weightedSlope_entry_error_le hn (hpb x) (hwb x) hK (hlip x)
  have hj : Integrable (fun x => (n:ℝ)^2*w x+K*p x) μ :=
    (hwi.const_mul _).add (hpi.const_mul _)
  have hh := (abs_integral_le_integral_abs (f := fun x =>
    weightedSlope n (p x) (w x)-E.indicator (fun _ => phi n 0) x)).trans
      (integral_mono (hi.sub hEi).abs hj hbound)
  simpa only [integral_add (hwi.const_mul _) (hpi.const_mul _),integral_const_mul] using hh

end FCAppendix.PayOnce.RareSuccessSlope
