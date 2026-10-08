import FCAppendix.PayOnce.FocalAllocationLimit
import FCAppendix.PayOnce.TruncatedFOC

namespace FCAppendix.PayOnce.RareSuccessSlope
open MeasureTheory Filter Topology Set OwnImpact

theorem continuousAt_phi {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    ContinuousAt (phi n) p := by
  apply ContinuousAt.div ?_ (continuous_Hslope n).continuousAt (Hslope_pos hn hp).ne'
  unfold H
  fun_prop

theorem phi_one {n : ℕ} (hn : 2 ≤ n) : phi n 1 = 0 := by
  simp [phi, show n-1 ≠ 0 by omega]

end FCAppendix.PayOnce.RareSuccessSlope

namespace FCAppendix.PayOnce.TruncatedFOC
open MeasureTheory Filter Topology Set OwnImpact RareSuccessSlope

theorem baseSlope_phi_error_le {n : ℕ} (hn : 2 ≤ n) {p q : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : 0 < q) :
    |baseSlope n p-phi n p| ≤ ((n:ℝ)^2/q)*|p-q| := by
  by_cases hp0 : p = 0
  · rw [hp0]
    have hbase : baseSlope n 0 = 0 := by simp [baseSlope, weightedSlope]
    rw [hbase, zero_sub, abs_neg, abs_of_nonneg (phi_nonneg hn ⟨le_rfl,zero_le_one⟩),
      zero_sub, abs_neg, abs_of_pos hq, div_mul_cancel₀ _ hq.ne']
    exact phi_le_sq hn ⟨le_rfl,zero_le_one⟩
  by_cases hp1 : p = 1
  · rw [hp1, phi_one hn]
    have hbase : baseSlope n 1 = 0 := by simp [baseSlope, weightedSlope]
    rw [hbase,sub_self,abs_zero]
    positivity
  · have hpi : 0 < p ∧ p < 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
    simp only [baseSlope,weightedSlope,if_pos hpi,sub_zero,mul_one,sub_self,abs_zero]
    positivity

theorem mean_abs_baseSlope_tendsto_zero
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    {n : ℕ} (hn : 2 ≤ n) (p : ∀ t, Ω t → ℝ)
    (hp : ∀ t, Measurable (p t)) (hpb : ∀ t ω, p t ω ∈ Icc (0:ℝ) 1)
    {q : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hgap : Tendsto (fun t => ∫ ω, |p t ω-q| ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, |baseSlope n (p t ω)-phi n q| ∂P t) atTop (𝓝 0) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1.le,hq.2⟩
  have hφbound : ∀ u ∈ Icc (0:ℝ) 1, |phi n u| ≤ (n:ℝ)^2 := fun u hu => by
    rw [abs_of_nonneg (phi_nonneg hn hu)]
    exact phi_le_sq hn hu
  have hφ := mean_abs_comp_tendsto_zero P p hp hpb (measurable_phi n) hq'
    (continuousAt_phi hn hq') hφbound hgap
  have hI t : Integrable (fun ω => |baseSlope n (p t ω)-phi n q|) (P t) := by
    apply Integrable.of_bound ((measurable_baseSlope n |>.comp (hp t)).sub measurable_const).abs.aestronglyMeasurable
      (2*(n:ℝ)^2)
    filter_upwards [] with ω
    change ‖|baseSlope n (p t ω)-phi n q|‖ ≤ 2*(n:ℝ)^2
    rw [Real.norm_eq_abs,abs_abs]
    have hb := baseSlope_bounds hn (hpb t ω)
    have hh := abs_sub (baseSlope n (p t ω)) (phi n q)
    rw [abs_of_nonneg hb.1] at hh
    linarith [hφbound q hq',hb.2]
  have hJ t : Integrable (fun ω => |phi n (p t ω)-phi n q|) (P t) := by
    apply Integrable.of_bound ((measurable_phi n |>.comp (hp t)).sub measurable_const).abs.aestronglyMeasurable
      (2*(n:ℝ)^2)
    filter_upwards [] with ω
    change ‖|phi n (p t ω)-phi n q|‖ ≤ 2*(n:ℝ)^2
    rw [Real.norm_eq_abs,abs_abs]
    have hh := abs_sub (phi n (p t ω)) (phi n q)
    linarith [hφbound _ (hpb t ω),hφbound q hq']
  have hlim : Tendsto (fun t => ((n:ℝ)^2/q)*(∫ ω, |p t ω-q| ∂P t)+
      (∫ ω, |phi n (p t ω)-phi n q| ∂P t)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hgap.const_mul ((n:ℝ)^2/q)).add hφ
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) _ hlim
  intro t
  have hgapI := CovarianceConcentration.integrable_abs_gap (P t) (hp t) measurable_const (hpb t) (fun _ => hq')
  have hh := integral_mono (hI t) ((hgapI.const_mul ((n:ℝ)^2/q)).add (hJ t)) (fun ω =>
    (abs_sub_le (baseSlope n (p t ω)) (phi n (p t ω)) (phi n q)).trans
      (add_le_add (baseSlope_phi_error_le hn (hpb t ω) hq.1) le_rfl))
  simpa only [Pi.add_apply, integral_add (hgapI.const_mul ((n:ℝ)^2/q)) (hJ t),integral_const_mul] using hh

end FCAppendix.PayOnce.TruncatedFOC
