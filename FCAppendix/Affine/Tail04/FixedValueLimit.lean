import FCAppendix.Affine.Tail04.ConditionalVersions
import FCAppendix.Affine.Tail04.CountLaws
import FCAppendix.Affine.Tail04.MovingBoundary

noncomputable section
namespace FCAppendix.Affine.Tail04.FixedValues
open MeasureTheory ProbabilityTheory Set Filter Topology Classical

section CompactOptimizer
variable {A : Type*} [MetricSpace A] [CompactSpace A]

theorem compact_strict_maximum_gap (f : A→ℝ) (hf : Continuous f) (a₀ : A)
    (hstrict : ∀ a,a≠a₀→ f a< f a₀) (ε : ℝ) (hε : 0< ε) :
    ∃ γ : ℝ,0< γ ∧ ∀ a,f a₀≤ f a+γ → dist a a₀< ε := by
  let K : Set A := {a | ε≤ dist a a₀}
  have hK : IsCompact K :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨b,hb,hmax⟩ := hK.exists_isMaxOn hne hf.continuousOn
    have hba : b≠a₀ := by
      intro he
      subst b
      have hh : ε≤0 := by simpa only [dist_self] using (show ε≤ dist a₀ a₀ from hb)
      exact (not_le.mpr hε) hh
    have hgap : 0< f a₀-f b := sub_pos.mpr (hstrict b hba)
    refine ⟨(f a₀-f b)/2,by positivity,?_⟩
    intro a ha
    by_contra hn
    have haK : a∈K := le_of_not_gt hn
    have hfa : f a≤ f b := hmax haK
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro a _
    by_contra ha
    exact hne ⟨a,le_of_not_gt ha⟩

end CompactOptimizer

section ConditionalLaws
variable {A : Type*} [MetricSpace A] [CompactSpace A]
  [MeasurableSpace A] [BorelSpace A]
variable (μ : ℕ→ Measure A) [∀ k,IsProbabilityMeasure (μ k)]

omit [BorelSpace A] [∀ (k : ℕ), IsProbabilityMeasure (μ k)] in
theorem eventual_conditional_neighborhood (f : A→ℝ) (hf : Continuous f)
    (a₀ : A) (hstrict : ∀ a,a≠a₀→ f a< f a₀)
    (err : ℕ→ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hregret : ∀ᶠ k in atTop,∀ᵐ a∂μ k,f a₀≤ f a+err k)
    (ε : ℝ) (hε : 0< ε) :
    ∀ᶠ k in atTop,∀ᵐ a∂μ k,dist a a₀< ε := by
  obtain ⟨γ,hγ,hgood⟩ := compact_strict_maximum_gap f hf a₀ hstrict ε hε
  filter_upwards [hregret,herr.eventually_le_const hγ] with k hk he
  filter_upwards [hk] with a ha
  exact hgood a (by linarith)

include μ in
theorem conditional_continuous_test_tendsto (f : A→ℝ) (hf : Continuous f)
    (a₀ : A) (hstrict : ∀ a,a≠a₀→ f a< f a₀)
    (err : ℕ→ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hregret : ∀ᶠ k in atTop,∀ᵐ a∂μ k,f a₀≤ f a+err k)
    (g : C(A,ℝ)) :
    Tendsto (fun k => ∫ a,g a ∂μ k) atTop (𝓝 (g a₀)) := by
  have hgint (k : ℕ) : Integrable (fun a => g a) (μ k) :=
    Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall (fun a => g.norm_coe_le_norm a))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδg⟩ := Metric.continuousAt_iff.mp g.continuous.continuousAt
    (ε/2) (half_pos hε)
  filter_upwards [eventual_conditional_neighborhood μ f hf a₀ hstrict err herr
    hregret δ hδ] with k hk
  have hb : ∀ᵐ a∂μ k,‖g a-g a₀‖≤ ε/2 := by
    filter_upwards [hk] with a ha
    simpa only [Real.dist_eq,Real.norm_eq_abs] using (hδg ha).le
  have hh := norm_integral_le_of_norm_le_const (μ := μ k) hb
  rw [integral_sub (hgint k) (integrable_const (g a₀))] at hh
  simp only [probReal_univ,mul_one] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,mul_one,
    Real.norm_eq_abs,Real.dist_eq] using hh.trans_lt (half_lt_self hε)

theorem conditional_varying_test_tendsto (f : A→ℝ) (hf : Continuous f)
    (a₀ : A) (hstrict : ∀ a,a≠a₀→ f a< f a₀)
    (err : ℕ→ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hregret : ∀ᶠ k in atTop,∀ᵐ a∂μ k,f a₀≤ f a+err k)
    (g : C(A,ℝ)) (gk : ℕ→ A→ℝ)
    (hgk : ∀ k,Integrable (gk k) (μ k))
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (happrox : ∀ᶠ k in atTop,∀ᵐ a∂μ k,|gk k a-g a|≤ e k) :
    Tendsto (fun k => ∫ a,gk k a ∂μ k) atTop (𝓝 (g a₀)) := by
  have hgint (k : ℕ) : Integrable (fun a => g a) (μ k) :=
    Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall (fun a => g.norm_coe_le_norm a))
  have hdiff : Tendsto (fun k => (∫ a,gk k a ∂μ k)-(∫ a,g a ∂μ k))
      atTop (𝓝 0) := by
    have hnorm : Tendsto
        (fun k => |(∫ a,gk k a ∂μ k)-(∫ a,g a ∂μ k)|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun k => abs_nonneg _)) _ he
      filter_upwards [happrox] with k hk
      have hb : ∀ᵐ a∂μ k,‖gk k a-g a‖≤ e k := by
        simpa only [Real.norm_eq_abs] using hk
      have hh := norm_integral_le_of_norm_le_const (μ := μ k) hb
      rw [integral_sub (hgk k) (hgint k)] at hh
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
    simpa only [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm
  have hfixed := conditional_continuous_test_tendsto μ f hf a₀ hstrict err herr hregret g
  simpa only [sub_add_cancel,zero_add] using hdiff.add hfixed

end ConditionalLaws

theorem every_fixed_value_below_same_threshold (φ : ℕ→ℕ)
    (hφ : Tendsto φ atTop atTop) (v : ℝ) :
    ∀ᶠ k in atTop,v< movingThreshold (φ k) :=
  (movingThreshold_tendsto.comp hφ).eventually_gt_atTop v

end FCAppendix.Affine.Tail04.FixedValues
