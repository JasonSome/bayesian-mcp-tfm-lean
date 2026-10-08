import FCAppendix.Probability.GaussianMeanConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem tendstoInDistribution_of_integral_abs_sub
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X Y : (t : ℕ) → Ω t → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ t, Measurable (X t))
    (hY : TendstoInDistribution Y atTop Z μ ν)
    (hi : ∀ t, Integrable (fun ω => |X t ω-Y t ω|) (μ t))
    (hclose : Tendsto (fun t => ∫ ω, |X t ω-Y t ω| ∂μ t) atTop (𝓝 0)) :
    TendstoInDistribution X atTop Z μ ν := by
  refine ⟨fun t => (hX t).aemeasurable,hY.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro f hfb ⟨L,hL⟩
  let bf : BoundedContinuousFunction ℝ ℝ := ⟨⟨f,hL.continuous⟩,hfb⟩
  have hxint t : Integrable (fun ω => f (X t ω)) (μ t) := by
    apply Integrable.of_bound ((hL.continuous.measurable.comp (hX t)).aestronglyMeasurable) ‖bf‖
    exact .of_forall fun ω => bf.norm_coe_le_norm (X t ω)
  have hyint t : Integrable (fun ω => f (Y t ω)) (μ t) := by
    apply Integrable.of_bound ((hL.continuous.measurable.comp_aemeasurable
      (hY.forall_aemeasurable t)).aestronglyMeasurable) ‖bf‖
    exact .of_forall fun ω => bf.norm_coe_le_norm (Y t ω)
  have hbound t : |(∫ ω, f (X t ω) ∂μ t)-(∫ ω, f (Y t ω) ∂μ t)| ≤
      (L:ℝ)*(∫ ω, |X t ω-Y t ω| ∂μ t) := by
    rw [← integral_sub (hxint t) (hyint t),← integral_const_mul]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono ((hxint t).sub (hyint t)).abs ((hi t).const_mul (L:ℝ))
    intro ω
    simpa only [Real.dist_eq,Pi.sub_apply] using hL.dist_le_mul (X t ω) (Y t ω)
  have he : Tendsto (fun t => (∫ ω, f (X t ω) ∂μ t)-(∫ ω, f (Y t ω) ∂μ t)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero (fun _ => abs_nonneg _) hbound (by simpa using hclose.const_mul (L:ℝ))
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hY.tendsto) bf
  change Tendsto (fun t => ∫ z, f z ∂(μ t).map (Y t)) atTop
    (𝓝 (∫ z, f z ∂ν.map Z)) at hw
  change Tendsto (fun t => ∫ z, f z ∂(μ t).map (X t)) atTop
    (𝓝 (∫ z, f z ∂ν.map Z))
  simp_rw [integral_map (hY.forall_aemeasurable _) hL.continuous.measurable.aestronglyMeasurable] at hw
  have hh := he.add hw
  simp only [sub_add_cancel,zero_add] at hh
  simpa only [integral_map (hX _).aemeasurable hL.continuous.measurable.aestronglyMeasurable] using hh

theorem tendstoInDistribution_positivePart_moving
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (μ t)]
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : (t : ℕ) → Ω t → ℝ) (Z : Ω' → ℝ)
    (hX : ∀ t, Measurable (X t)) (hweak : TendstoInDistribution X atTop Z μ ν)
    (y : ℕ → ℝ) {z : ℝ} (hy : Tendsto y atTop (𝓝 z)) (α : ℝ) :
    TendstoInDistribution (fun t ω => α*max (y t-X t ω) 0) atTop
      (fun ω => α*max (z-Z ω) 0) μ ν := by
  have hbound t ω : |α*max (y t-X t ω) 0-α*max (z-X t ω) 0| ≤ |α| *|y t-z| := by
    rw [← mul_sub,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg α)
    simpa only [sub_sub_sub_cancel_right] using abs_max_sub_max_le_abs (y t-X t ω) (z-X t ω) 0
  have hi t : Integrable (fun ω => |α*max (y t-X t ω) 0-α*max (z-X t ω) 0|) (μ t) := by
    apply Integrable.of_bound (by fun_prop) (|α| *|y t-z|)
    exact .of_forall fun ω => by simpa only [Real.norm_eq_abs,abs_abs] using hbound t ω
  apply tendstoInDistribution_of_integral_abs_sub μ ν _ _ _ (fun t => by fun_prop)
    (hweak.continuous_comp (g := fun q : ℝ => α*max (z-q) 0) (by fun_prop)) hi
  apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _) (g := fun t => |α| *|y t-z|)
  · intro t
    have hh := integral_mono (hi t) (integrable_const (|α| *|y t-z|)) (hbound t)
    simpa only [integral_const,probReal_univ,one_smul,Function.comp_def] using hh
  · simpa only [sub_self,abs_zero,mul_zero] using ((hy.sub_const z).abs).const_mul |α|

end FCAppendix.Probability
