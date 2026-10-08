import FCAppendix.Probability.BoundedTiltVariance
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Filter Topology Set Real
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ}

theorem mean_sub_tilted_mean_bounds (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u a : ℝ} (hu : u ∈ Icc (-a) 0) :
    exp (-2*a)*variance X μ*|u| ≤
        (∫ ω, X ω ∂μ)-(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) ∧
      (∫ ω, X ω ∂μ)-(∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) ≤
        exp (2*a)*variance X μ*|u| := by
  by_cases hu0 : u = 0
  · subst u
    simp only [zero_mul,abs_zero,mul_zero,tilted_const,sub_self,le_refl,and_self]
  have hu' : u < 0 := lt_of_le_of_ne hu.2 hu0
  let f : ℝ → ℝ := fun v => ∫ ω, X ω ∂μ.tilted (fun ω => v*X ω)
  have hzero : f 0 = ∫ ω, X ω ∂μ := by simp [f]
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_tilted_mean μ hX hbound v).continuousAt)
  obtain ⟨v,hv,hvv⟩ := exists_hasDerivAt_eq_slope f
    (fun v => variance X (μ.tilted (fun ω => v*X ω))) hu' hc.continuousOn
    (fun v _ => hasDerivAt_tilted_mean μ hX hbound v)
  have hva : |v| ≤ a := abs_le.mpr ⟨by linarith [hu.1,hv.1],by linarith [hu.1,hu.2,hv.2]⟩
  have hh := tilted_variance_bounds μ hX hbound hva
  rw [hvv,hzero,zero_sub] at hh
  exact ⟨by simpa only [abs_of_neg hu'] using (le_div_iff₀ (neg_pos.mpr hu')).mp hh.1,
    by simpa only [abs_of_neg hu'] using (div_le_iff₀ (neg_pos.mpr hu')).mp hh.2⟩

theorem exists_negative_tilt_of_mean_gap (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {a r : ℝ}
    (ha : 0 < a) (hvar : 0 < variance X μ)
    (hr : 0 < (∫ ω, X ω ∂μ)-r)
    (hgap : (∫ ω, X ω ∂μ)-r < a*exp (-2*a)*variance X μ) :
    ∃ u : ℝ, u ∈ Ioo (-a) 0 ∧
      (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r ∧
      ((∫ ω, X ω ∂μ)-r)/(exp (2*a)*variance X μ) ≤ |u| ∧
      |u| ≤ ((∫ ω, X ω ∂μ)-r)/(exp (-2*a)*variance X μ) := by
  let f : ℝ → ℝ := fun v => ∫ ω, X ω ∂μ.tilted (fun ω => v*X ω)
  have hzero : f 0 = ∫ ω, X ω ∂μ := by simp [f]
  have hc : Continuous f := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_tilted_mean μ hX hbound v).continuousAt)
  have hleft := (mean_sub_tilted_mean_bounds μ hX hbound
    (u := -a) (a := a) ⟨le_rfl,by linarith⟩).1
  rw [abs_neg,abs_of_pos ha] at hleft
  have hends : r ∈ Ioo (f (-a)) (f 0) := by
    change f (-a) < r ∧ r < f 0
    rw [hzero]
    constructor
    · change (∫ ω, X ω ∂μ.tilted (fun ω => -a*X ω)) < r
      nlinarith [hleft]
    · linarith
  obtain ⟨u,hu,hm⟩ := intermediate_value_Ioo (show -a ≤ (0:ℝ) by linarith) hc.continuousOn hends
  have hb := mean_sub_tilted_mean_bounds μ hX hbound (Ioo_subset_Icc_self hu)
  change (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r at hm
  rw [hm] at hb
  refine ⟨u,hu,hm,?_,?_⟩
  · apply (div_le_iff₀ (mul_pos (exp_pos _) hvar)).mpr
    nlinarith [hb.2]
  · apply (le_div_iff₀ (mul_pos (exp_pos _) hvar)).mpr
    nlinarith [hb.1]

theorem monotone_tilted_mean (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) :
    Monotone (fun u => ∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) := by
  apply monotone_of_deriv_nonneg
    (fun u => (hasDerivAt_tilted_mean μ hX hbound u).differentiableAt)
  intro u
  rw [(hasDerivAt_tilted_mean μ hX hbound u).deriv]
  exact variance_nonneg _ _

theorem cgf_sub_linear_min_of_tilted_mean (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u r : ℝ}
    (hmean : (∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) = r) (v : ℝ) :
    cgf X μ u-u*r ≤ cgf X μ v-v*r := by
  have hi (w : ℝ) : w ∈ interior (integrableExpSet X μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ hX.aemeasurable hbound,interior_univ]
    trivial
  have hm := monotone_tilted_mean μ hX hbound
  have hd : Differentiable ℝ (cgf X μ) := fun w => (analyticAt_cgf (hi w)).differentiableAt
  rcases lt_trichotomy u v with huv | rfl | hvu
  · obtain ⟨w,hw,he⟩ := exists_deriv_eq_slope (cgf X μ) huv hd.continuous.continuousOn hd.differentiableOn
    have hh := hm hw.1.le
    dsimp only at hh
    rw [hmean,integral_tilted_mul_self (hi w),he] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr huv)).mp hh
    nlinarith
  · exact le_rfl
  · obtain ⟨w,hw,he⟩ := exists_deriv_eq_slope (cgf X μ) hvu hd.continuous.continuousOn hd.differentiableOn
    have hh := hm hw.2.le
    dsimp only at hh
    rw [hmean,integral_tilted_mul_self (hi w),he] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hvu)).mp hh
    nlinarith

end FCAppendix.ExponentialTilt
