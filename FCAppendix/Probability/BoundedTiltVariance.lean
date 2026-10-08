import FCAppendix.Probability.ExponentialTilt
import Mathlib.Analysis.Calculus.MeanValue

namespace FCAppendix.ExponentialTilt
open MeasureTheory ProbabilityTheory Filter Topology Set Real
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ}

theorem cgf_mem_Icc_of_unit_bounded (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u a : ℝ} (hu : |u| ≤ a) :
    cgf X μ u ∈ Icc (-a) a := by
  have ht := integrable_exp_mul_of_bounded μ hX.aemeasurable hbound u
  have hb : ∀ᵐ ω ∂μ, u*X ω ∈ Icc (-a) a := by
    filter_upwards [hbound] with ω hω
    have hh : |u*X ω| ≤ a := by
      rw [abs_mul,abs_of_nonneg hω.1]
      exact (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg u)).trans (by simpa using hu)
    exact abs_le.mp hh
  have hlo := integral_mono_ae (integrable_const (exp (-a))) ht
    (hb.mono (fun ω hω => exp_le_exp.mpr hω.1))
  have hhi := integral_mono_ae ht (integrable_const (exp a))
    (hb.mono (fun ω hω => exp_le_exp.mpr hω.2))
  simp only [integral_const,probReal_univ,one_smul] at hlo hhi
  change exp (-a) ≤ mgf X μ u at hlo
  change mgf X μ u ≤ exp a at hhi
  rw [← exp_cgf ht] at hlo hhi
  exact ⟨exp_le_exp.mp hlo,exp_le_exp.mp hhi⟩

theorem tilted_density_bounds (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u a : ℝ} (hu : |u| ≤ a) :
    ∀ᵐ ω ∂μ, exp (-2*a) ≤ exp (u*X ω-cgf X μ u) ∧
      exp (u*X ω-cgf X μ u) ≤ exp (2*a) := by
  have hc := cgf_mem_Icc_of_unit_bounded μ hX hbound hu
  filter_upwards [hbound] with ω hω
  have hh : |u*X ω| ≤ a := by
    rw [abs_mul,abs_of_nonneg hω.1]
    exact (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg u)).trans (by simpa using hu)
  have hb := abs_le.mp hh
  exact ⟨exp_le_exp.mpr (by linarith [hb.1,hc.2]),exp_le_exp.mpr (by linarith [hb.2,hc.1])⟩

theorem integral_tilted_bounds (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u a : ℝ} (hu : |u| ≤ a)
    {Y : Ω → ℝ} (hY : Integrable Y μ) (hYpos : 0 ≤ᵐ[μ] Y) :
    exp (-2*a)*(∫ ω, Y ω ∂μ) ≤ (∫ ω, Y ω ∂μ.tilted (fun ω => u*X ω)) ∧
      (∫ ω, Y ω ∂μ.tilted (fun ω => u*X ω)) ≤ exp (2*a)*(∫ ω, Y ω ∂μ) := by
  have hd := tilted_density_bounds μ hX hbound hu
  have hi : Integrable (fun ω => exp (u*X ω-cgf X μ u)*Y ω) μ := by
    apply Integrable.mono' (hY.const_mul (exp (2*a)))
      ((((hX.const_mul u).sub_const _).exp).aestronglyMeasurable.mul hY.aestronglyMeasurable)
    filter_upwards [hd,hYpos] with ω hdω hYω
    change ‖exp (u*X ω-cgf X μ u)*Y ω‖ ≤ exp (2*a)*Y ω
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _),abs_of_nonneg hYω]
    exact mul_le_mul_of_nonneg_right hdω.2 hYω
  have hlo := integral_mono_ae (hY.const_mul (exp (-2*a))) hi
    (by filter_upwards [hd,hYpos] with ω hdω hYω; exact mul_le_mul_of_nonneg_right hdω.1 hYω)
  have hhi := integral_mono_ae hi (hY.const_mul (exp (2*a)))
    (by filter_upwards [hd,hYpos] with ω hdω hYω; exact mul_le_mul_of_nonneg_right hdω.2 hYω)
  rw [integral_const_mul] at hlo hhi
  rw [integral_tilted_mul_eq_cgf _ (integrable_exp_mul_of_bounded μ hX.aemeasurable hbound u)]
  simpa only [smul_eq_mul] using And.intro hlo hhi

theorem tilted_variance_bounds (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) {u a : ℝ} (hu : |u| ≤ a) :
    exp (-2*a)*variance X μ ≤ variance X (μ.tilted (fun ω => u*X ω)) ∧
      variance X (μ.tilted (fun ω => u*X ω)) ≤ exp (2*a)*variance X μ := by
  let ν := μ.tilted (fun ω => u*X ω)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted
    (integrable_exp_mul_of_bounded μ hX.aemeasurable hbound u)
  have hXν : AEMeasurable X ν := hX.aemeasurable
  have hLp : MemLp X 2 μ := memLp_of_bounded hbound hX.aestronglyMeasurable 2
  have hsq (c : ℝ) : Integrable (fun ω => (X ω-c)^2) μ :=
    (hLp.sub (memLp_const c)).integrable_sq
  have hc (κ : Measure Ω) [IsProbabilityMeasure κ] (c : ℝ) :
      variance X κ ≤ ∫ ω, (X ω-c)^2 ∂κ := by
    have hh := variance_le_expectation_sq (X := fun ω => X ω-c) (μ := κ) (hX.sub_const c).aestronglyMeasurable
    simpa only [variance_sub_const hX.aestronglyMeasurable,Pi.pow_apply] using hh
  constructor
  · calc
      exp (-2*a)*variance X μ ≤ exp (-2*a)*(∫ ω, (X ω-(∫ z, X z ∂ν))^2 ∂μ) :=
        mul_le_mul_of_nonneg_left (hc μ _) (exp_pos _).le
      _ ≤ ∫ ω, (X ω-(∫ z, X z ∂ν))^2 ∂ν :=
        (integral_tilted_bounds μ hX hbound hu (hsq _) (Eventually.of_forall (fun _ => sq_nonneg _))).1
      _ = variance X ν := (variance_eq_integral hXν).symm
  · calc
      variance X ν ≤ ∫ ω, (X ω-(∫ z, X z ∂μ))^2 ∂ν := hc ν _
      _ ≤ exp (2*a)*(∫ ω, (X ω-(∫ z, X z ∂μ))^2 ∂μ) :=
        (integral_tilted_bounds μ hX hbound hu (hsq _) (Eventually.of_forall (fun _ => sq_nonneg _))).2
      _ = exp (2*a)*variance X μ := by rw [variance_eq_integral hX.aemeasurable]

theorem hasDerivAt_tilted_mean (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) (u : ℝ) :
    HasDerivAt (fun v => ∫ ω, X ω ∂μ.tilted (fun ω => v*X ω))
      (variance X (μ.tilted (fun ω => u*X ω))) u := by
  have hi (v : ℝ) : v ∈ interior (integrableExpSet X μ) := by
    rw [integrableExpSet_eq_univ_of_bounded μ hX.aemeasurable hbound,interior_univ]
    trivial
  have he : (fun v => ∫ ω, X ω ∂μ.tilted (fun ω => v*X ω)) = deriv (cgf X μ) :=
    funext (fun v => integral_tilted_mul_self (hi v))
  rw [he]
  have hv := variance_tilted_mul (hi u)
  rw [iteratedDeriv_succ,iteratedDeriv_one] at hv
  rw [hv]
  exact (analyticAt_cgf (hi u)).deriv.differentiableAt.hasDerivAt

end FCAppendix.ExponentialTilt
