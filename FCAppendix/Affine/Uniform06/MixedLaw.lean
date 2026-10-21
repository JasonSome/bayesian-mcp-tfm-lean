import FCAppendix.Affine.Uniform06.LowChernoffRows
import FCAppendix.Probability.BoundedTiltVariance
import Mathlib.Probability.Moments.Covariance

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedLaw

open MeasureTheory ProbabilityTheory Set
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.ExponentialTilt

abbrev Pair := ℝ × ℝ

def upperSignLaw : Measure Pair :=
  ENNReal.ofReal (1/2:ℝ) • Measure.dirac ((1/2:ℝ),1) +
    ENNReal.ofReal (1/2:ℝ) • Measure.dirac ((1/2:ℝ),-1)

instance upperSignLaw_probability : IsProbabilityMeasure upperSignLaw := by
  constructor
  simp only [upperSignLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

def lowerLift (μ : Measure ℝ) : Measure Pair := μ.map (fun x => (x,0))

instance lowerLift_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (lowerLift μ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

def law (i : Row) (μ : Measure ℝ) : Measure Pair :=
  ENNReal.ofReal (1-cutoff i) • upperSignLaw +
    ENNReal.ofReal (cutoff i) • lowerLift μ

instance law_probability (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law i μ) := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [cutoff_lt_one i]) (cutoff_pos i).le]
  norm_num

section Integrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem upper_integrable (f : Pair → E) : Integrable f upperSignLaw := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem integral_upper (f : Pair → E) :
    (∫ p, f p ∂upperSignLaw) =
      (1/2:ℝ) • f (1/2,1)+(1/2:ℝ) • f (1/2,-1) := by
  rw [upperSignLaw, integral_add_measure
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem lower_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {f : Pair → E} (hf : Continuous f) :
    Integrable f (lowerLift μ) := by
  have hc : Continuous (fun x : ℝ => f (x,0)) := hf.comp (by fun_prop)
  have hi := hc.integrableOn_Icc (μ := μ) (a := (0:ℝ)) (b := 1)
  change Integrable (fun x : ℝ => f (x,0)) (μ.restrict (Icc 0 1)) at hi
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hi
  exact (integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable
    (by fun_prop)).mpr hi

omit [CompleteSpace E] in
theorem integral_lower (μ : Measure ℝ) {f : Pair → E} (hf : Continuous f) :
    (∫ p, f p ∂lowerLift μ) = ∫ x, f (x,0) ∂μ := by
  rw [lowerLift, integral_map (by fun_prop) hf.stronglyMeasurable.aestronglyMeasurable]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem integrable_law (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {f : Pair → E} (hf : Continuous f) :
    Integrable f (law i μ) :=
  ((upper_integrable f).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((lower_integrable μ hμ hf).smul_measure ENNReal.ofReal_ne_top)

theorem integral_law (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {f : Pair → E} (hf : Continuous f) :
    (∫ p, f p ∂law i μ) =
      (1-cutoff i) • ((1/2:ℝ) • f (1/2,1)+(1/2:ℝ) • f (1/2,-1))+
        cutoff i • (∫ x, f (x,0) ∂μ) := by
  rw [law, integral_add_measure
    ((upper_integrable f).smul_measure ENNReal.ofReal_ne_top)
    ((lower_integrable μ hμ hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith [cutoff_lt_one i]),
    ENNReal.toReal_ofReal (cutoff_pos i).le, integral_upper, integral_lower μ hf]

end Integrals

theorem law_support (i : Row) (μ : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    ∀ᵐ p ∂law i μ, p.1 ∈ Icc (0:ℝ) 1 ∧
      (p.2 = -1 ∨ p.2 = 0 ∨ p.2 = 1) := by
  rw [law, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [upperSignLaw, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      apply (ae_dirac_iff (by measurability)).mpr <;> norm_num
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    filter_upwards [hμ] with x hx
    exact ⟨hx, Or.inr (Or.inl rfl)⟩

theorem demand_bounds (i : Row) (μ : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    ∀ᵐ p ∂law i μ, p.1 ∈ Icc (0:ℝ) 1 :=
  (law_support i μ hμ).mono fun _ hp => hp.1

theorem sign_bounds (i : Row) (μ : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    ∀ᵐ p ∂law i μ, p.2 ∈ Icc (-1:ℝ) 1 := by
  filter_upwards [law_support i μ hμ] with p hp
  rcases hp.2 with h | h | h <;> rw [h] <;> norm_num

theorem sign_mean (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    (∫ p, p.2 ∂law i μ) = 0 := by
  rw [integral_law i μ hμ continuous_snd]
  norm_num

theorem demand_sign_moment (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    (∫ p, p.1*p.2 ∂law i μ) = 0 := by
  rw [integral_law i μ hμ (by fun_prop)]
  norm_num

theorem sign_second_moment (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    (∫ p, p.2^2 ∂law i μ) = 1-cutoff i := by
  rw [integral_law i μ hμ (by fun_prop)]
  norm_num

theorem sign_variance (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    variance Prod.snd (law i μ) = 1-cutoff i := by
  rw [variance_eq_integral measurable_snd.aemeasurable, sign_mean i μ hμ]
  simpa using sign_second_moment i μ hμ

theorem demand_sign_covariance (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) :
    covariance Prod.fst Prod.snd (law i μ) = 0 := by
  have hX := memLp_of_bounded (demand_bounds i μ hμ)
    measurable_fst.aestronglyMeasurable 2
  have hY := memLp_of_bounded (sign_bounds i μ hμ)
    measurable_snd.aestronglyMeasurable 2
  rw [covariance_eq_sub hX hY]
  simp only [Pi.mul_apply, sign_mean i μ hμ, mul_zero, sub_zero]
  exact demand_sign_moment i μ hμ

def tiltedLaw (i : Row) (μ : Measure ℝ) (u : ℝ) : Measure Pair :=
  (law i μ).tilted (fun p => u*p.1)

theorem tiltedLaw_probability (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    IsProbabilityMeasure (tiltedLaw i μ u) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_of_bounded (law i μ)
    measurable_fst.aemeasurable (demand_bounds i μ hμ) u)

theorem tilted_integral (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ)
    {f : Pair → ℝ} (hf : Continuous f) :
    (∫ p, f p ∂tiltedLaw i μ u) =
      (1-cutoff i)*Real.exp (u/2-cgf Prod.fst (law i μ) u)*
        (f (1/2,1)+f (1/2,-1))/2+
      cutoff i*(∫ x, Real.exp (u*x-cgf Prod.fst (law i μ) u)*f (x,0) ∂μ) := by
  rw [tiltedLaw, integral_tilted_mul_eq_cgf _
    (integrable_exp_mul_of_bounded (law i μ) measurable_fst.aemeasurable
      (demand_bounds i μ hμ) u)]
  simp only [smul_eq_mul]
  rw [integral_law i μ hμ (by fun_prop)]
  simp only [smul_eq_mul]
  rw [show u*(1/2:ℝ) = u/2 by ring]
  ring

theorem tilted_sign_mean (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    (∫ p, p.2 ∂tiltedLaw i μ u) = 0 := by
  rw [tilted_integral i μ hμ u continuous_snd]
  simp

theorem tilted_demand_sign_moment (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    (∫ p, p.1*p.2 ∂tiltedLaw i μ u) = 0 := by
  rw [tilted_integral i μ hμ u (by fun_prop)]
  norm_num

def tiltedUpperMass (i : Row) (μ : Measure ℝ) (u : ℝ) : ℝ :=
  (1-cutoff i)*Real.exp (u/2-cgf Prod.fst (law i μ) u)

theorem tilted_sign_variance (i : Row) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    variance Prod.snd (tiltedLaw i μ u) = tiltedUpperMass i μ u := by
  letI := tiltedLaw_probability i μ hμ u
  rw [variance_eq_integral measurable_snd.aemeasurable, tilted_sign_mean i μ hμ u]
  simp only [sub_zero]
  rw [tilted_integral i μ hμ u (by fun_prop)]
  norm_num [tiltedUpperMass]

theorem tiltedUpperMass_pos (i : Row) (μ : Measure ℝ) (u : ℝ) :
    0 < tiltedUpperMass i μ u :=
  mul_pos (sub_pos.mpr (cutoff_lt_one i)) (Real.exp_pos _)

theorem tilted_demand_sign_covariance (i : Row) (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (u : ℝ) :
    covariance Prod.fst Prod.snd (tiltedLaw i μ u) = 0 := by
  letI := tiltedLaw_probability i μ hμ u
  have hac := tilted_absolutelyContinuous (law i μ) (fun p : Pair => u*p.1)
  have hX := memLp_of_bounded (hac.ae_le (demand_bounds i μ hμ))
    measurable_fst.aestronglyMeasurable 2
  have hY := memLp_of_bounded (hac.ae_le (sign_bounds i μ hμ))
    measurable_snd.aestronglyMeasurable 2
  change MemLp Prod.fst 2 (tiltedLaw i μ u) at hX
  change MemLp Prod.snd 2 (tiltedLaw i μ u) at hY
  rw [covariance_eq_sub hX hY]
  simp only [Pi.mul_apply, tilted_sign_mean i μ hμ u, mul_zero, sub_zero]
  exact tilted_demand_sign_moment i μ hμ u

def physicalLowerLaw (i : Row) (b : ℝ) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  G.map (fun p => exposure (xi i) b p.2)

theorem physicalLowerLaw_probability (i : Row) {b : ℝ} (hb : 0 < b)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] :
    IsProbabilityMeasure (physicalLowerLaw i b G) :=
  Measure.isProbabilityMeasure_map
    ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable

theorem physicalLowerLaw_bounds (i : Row) {b : ℝ} (hb : 0 < b)
    (G : Measure (ℝ × ℝ)) :
    ∀ᵐ x ∂physicalLowerLaw i b G, x ∈ Icc (0:ℝ) 1 := by
  apply (ae_map_iff
    ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aemeasurable
    measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall fun _ =>
    ⟨exposure_nonneg (xi_pos i) hb, exposure_le_one _ _ _⟩

theorem physical_tilted_covariance (i : Row) {b : ℝ} (hb : 0 < b)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (u : ℝ) :
    (∫ p, p.2 ∂tiltedLaw i (physicalLowerLaw i b G) u) = 0 ∧
    covariance Prod.fst Prod.snd (tiltedLaw i (physicalLowerLaw i b G) u) = 0 ∧
    0 < variance Prod.snd (tiltedLaw i (physicalLowerLaw i b G) u) := by
  letI := physicalLowerLaw_probability i hb G
  have hμ := physicalLowerLaw_bounds i hb G
  refine ⟨tilted_sign_mean i _ hμ u, tilted_demand_sign_covariance i _ hμ u, ?_⟩
  rw [tilted_sign_variance i _ hμ u]
  exact tiltedUpperMass_pos i _ u

end FCAppendix.Affine.Uniform06.MixedLaw
