import FCAppendix.PayOnce.GaussianTruncatedMoments
import ProbabilityApproximation.ChenShao.SteinProductDerivative

noncomputable section
namespace FCAppendix.PayOnce.GaussianTilt
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

def negativeHalfExp (v z : ℝ) : ℝ := (Iic 0).indicator (fun z => Real.exp (v*z)) z

theorem measurable_negativeHalfExp (v : ℝ) : Measurable (negativeHalfExp v) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).indicator measurableSet_Iic

theorem negativeHalfExp_bounds {v : ℝ} (hv : 0 ≤ v) (z : ℝ) :
    negativeHalfExp v z ∈ Icc (0:ℝ) 1 := by
  by_cases hz : z ≤ 0
  · simp only [negativeHalfExp,indicator_of_mem (show z ∈ Iic 0 from hz),mem_Icc]
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hv hz)⟩
  · simp only [negativeHalfExp,indicator_of_notMem (show z ∉ Iic 0 from hz)]
    exact ⟨le_rfl,zero_le_one⟩

theorem integrable_negativeHalfExp_of_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ]
    {v : ℝ} (hv : 0 ≤ v) : Integrable (negativeHalfExp v) μ := by
  apply Integrable.of_bound (measurable_negativeHalfExp v).aestronglyMeasurable 1
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs,abs_of_nonneg (negativeHalfExp_bounds hv z).1] using
    (negativeHalfExp_bounds hv z).2

theorem integrable_negativeHalfExp (v : ℝ) :
    Integrable (negativeHalfExp v) (gaussianReal 0 1) :=
  (integrable_exp_mul_gaussianReal v).indicator measurableSet_Iic

def prefactor (v : ℝ) : ℝ := ∫ z in Iic 0, Real.exp (v*z) ∂gaussianReal 0 1

theorem prefactor_eq_integral (v : ℝ) :
    prefactor v = ∫ z, negativeHalfExp v z ∂gaussianReal 0 1 :=
  (integral_indicator measurableSet_Iic).symm

theorem prefactor_eq_strict_integral (v : ℝ) :
    prefactor v = ∫ z in Iio 0, Real.exp (v*z) ∂gaussianReal 0 1 := by
  letI := nullSingletonClass_gaussianReal (μ := 0) (by norm_num : (1:NNReal) ≠ 0)
  exact integral_Iic_eq_integral_Iio

theorem weighted_normalPDF (v z : ℝ) :
    φ z*Real.exp (v*z) = Real.exp (v^2/2)*φ (z-v) := by
  rw [GaussianResponse.normalPDF_eq,GaussianResponse.normalPDF_eq]
  have he : Real.exp (v*z)*Real.exp (-(1/2:ℝ)*z^2) =
      Real.exp (v^2/2)*Real.exp (-(1/2:ℝ)*(z-v)^2) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  calc
    _ = (1/Real.sqrt (2*Real.pi))*(Real.exp (v*z)*Real.exp (-(1/2:ℝ)*z^2)) := by ring
    _ = _ := by rw [he]; ring

theorem prefactor_eq_exp_mul_cdf (v : ℝ) :
    prefactor v = Real.exp (v^2/2)*Φ (-v) := by
  have hi : Integrable (fun z : ℝ => φ z*Real.exp (v*z)) := by
    simpa only [weighted_normalPDF] using
      ((integrable_gaussianPDFReal 0 1).comp_sub_right v).const_mul (Real.exp (v^2/2))
  have hd (z : ℝ) : HasDerivAt (fun x => Real.exp (v^2/2)*Φ (x-v))
      (φ z*Real.exp (v*z)) z := by
    have hh := ((GaussianResponse.hasDerivAt_normalCDF (z-v)).comp z
      ((hasDerivAt_id z).sub_const v)).const_mul (Real.exp (v^2/2))
    simpa only [mul_one,weighted_normalPDF,Function.comp_apply,id_eq] using hh
  have hlim : Tendsto (fun z : ℝ => Real.exp (v^2/2)*Φ (z-v)) atBot (𝓝 0) := by
    have hs : Tendsto (fun z : ℝ => z-v) atBot atBot := by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atBot_add_const_right atBot (-v) tendsto_id
    simpa only [mul_zero,Function.comp_apply] using ((tendsto_cdf_atBot (gaussianReal 0 1)).comp hs).const_mul (Real.exp (v^2/2))
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun z (_ : z ∈ Iic (0:ℝ)) => hd z) hi.integrableOn hlim
  unfold prefactor
  conv_lhs =>
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:NNReal) ≠ 0),
      setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF 0 1)
        (Eventually.of_forall fun _ => gaussianPDF_lt_top) _ measurableSet_Iic]
  simpa only [toReal_gaussianPDF,smul_eq_mul,zero_sub,sub_zero] using hFTC

theorem prefactor_pos (v : ℝ) : 0 < prefactor v := by
  rw [prefactor_eq_exp_mul_cdf]
  exact mul_pos (Real.exp_pos _) (CorrelatedLoads.gaussian_cdf_pos _)

theorem prefactor_le_one {v : ℝ} (hv : 0 ≤ v) : prefactor v ≤ 1 := by
  rw [prefactor_eq_integral]
  have hh := integral_mono (integrable_negativeHalfExp v) (integrable_const (1:ℝ))
    (fun z => (negativeHalfExp_bounds hv z).2)
  simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using hh

theorem exp_mul_normalPDF (v : ℝ) : Real.exp (v^2/2)*φ v = φ 0 := by
  rw [GaussianResponse.normalPDF_eq,GaussianResponse.normalPDF_eq]
  have he : Real.exp (v^2/2)*Real.exp (-(1/2:ℝ)*v^2) = 1 := by
    rw [← Real.exp_add,show v^2/2+(-(1/2:ℝ)*v^2)=0 by ring,Real.exp_zero]
  calc
    _ = (1/Real.sqrt (2*Real.pi))*(Real.exp (v^2/2)*Real.exp (-(1/2:ℝ)*v^2)) := by ring
    _ = _ := by rw [he]; norm_num

theorem prefactor_mills_bounds {v : ℝ} (hv : 0 < v) :
    φ 0*v/(1+v^2) ≤ prefactor v ∧ prefactor v ≤ φ 0/v := by
  have hlo := mul_le_mul_of_nonneg_left
    (gaussianPDF_mul_div_one_add_sq_le_one_sub_cdf hv.le) (Real.exp_pos (v^2/2)).le
  have hhi := mul_le_mul_of_nonneg_left
    (one_sub_cdf_gaussian_le_pdf_div hv) (Real.exp_pos (v^2/2)).le
  have hp : prefactor v = Real.exp (v^2/2)*(1-Φ v) := by
    rw [prefactor_eq_exp_mul_cdf,cdf_gaussian_neg]
  constructor
  · calc
      φ 0*v/(1+v^2) = (Real.exp (v^2/2)*φ v)*(v/(1+v^2)) := by
        rw [exp_mul_normalPDF]
        ring
      _ = Real.exp (v^2/2)*(v/(1+v^2)*φ v) := by ring
      _ ≤ Real.exp (v^2/2)*(1-Φ v) := hlo
      _ = prefactor v := hp.symm
  · calc
      prefactor v = Real.exp (v^2/2)*(1-Φ v) := hp
      _ ≤ Real.exp (v^2/2)*(φ v/v) := hhi
      _ = φ 0/v := by rw [← mul_div_assoc,exp_mul_normalPDF]

def lowerConstant : ℝ := min (Φ (-1)) (φ 0/2)

def upperConstant : ℝ := 2+2*φ 0

theorem lowerConstant_pos : 0 < lowerConstant :=
  lt_min (CorrelatedLoads.gaussian_cdf_pos _) (div_pos (gaussianPDFReal_pos 0 1 0 (by norm_num)) (by norm_num))

theorem upperConstant_pos : 0 < upperConstant := by
  have hφ := gaussianPDFReal_nonneg 0 1 0
  unfold upperConstant
  linarith

theorem prefactor_bounds {v : ℝ} (hv : 0 ≤ v) :
    lowerConstant/(1+v) ≤ prefactor v ∧ prefactor v ≤ upperConstant/(1+v) := by
  have hden : 0 < 1+v := by linarith
  have hφ := gaussianPDFReal_nonneg 0 1 0
  by_cases hv1 : v ≤ 1
  · have hcdf : Φ (-1) ≤ Φ (-v) := monotone_cdf _ (by linarith)
    have hexp : 1 ≤ Real.exp (v^2/2) := Real.one_le_exp_iff.mpr (by positivity)
    have hlo : Φ (-1) ≤ prefactor v := by
      rw [prefactor_eq_exp_mul_cdf]
      exact hcdf.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hexp (cdf_nonneg (gaussianReal 0 1) (-v)))
    constructor
    · calc
        lowerConstant/(1+v) ≤ lowerConstant := (div_le_self lowerConstant_pos.le (by linarith))
        _ ≤ Φ (-1) := min_le_left _ _
        _ ≤ prefactor v := hlo
    · apply (le_div_iff₀ hden).mpr
      have hh := mul_le_mul_of_nonneg_right (prefactor_le_one hv) hden.le
      unfold upperConstant
      nlinarith
  · have hvpos : 0 < v := by linarith
    have hm := prefactor_mills_bounds hvpos
    constructor
    · have hlower : (φ 0/2)/(1+v) ≤ φ 0*v/(1+v^2) := by
        apply (div_le_div_iff₀ hden (by positivity : 0 < 1+v^2)).mpr
        have hvlarge : 1 ≤ v := by linarith
        nlinarith [mul_nonneg hφ (sq_nonneg (v-1))]
      exact (div_le_div_of_nonneg_right (min_le_right _ _) hden.le).trans (hlower.trans hm.1)
    · apply hm.2.trans
      apply (div_le_div_iff₀ hvpos hden).mpr
      unfold upperConstant
      have hvlarge : 1 ≤ v := by linarith
      nlinarith [mul_nonneg hφ (sub_nonneg.mpr hvlarge)]

theorem exists_prefactor_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ v : ℝ, 0 ≤ v → c/(1+v) ≤ prefactor v ∧ prefactor v ≤ C/(1+v) :=
  ⟨lowerConstant,upperConstant,lowerConstant_pos,upperConstant_pos,fun _ hv => prefactor_bounds hv⟩

end FCAppendix.PayOnce.GaussianTilt
