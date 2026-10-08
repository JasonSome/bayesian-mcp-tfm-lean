import FCAppendix.Probability.GaussianPositivePart

noncomputable section
namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set

def secondPositivePart (y : ℝ) : ℝ :=
  (y^2+1)*cdf (gaussianReal 0 1) y+y*gaussianPDFReal 0 1 y

theorem integral_normal_positivePart_sq (y : ℝ) :
    (∫ z, (max (y-z) 0)^2 ∂gaussianReal 0 1) = secondPositivePart y := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have he : (fun z : ℝ => gaussianPDFReal 0 1 z*(max (y-z) 0)^2) =
      (Iic y).indicator (fun z => (y^2*gaussianPDFReal 0 1 z-(2*y)*(z*gaussianPDFReal 0 1 z))+
        z^2*gaussianPDFReal 0 1 z) := by
    funext z
    by_cases hz : z ≤ y
    · simp only [indicator,mem_Iic,if_pos hz,max_eq_left (sub_nonneg.mpr hz)]
      ring
    · simp [hz,max_eq_right (sub_nonpos.mpr (le_of_not_ge hz))]
  have hA : Integrable (fun z : ℝ => y^2*gaussianPDFReal 0 1 z) :=
    (integrable_gaussianPDFReal 0 1).const_mul (y^2)
  have hB : Integrable (fun z : ℝ => (2*y)*(z*gaussianPDFReal 0 1 z)) :=
    integrable_mul_normalPDF.const_mul (2*y)
  have hAB : Integrable (fun z : ℝ => y^2*gaussianPDFReal 0 1 z-(2*y)*(z*gaussianPDFReal 0 1 z)) := hA.sub hB
  rw [he,integral_indicator measurableSet_Iic,
    integral_add hAB.integrableOn integrable_sq_mul_normalPDF.integrableOn,
    integral_sub hA.integrableOn hB.integrableOn,
    integral_const_mul,integral_const_mul,integral_normalPDF_Iic,
    integral_mul_normalPDF_Iic,integral_sq_mul_normalPDF_Iic]
  unfold secondPositivePart
  ring

end FCAppendix.PayOnce.GaussianResponse
