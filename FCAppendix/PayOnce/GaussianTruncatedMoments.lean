import FCAppendix.Finite.PPIGaussianPrimitive
import FCAppendix.Probability.CorrelatedLoads

noncomputable section
namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

theorem normalPDF_eq (x : ℝ) :
    φ x = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1/2:ℝ)*x^2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -x^2 / 2 = -(1/2:ℝ)*x^2 by ring]
  simp only [one_div]

theorem hasDerivAt_normalCDF (x : ℝ) : HasDerivAt (fun z => Φ z) (φ x) x :=
  hasDerivAt_Φ x

theorem integrable_mul_normalPDF : Integrable (fun x : ℝ => x * φ x) := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul
    (1 / Real.sqrt (2 * Real.pi))
  convert h using 1
  funext x
  rw [normalPDF_eq]
  ring

theorem integrable_sq_mul_normalPDF : Integrable (fun x : ℝ => x^2 * φ x) := by
  have hi : Integrable (fun x : ℝ => x^2 * Real.exp (-(1/2:ℝ)*x^2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2) (by norm_num : (-1:ℝ) < 2)
  convert hi.const_mul (1 / Real.sqrt (2 * Real.pi)) using 1
  funext x
  rw [normalPDF_eq]
  ring

theorem normalPDF_tendsto_atBot : Tendsto φ atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => Bayes.hasDerivAt_standardGaussianPDF x)
  · have hi : Integrable (fun x : ℝ => -x * φ x) :=
      integrable_mul_normalPDF.neg.congr (Eventually.of_forall fun x => by
        change -(x * φ x) = -x * φ x
        ring)
    exact hi.integrableOn
  · exact (integrable_gaussianPDFReal 0 1).integrableOn

theorem hasDerivAt_mul_normalPDF (x : ℝ) :
    HasDerivAt (fun z : ℝ => z * φ z) (φ x - x^2*φ x) x := by
  have h := (hasDerivAt_id x).mul (Bayes.hasDerivAt_standardGaussianPDF x)
  apply h.congr_deriv
  dsimp only [id_eq]
  ring

theorem mul_normalPDF_tendsto_atBot :
    Tendsto (fun x : ℝ => x * φ x) atBot (𝓝 0) := by
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => hasDerivAt_mul_normalPDF x)
    ((integrable_gaussianPDFReal 0 1).sub integrable_sq_mul_normalPDF).integrableOn
    integrable_mul_normalPDF.integrableOn

theorem integral_normalPDF_Iic (y : ℝ) : ∫ x in Iic y, φ x = Φ y := by
  have hh := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun x (_ : x ∈ Iic y) => hasDerivAt_normalCDF x)
    (integrable_gaussianPDFReal 0 1).integrableOn (tendsto_cdf_atBot (gaussianReal 0 1))
  simpa only [sub_zero] using hh

theorem integral_mul_normalPDF_Iic (y : ℝ) : ∫ x in Iic y, x * φ x = -φ y := by
  have hd (x : ℝ) : HasDerivAt (fun z => -φ z) (x * φ x) x := by
    exact ((Bayes.hasDerivAt_standardGaussianPDF x).neg).congr_deriv (by ring)
  have hh := integral_Iic_of_hasDerivAt_of_tendsto' (fun x (_ : x ∈ Iic y) => hd x)
    integrable_mul_normalPDF.integrableOn normalPDF_tendsto_atBot.neg
  simpa only [neg_zero,sub_zero] using hh

theorem integral_sq_mul_normalPDF_Iic (y : ℝ) :
    ∫ x in Iic y, x^2 * φ x = Φ y - y * φ y := by
  have hd (x : ℝ) : HasDerivAt (fun z => Φ z - z * φ z) (x^2 * φ x) x := by
    exact ((hasDerivAt_normalCDF x).sub (hasDerivAt_mul_normalPDF x)).congr_deriv (by ring)
  have hh := integral_Iic_of_hasDerivAt_of_tendsto' (fun x (_ : x ∈ Iic y) => hd x)
    integrable_sq_mul_normalPDF.integrableOn
    ((tendsto_cdf_atBot (gaussianReal 0 1)).sub mul_normalPDF_tendsto_atBot)
  simpa only [sub_zero] using hh

theorem truncated_variance_nonneg (y : ℝ) :
    0 ≤ 1 - y * (φ y / Φ y) - (φ y / Φ y)^2 := by
  let r := φ y / Φ y
  have hzero : Integrable (fun x : ℝ => r^2*φ x) :=
    (integrable_gaussianPDFReal 0 1).const_mul (r^2)
  have hfirst : Integrable (fun x : ℝ => (2*r)*(x*φ x)) :=
    integrable_mul_normalPDF.const_mul (2*r)
  have hsum : Integrable (fun x : ℝ => x^2*φ x+(2*r)*(x*φ x)) :=
    integrable_sq_mul_normalPDF.add hfirst
  have he : (∫ x in Iic y, (x+r)^2*φ x) = Φ y-y*φ y-2*r*φ y+r^2*Φ y := by
    have hx : (fun x : ℝ => (x+r)^2*φ x) =
        fun x => (x^2*φ x+(2*r)*(x*φ x))+r^2*φ x := by funext x; ring
    rw [hx,integral_add hsum.integrableOn hzero.integrableOn,
      integral_add integrable_sq_mul_normalPDF.integrableOn hfirst.integrableOn,
      integral_const_mul,integral_const_mul,integral_sq_mul_normalPDF_Iic,
      integral_mul_normalPDF_Iic,integral_normalPDF_Iic]
    ring
  have hn : 0 ≤ ∫ x in Iic y, (x+r)^2*φ x :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x)
  rw [he] at hn
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  have hr : r * Φ y = φ y := div_mul_cancel₀ _ hp.ne'
  apply (nonneg_of_mul_nonneg_left (b := Φ y) ?_ hp)
  change 0 ≤ (1-y*r-r^2) * Φ y
  rw [← hr] at hn
  nlinarith only [hn]

end FCAppendix.PayOnce.GaussianResponse
