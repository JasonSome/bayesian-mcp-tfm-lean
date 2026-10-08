import FCAppendix.PayOnce.GaussianResponseProfile
import Mathlib.Probability.ConditionalProbability

namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set Filter Topology
local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

theorem integral_cond_normal_Iic (f : ℝ → ℝ) (y : ℝ) :
    (∫ z, f z ∂cond (gaussianReal 0 1) (Iic y)) = (∫ z in Iic y, f z*φ z)/Φ y := by
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv]
  simp only [smul_eq_mul]
  rw [← measureReal_def]
  rw [← cdf_eq_real,← integral_indicator measurableSet_Iic,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have he : (fun z : ℝ => φ z • (Iic y).indicator f z)=
      (Iic y).indicator (fun z => f z*φ z) := by
    funext z
    by_cases hz : z ∈ Iic y <;> simp [hz,mul_comm]
  rw [he,integral_indicator measurableSet_Iic]
  ring

theorem truncated_variance_formula (y : ℝ) :
    ProbabilityTheory.variance (fun z : ℝ => z) (cond (gaussianReal 0 1) (Iic y)) =
      1-y*(φ y/Φ y)-(φ y/Φ y)^2 := by
  have hmean : (∫ z : ℝ, z ∂cond (gaussianReal 0 1) (Iic y)) = -(φ y/Φ y) := by
    rw [integral_cond_normal_Iic,integral_mul_normalPDF_Iic]
    ring
  rw [variance_eq_integral (X := fun z : ℝ => z) (by fun_prop),hmean,integral_cond_normal_Iic]
  let r := φ y/Φ y
  change (∫ z in Iic y, (z- -r)^2*φ z)/Φ y=1-y*r-r^2
  have hzero : Integrable (fun x : ℝ => r^2*φ x) :=
    (integrable_gaussianPDFReal 0 1).const_mul (r^2)
  have hfirst : Integrable (fun x : ℝ => (2*r)*(x*φ x)) :=
    integrable_mul_normalPDF.const_mul (2*r)
  have hsum : Integrable (fun x : ℝ => x^2*φ x+(2*r)*(x*φ x)) :=
    integrable_sq_mul_normalPDF.add hfirst
  have hx : (fun z : ℝ => (z- -r)^2*φ z) =
      fun z => (z^2*φ z+(2*r)*(z*φ z))+r^2*φ z := by funext z; ring
  rw [hx,integral_add hsum.integrableOn hzero.integrableOn,
    integral_add integrable_sq_mul_normalPDF.integrableOn hfirst.integrableOn,
    integral_const_mul,integral_const_mul,integral_sq_mul_normalPDF_Iic,
    integral_mul_normalPDF_Iic,integral_normalPDF_Iic]
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  dsimp only [r]
  field_simp
  ring

theorem responseMap_deriv_eq_one_add_variance (y : ℝ) :
    deriv responseMap y = 1+ProbabilityTheory.variance (fun z : ℝ => z)
      (cond (gaussianReal 0 1) (Iic y)) := by
  rw [(hasDerivAt_responseMap y).deriv,truncated_variance_formula]
  ring

theorem truncated_variance_pos (y : ℝ) :
    0 < 1-y*(φ y/Φ y)-(φ y/Φ y)^2 := by
  let r := φ y/Φ y
  have hzero : Integrable (fun x : ℝ => r^2*φ x) :=
    (integrable_gaussianPDFReal 0 1).const_mul (r^2)
  have hfirst : Integrable (fun x : ℝ => (2*r)*(x*φ x)) :=
    integrable_mul_normalPDF.const_mul (2*r)
  have hsum : Integrable (fun x : ℝ => x^2*φ x+(2*r)*(x*φ x)) :=
    integrable_sq_mul_normalPDF.add hfirst
  have hi : Integrable (fun x : ℝ => (x+r)^2*φ x) :=
    (hsum.add hzero).congr (.of_forall fun x => by dsimp only [Pi.add_apply]; ring)
  have he : (∫ x in Iic y, (x+r)^2*φ x)=Φ y-y*φ y-2*r*φ y+r^2*Φ y := by
    have hx : (fun x : ℝ => (x+r)^2*φ x) =
        fun x => (x^2*φ x+(2*r)*(x*φ x))+r^2*φ x := by funext x; ring
    rw [hx,integral_add hsum.integrableOn hzero.integrableOn,
      integral_add integrable_sq_mul_normalPDF.integrableOn hfirst.integrableOn,
      integral_const_mul,integral_const_mul,integral_sq_mul_normalPDF_Iic,
      integral_mul_normalPDF_Iic,integral_normalPDF_Iic]
    ring
  have hpos : 0 < ∫ x in Iic y, (x+r)^2*φ x := by
    apply (integral_pos_iff_support_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 1 x)) hi.integrableOn).mpr
    have hs : Ioo (min y (-r)-2) (min y (-r)-1) ⊆
        Function.support (fun x : ℝ => (x+r)^2*φ x) := by
      intro x hx
      have hxr : x+r < 0 := by linarith [hx.2,min_le_right y (-r)]
      exact (mul_pos (sq_pos_of_ne_zero hxr.ne) (gaussianPDFReal_pos 0 1 x (by norm_num))).ne'
    apply lt_of_lt_of_le (b := (volume.restrict (Iic y)) (Ioo (min y (-r)-2) (min y (-r)-1))) ?_
      (measure_mono hs)
    rw [Measure.restrict_apply measurableSet_Ioo,inter_eq_left.mpr (show
      Ioo (min y (-r)-2) (min y (-r)-1) ⊆ Iic y from fun x hx => by
        change x ≤ y
        linarith [hx.2,min_le_left y (-r)]),Real.volume_Ioo]
    norm_num
  rw [he] at hpos
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  have hr : r*Φ y=φ y := div_mul_cancel₀ _ hp.ne'
  apply (pos_of_mul_pos_left (b := Φ y) ?_ hp.le)
  change 0 < (1-y*r-r^2)*Φ y
  rw [← hr] at hpos
  nlinarith only [hpos]

theorem responseMap_deriv_mem_Ioo (y : ℝ) :
    2-y*(φ y/Φ y)-(φ y/Φ y)^2 ∈ Ioo (1:ℝ) 2 := by
  refine ⟨by linarith [truncated_variance_pos y],?_⟩
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  have hφ := gaussianPDFReal_pos 0 1 y (by norm_num)
  have ht := successPrimitive_pos y
  rw [Bayes.gaussianSuccessPrimitive] at ht
  have hy : 0 < y+φ y/Φ y := by
    apply (div_pos ht hp).trans_eq
    field_simp
  have hh := mul_pos (div_pos hφ hp) hy
  nlinarith only [hh]

end FCAppendix.PayOnce.GaussianResponse
