import FCAppendix.PayOnce.GaussianResponseProfile
import FCAppendix.PayOnce.GaussianSecondPositivePart
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
namespace FCAppendix.PayOnce.GaussianResponse
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped BigOperators

def normalTaylor (x : ℝ) : ℝ := ∑ m ∈ Finset.range 12, (-(x^2)/2)^m/(m.factorial:ℝ)

def normalTaylorIntegral (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 12, (-1/2:ℝ)^m*x^(2*m+1)/((m.factorial:ℝ)*((2*m+1:ℕ):ℝ))

theorem normalTaylor_error {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |exp (-x^2/2)-normalTaylor x| ≤ 1/10^12 := by
  have hsq : x^2 ≤ 1 := pow_le_one₀ hx.1 hx.2
  have harg : |-x^2/2| ≤ 1/2 := by
    rw [abs_div,abs_neg,abs_of_nonneg (sq_nonneg x)]
    norm_num
    linarith
  have hh := Real.exp_bound (le_trans harg (by norm_num : (1/2:ℝ) ≤ 1)) (n := 12) (by norm_num)
  have hp := pow_le_pow_left₀ (abs_nonneg _) harg 12
  change |exp (-x^2/2)-normalTaylor x| ≤ _ at hh
  exact hh.trans (by norm_num at hp ⊢; nlinarith)

theorem integral_normalTaylor (x : ℝ) :
    (∫ u in (0:ℝ)..x, normalTaylor u)=normalTaylorIntegral x := by
  have he (u : ℝ) (m : ℕ) : (-u^2/2)^m=(-1/2:ℝ)^m*u^(2*m) := by
    rw [show -u^2/2=(-1/2:ℝ)*u^2 by ring,mul_pow,← pow_mul]
  unfold normalTaylor normalTaylorIntegral
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun m _ =>
    (show Continuous (fun u : ℝ => (-1/2:ℝ)^m*u^(2*m)/(m.factorial:ℝ)) by fun_prop).intervalIntegrable 0 x)]
  apply Finset.sum_congr rfl
  intro m _
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,integral_pow]
  simp only [zero_pow (by omega : 2*m+1 ≠ 0),sub_zero]
  push_cast
  field_simp

theorem normalTaylorIntegral_error {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |(∫ u in (0:ℝ)..x, exp (-u^2/2))-normalTaylorIntegral x| ≤ 1/10^12 := by
  have he : Continuous (fun u : ℝ => exp (-u^2/2)) := by fun_prop
  have hp : Continuous normalTaylor := by unfold normalTaylor; fun_prop
  rw [← integral_normalTaylor,← intervalIntegral.integral_sub (he.intervalIntegrable 0 x) (hp.intervalIntegrable 0 x)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
    (f := fun u => exp (-u^2/2)-normalTaylor u) (C := (1/10^12:ℝ)) (by
      intro u hu
      rw [uIoc_of_le hx.1] at hu
      simpa only [Real.norm_eq_abs] using normalTaylor_error ⟨hu.1.le,hu.2.trans hx.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hx.1] at hh
  exact hh.trans (by nlinarith [hx.2])

def entryResidual (r : ℝ) : ℝ :=
  exp (-r^2/2)+2*r*(∫ u in (0:ℝ)..r, exp (-u^2/2))-r*sqrt (2*Real.pi)

theorem responseMap_neg_residual (r : ℝ) :
    responseMap (-r)*cdf (gaussianReal 0 1) (-r)*sqrt (2*Real.pi)=entryResidual r := by
  let I := ∫ u in (0:ℝ)..r, exp (-u^2/2)
  have hc : 0 < sqrt (2*Real.pi) := sqrt_pos.2 (mul_pos (by norm_num) pi_pos)
  have hp := CorrelatedLoads.gaussian_cdf_pos (-r)
  have hφ : (∫ u in (0:ℝ)..r, gaussianPDFReal 0 1 u)=I/sqrt (2*Real.pi) := by
    simp_rw [normalPDF_eq]
    rw [intervalIntegral.integral_const_mul]
    rw [show I/sqrt (2*Real.pi)=(1/sqrt (2*Real.pi))*I by ring]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    exact congrArg Real.exp (by ring)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ uIcc (0:ℝ) r) => hasDerivAt_normalCDF u)
    ((show Continuous (gaussianPDFReal 0 1) by unfold gaussianPDFReal; fun_prop).intervalIntegrable 0 r)
  rw [hφ,cdf_gaussian_zero] at hFTC
  have hcdf : cdf (gaussianReal 0 1) (-r)=1/2-I/sqrt (2*Real.pi) := by
    rw [cdf_gaussian_neg]
    linarith
  have hpdf : gaussianPDFReal 0 1 (-r)=exp (-r^2/2)/sqrt (2*Real.pi) := by
    rw [normalPDF_eq]
    rw [show -(1/2:ℝ)*(-r)^2= -r^2/2 by ring]
    ring
  have he : responseMap (-r)*cdf (gaussianReal 0 1) (-r)=
      2*(-r)*cdf (gaussianReal 0 1) (-r)+gaussianPDFReal 0 1 (-r) := by
    unfold responseMap
    field_simp
  rw [he,hcdf,hpdf]
  change (2*(-r)*(1/2-I/sqrt (2*Real.pi))+exp (-r^2/2)/sqrt (2*Real.pi))*sqrt (2*Real.pi)=
    exp (-r^2/2)+2*r*I-r*sqrt (2*Real.pi)
  field_simp
  ring

theorem sqrt_two_pi_bounds :
    (2506628274631/10^12:ℝ) < sqrt (2*Real.pi) ∧ sqrt (2*Real.pi) < (2506628274632/10^12:ℝ) := by
  have hs := sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  have hn := sqrt_nonneg (2*Real.pi)
  constructor <;> nlinarith

theorem entryResidual_bounds {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    normalTaylor r+2*r*normalTaylorIntegral r-r*(2506628274632/10^12)-3/10^12 ≤ entryResidual r ∧
    entryResidual r ≤ normalTaylor r+2*r*normalTaylorIntegral r-r*(2506628274631/10^12)+3/10^12 := by
  have he := abs_le.mp (normalTaylor_error hr)
  have hI := abs_le.mp (normalTaylorIntegral_error hr)
  have hc := sqrt_two_pi_bounds
  have hIl := mul_le_mul_of_nonneg_left hI.1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.1)
  have hIu := mul_le_mul_of_nonneg_left hI.2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.1)
  have hcl := mul_le_mul_of_nonneg_left hc.1.le hr.1
  have hcu := mul_le_mul_of_nonneg_left hc.2.le hr.1
  unfold entryResidual
  constructor <;> nlinarith [hr.2]

theorem entryResidual_decimal_signs :
    0 < entryResidual (6120031809/10^10) ∧ entryResidual (6120031810/10^10) < 0 := by
  have hlo := (entryResidual_bounds (r := 6120031809/10^10) (by norm_num)).1
  have hhi := (entryResidual_bounds (r := 6120031810/10^10) (by norm_num)).2
  have hl : (0:ℝ) < normalTaylor (6120031809/10^10)+
      2*(6120031809/10^10)*normalTaylorIntegral (6120031809/10^10)-
      (6120031809/10^10)*(2506628274632/10^12)-3/10^12 := by
    norm_num [normalTaylor,normalTaylorIntegral,Finset.sum_range_succ,Nat.factorial_succ]
  have hu : normalTaylor (6120031810/10^10)+
      2*(6120031810/10^10)*normalTaylorIntegral (6120031810/10^10)-
      (6120031810/10^10)*(2506628274631/10^12)+3/10^12 < (0:ℝ) := by
    norm_num [normalTaylor,normalTaylorIntegral,Finset.sum_range_succ,Nat.factorial_succ]
  exact ⟨hl.trans_le hlo,hhi.trans_lt hu⟩

theorem response_zero_decimal_enclosure :
    -(6120031810/10^10:ℝ) < response 0 ∧ response 0 < -(6120031809/10^10:ℝ) := by
  have hc : 0 < sqrt (2*Real.pi) := sqrt_pos.2 (mul_pos (by norm_num) pi_pos)
  have hlo := entryResidual_decimal_signs.2
  have hhi := entryResidual_decimal_signs.1
  rw [← responseMap_neg_residual] at hlo hhi
  have hlo' : responseMap (-(6120031810/10^10:ℝ)) < 0 := by
    by_contra hh
    have hr : 0 ≤ responseMap (-(6120031810/10^10:ℝ)) := le_of_not_gt hh
    have hp := mul_nonneg (mul_nonneg hr (CorrelatedLoads.gaussian_cdf_pos (-(6120031810/10^10:ℝ))).le) hc.le
    exact (not_lt_of_ge hp) hlo
  have hhi' : 0 < responseMap (-(6120031809/10^10:ℝ)) := by
    by_contra hh
    have hr : responseMap (-(6120031809/10^10:ℝ)) ≤ 0 := le_of_not_gt hh
    have hp := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hr (CorrelatedLoads.gaussian_cdf_pos (-(6120031809/10^10:ℝ))).le) hc.le
    exact (not_lt_of_ge hp) hhi
  constructor
  · apply responseMap_strictMono.lt_iff_lt.mp
    simpa only [responseMap_response] using hlo'
  · apply responseMap_strictMono.lt_iff_lt.mp
    simpa only [responseMap_response] using hhi'

theorem secondPositivePart_div_success_at_zero :
    secondPositivePart (response 0)/Bayes.gaussianSuccessPrimitive (response 0)=
      response 0-1/response 0 := by
  let y := response 0
  have hy : y ≠ 0 := by
    have hh := response_zero_decimal_enclosure.2
    change y < -(6120031809/10^10:ℝ) at hh
    linarith
  have hp := CorrelatedLoads.gaussian_cdf_pos y
  have he := responseMap_response 0
  change 2*y+gaussianPDFReal 0 1 y/cdf (gaussianReal 0 1) y=0 at he
  have hφ : gaussianPDFReal 0 1 y= -2*y*cdf (gaussianReal 0 1) y := by
    have hh := (div_eq_iff hp.ne').mp (show gaussianPDFReal 0 1 y/cdf (gaussianReal 0 1) y= -2*y by linarith)
    exact hh
  change secondPositivePart y/Bayes.gaussianSuccessPrimitive y=y-1/y
  unfold secondPositivePart Bayes.gaussianSuccessPrimitive
  rw [hφ]
  have hden : y*cdf (gaussianReal 0 1) y+-2*y*cdf (gaussianReal 0 1) y=
      -y*cdf (gaussianReal 0 1) y := by ring
  rw [hden]
  field_simp
  ring

theorem copies_origin_decimal_enclosures :
    -(61200319/10^8:ℝ) < response 0 ∧ response 0 < -(61200318/10^8:ℝ) ∧
    (102197525/10^8:ℝ) < secondPositivePart (response 0)/Bayes.gaussianSuccessPrimitive (response 0) ∧
    secondPositivePart (response 0)/Bayes.gaussianSuccessPrimitive (response 0) < (102197526/10^8:ℝ) := by
  have hy := response_zero_decimal_enclosure
  refine ⟨by linarith [hy.1],by linarith [hy.2],?_⟩
  rw [secondPositivePart_div_success_at_zero]
  let r := -response 0
  have hr0 : 0 < r := by dsimp only [r]; linarith [hy.2]
  have hrl : (6120031809/10^10:ℝ) ≤ r := by dsimp only [r]; linarith [hy.2]
  have hru : r ≤ (6120031810/10^10:ℝ) := by dsimp only [r]; linarith [hy.1]
  have hl := one_div_le_one_div_of_le hr0 hru
  have hu := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<6120031809/10^10) hrl
  have he : response 0-1/response 0=1/r-r := by dsimp only [r]; field_simp; ring
  rw [he]
  have hlow : (102197525/10^8:ℝ)<1/(6120031810/10^10)-(6120031810/10^10) := by norm_num
  have hhigh : 1/(6120031809/10^10)-(6120031809/10^10)<(102197526/10^8:ℝ) := by norm_num
  constructor <;> linarith

end FCAppendix.PayOnce.GaussianResponse
