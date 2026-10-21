import FCAppendix.Affine.Uniform06.EntryGaussianLaw
import FCAppendix.Affine.Uniform06.EntryHazard
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryConvolution
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.PayOnce.GaussianResponse
open FCAppendix.Affine.Uniform06.EntryGaussian
local notation "γ" => gaussianReal 0 1
local notation "Φ" => cdf γ
local notation "φ" => gaussianPDFReal 0 1

lemma normalPDF_le_at_zero (x : ℝ) : φ x ≤ φ 0 := by
  rw [normalPDF_eq,normalPDF_eq]
  norm_num only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,Real.exp_zero,mul_one]
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

lemma normalPDF_abs (x : ℝ) : φ |x|=φ x := by
  simp only [normalPDF_eq,sq_abs]

@[fun_prop] lemma continuous_normalPDF : Continuous φ :=
  continuous_iff_continuousAt.mpr fun x =>
    (FCAppendix.Bayes.hasDerivAt_standardGaussianPDF x).continuousAt

def convolutionDensity (a b s : ℝ) : ℝ := ∫ y, φ ((s-b*|y|)/a)/a ∂γ

theorem hasDerivAt_actual_cdf {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    HasDerivAt (cdf (EntryGaussianLaw.law a b)) (convolutionDensity a b s) s := by
  let F : ℝ → ℝ → ℝ := fun t y => Φ ((t-b*|y|)/a)
  let F' : ℝ → ℝ → ℝ := fun t y => φ ((t-b*|y|)/a)/a
  have hF (t : ℝ) : AEStronglyMeasurable (F t) γ := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F]
    exact (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_normalCDF x).continuousAt).comp
      ((continuous_const.sub (continuous_const.mul continuous_abs)).div_const a)
  have hi : Integrable (F s) γ := by
    apply Integrable.of_bound (hF s) 1
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg γ _)]
      exact cdf_le_one γ _
  have hd (y t : ℝ) : HasDerivAt (fun r => F r y) (F' t y) t := by
    have hh := (hasDerivAt_normalCDF ((t-b*|y|)/a)).comp t
      (((hasDerivAt_id t).sub_const (b*|y|)).div_const a)
    convert! hh using 1
    dsimp only [F,F']
    ring
  have hbound : ∀ᵐ y ∂γ, ∀ t ∈ (univ : Set ℝ), ‖F' t y‖ ≤ φ 0/a := by
    apply Eventually.of_forall
    intro y t _
    dsimp only [F']
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) ha.le)]
    exact div_le_div_of_nonneg_right (normalPDF_le_at_zero _) ha.le
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := (univ : Set ℝ)) (by simp) (Eventually.of_forall hF) hi
    (show AEStronglyMeasurable (F' s) γ from by
      apply Continuous.aestronglyMeasurable
      dsimp only [F']; fun_prop)
    hbound (integrable_const (φ 0/a))
    (Eventually.of_forall fun y t _ => hd y t)
  have he : cdf (EntryGaussianLaw.law a b)=fun t => ∫ y, F t y ∂γ :=
    funext (EntryGaussianLaw.cdf_eq_integral ha b)
  rw [he]
  exact hD.2

def totalScale (a b : ℝ) : ℝ := Real.sqrt (a^2+b^2)

lemma totalScale_pos {a : ℝ} (ha : 0 < a) (b : ℝ) : 0 < totalScale a b := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_pos_of_pos ha,sq_nonneg b]

lemma totalScale_sq (a b : ℝ) : (totalScale a b)^2=a^2+b^2 :=
  Real.sq_sqrt (by positivity)

theorem gaussian_product_completion {a : ℝ} (ha : 0 < a) (b s y : ℝ) :
    φ y*(φ ((s-b*y)/a)/a)=
      (φ (s/totalScale a b)/totalScale a b)*
        ((totalScale a b/a)*φ ((totalScale a b/a)*(y-b*s/(totalScale a b)^2))) := by
  have hω := totalScale_pos ha b
  have hs := totalScale_sq a b
  have he0 :
      (-(1/2 : ℝ)*y^2 + -(1/2 : ℝ)*((s-b*y)/a)^2) -
      (-(1/2 : ℝ)*(s/totalScale a b)^2 +
        -(1/2 : ℝ)*((totalScale a b/a)*(y-b*s/(totalScale a b)^2))^2) =
      ((a^2+b^2-(totalScale a b)^2)*(s^2-(totalScale a b)^2*y^2))/
        (2*a^2*(totalScale a b)^2) := by
    field_simp [ha.ne',hω.ne']
    ring
  have hz : a^2+b^2-(totalScale a b)^2=0 := by rw [hs]; ring
  rw [hz,zero_mul,zero_div] at he0
  have he : -(1/2 : ℝ)*y^2 + -(1/2 : ℝ)*((s-b*y)/a)^2 =
      -(1/2 : ℝ)*(s/totalScale a b)^2 +
        -(1/2 : ℝ)*((totalScale a b/a)*(y-b*s/(totalScale a b)^2))^2 := by
    linarith
  have hex := congrArg Real.exp he
  simp only [Real.exp_add] at hex
  simp only [normalPDF_eq]
  calc
    _ = ((1/Real.sqrt (2*Real.pi))^2/a)*
        (Real.exp (-(1/2 : ℝ)*y^2)*Real.exp (-(1/2 : ℝ)*((s-b*y)/a)^2)) := by ring
    _ = ((1/Real.sqrt (2*Real.pi))^2/a)*
        (Real.exp (-(1/2 : ℝ)*(s/totalScale a b)^2)*
          Real.exp (-(1/2 : ℝ)*((totalScale a b/a)*(y-b*s/(totalScale a b)^2))^2)) := by
      rw [hex]
    _ = _ := by field_simp [ha.ne',hω.ne']

theorem integral_conditional_gaussian {r : ℝ} (hr : 0 < r) (d : ℝ) :
    (∫ y in Ioi (0 : ℝ), r*φ (r*(y-d)))=Φ (r*d) := by
  have hd (y : ℝ) : HasDerivAt (fun t => Φ (r*(t-d))) (r*φ (r*(y-d))) y := by
    have hh := (hasDerivAt_normalCDF (r*(y-d))).comp y
      (((hasDerivAt_id y).sub_const d).const_mul r)
    convert! hh using 1
    ring
  have harg : Tendsto (fun y : ℝ => r*(y-d)) atTop atTop :=
    (by
      have hshift : Tendsto (fun y : ℝ => y-d) atTop atTop := by
        simpa only [sub_eq_add_neg,id_eq] using
          tendsto_atTop_add_const_right atTop (-d) (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
      exact hshift.const_mul_atTop hr)
  have ht := (tendsto_cdf_atTop γ).comp harg
  have he := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun y (_ : y ∈ Ici (0 : ℝ)) => hd y)
    (fun y (_ : y ∈ Ioi (0 : ℝ)) => mul_nonneg hr.le (gaussianPDFReal_nonneg _ _ _)) ht
  have hn : r*((0 : ℝ)-d)=-(r*d) := by ring
  rw [hn,cdf_gaussian_neg] at he
  linarith

theorem actual_density_eq_foldedKernel {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    convolutionDensity a b s =
      foldedKernel (totalScale a b) (b/(a*totalScale a b)) s := by
  have hω := totalScale_pos ha b
  unfold convolutionDensity
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have he : (fun y : ℝ => φ y*(φ ((s-b*|y|)/a)/a)) =
      (fun y => (fun t => φ t*(φ ((s-b*t)/a)/a)) |y|) := by
    funext y
    change φ y*(φ ((s-b*|y|)/a)/a)= (φ |y|)*(φ ((s-b*|y|)/a)/a)
    rw [normalPDF_abs]
  rw [he]
  have habs : (∫ y : ℝ, (fun t => φ t*(φ ((s-b*t)/a)/a)) |y|) =
      2*∫ y in Ioi (0 : ℝ), φ y*(φ ((s-b*y)/a)/a) := by
    convert! integral_comp_abs (f := fun t => φ t*(φ ((s-b*t)/a)/a)) using 1
  rw [habs]
  simp_rw [gaussian_product_completion ha b s]
  rw [integral_const_mul,integral_conditional_gaussian (div_pos hω ha)]
  have harg : (totalScale a b/a)*(b*s/(totalScale a b)^2) =
      (b/(a*totalScale a b))*s := by
    field_simp [ha.ne',hω.ne']
  rw [harg]
  unfold foldedKernel
  ring

theorem hasDerivAt_actual_cdf_explicit {a : ℝ} (ha : 0 < a) (b s : ℝ) :
    HasDerivAt (cdf (EntryGaussianLaw.law a b))
      (foldedKernel (totalScale a b) (b/(a*totalScale a b)) s) s := by
  simpa only [actual_density_eq_foldedKernel ha b s] using hasDerivAt_actual_cdf ha b s

lemma scaled_normalPDF_integrable {ω : ℝ} (hω : 0 < ω) :
    Integrable (fun x : ℝ => φ (x/ω)) := by
  have he : (fun x : ℝ => φ (x/ω)) =
      (fun x => (1/Real.sqrt (2*Real.pi))*Real.exp (-(1/(2*ω^2))*x^2)) := by
    funext x
    rw [normalPDF_eq]
    congr 2
    field_simp [hω.ne']
  rw [he]
  exact (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ)<1/(2*ω^2))).const_mul _

lemma scaled_mul_normalPDF_integrable {ω : ℝ} (hω : 0 < ω) :
    Integrable (fun x : ℝ => |x| *φ (x/ω)) := by
  have hh := (integrable_mul_exp_neg_mul_sq
    (by positivity : (0 : ℝ)<1/(2*ω^2))).abs.const_mul (1/Real.sqrt (2*Real.pi))
  convert! hh using 1
  funext x
  rw [normalPDF_eq,abs_mul,abs_of_pos (Real.exp_pos _)]
  have he : -(1/2 : ℝ)*(x/ω)^2=-(1/(2*ω^2))*x^2 := by
    field_simp [hω.ne']
  rw [he]
  ring

lemma foldedKernel_le {ω c : ℝ} (hω : 0 < ω) (x : ℝ) :
    foldedKernel ω c x ≤ (2/ω)*φ (x/ω) := by
  unfold foldedKernel
  exact mul_le_of_le_one_right
    (mul_nonneg (div_nonneg (by norm_num) hω.le) (gaussianPDFReal_nonneg _ _ _))
    (cdf_le_one γ _)

lemma continuous_foldedKernel (ω c : ℝ) : Continuous (foldedKernel ω c) := by
  have hΦ : Continuous Φ := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_normalCDF x).continuousAt
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x =>
    (FCAppendix.Bayes.hasDerivAt_standardGaussianPDF x).continuousAt
  unfold foldedKernel
  exact (continuous_const.mul (hφ.comp (continuous_id.div_const ω))).mul
    (hΦ.comp (continuous_const.mul continuous_id))

lemma integrable_foldedKernel {ω c : ℝ} (hω : 0 < ω) : Integrable (foldedKernel ω c) := by
  apply Integrable.mono' ((scaled_normalPDF_integrable hω).const_mul (2/ω))
    (continuous_foldedKernel ω c).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (foldedKernel_pos hω x)]
    exact foldedKernel_le hω x

def logSlope (ω c x : ℝ) : ℝ := -x/ω^2+c*inverseMills (c*x)

lemma hasDerivAt_foldedKernel {ω c : ℝ} (hω : 0 < ω) (x : ℝ) :
    HasDerivAt (foldedKernel ω c) (logSlope ω c x*foldedKernel ω c x) x := by
  have h := (hasDerivAt_log_foldedKernel (c := c) hω x).exp
  simp_rw [Real.exp_log (foldedKernel_pos hω _)] at h
  simpa only [logSlope,mul_comm] using h

lemma logSlope_mul_identity {ω c : ℝ} (hω : 0 < ω) (x : ℝ) :
    logSlope ω c x*foldedKernel ω c x =
      (-x/ω^2)*foldedKernel ω c x+(2/ω)*c*φ (x/ω)*φ (c*x) := by
  have hF := FCAppendix.CorrelatedLoads.gaussian_cdf_pos (c*x)
  unfold logSlope foldedKernel inverseMills
  have hF' : (Φ (x*c)) ≠ 0 := by simpa only [mul_comm] using hF.ne'
  field_simp [hF.ne',hF',hω.ne']

lemma integrable_logSlope_mul {ω c : ℝ} (hω : 0 < ω) :
    Integrable (fun x => logSlope ω c x*foldedKernel ω c x) := by
  let D : ℝ → ℝ := fun x => (2/ω^3)*|x| *φ (x/ω)+
    ((2/ω)*|c| *φ 0)*φ (x/ω)
  have hD : Integrable D := by
    convert! ((scaled_mul_normalPDF_integrable hω).const_mul (2/ω^3)).add
      ((scaled_normalPDF_integrable hω).const_mul ((2/ω)*|c| *φ 0)) using 1
    funext x
    simp only [D,Pi.add_apply]
    ring
  apply Integrable.mono' hD ?_ ?_
  · simp_rw [logSlope_mul_identity hω]
    apply AEStronglyMeasurable.add
    · exact (measurable_id.neg.div_const _).aestronglyMeasurable.mul
        (integrable_foldedKernel hω).aestronglyMeasurable
    · fun_prop
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,logSlope_mul_identity hω]
    apply (abs_add_le _ _).trans
    have hfirst := mul_le_mul_of_nonneg_left (foldedKernel_le (c := c) hω x)
      (div_nonneg (abs_nonneg x) (sq_nonneg ω))
    have hsecond := mul_le_mul_of_nonneg_left (normalPDF_le_at_zero (c*x))
      (show (0:ℝ) ≤ (2/ω)*|c| *φ (x/ω) from
        mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hω.le) (abs_nonneg c))
          (gaussianPDFReal_nonneg 0 1 (x/ω)))
    rw [abs_mul,abs_div,abs_neg,abs_pow,abs_of_pos hω,
      abs_of_pos (foldedKernel_pos hω x),abs_mul,abs_mul,abs_mul,
      abs_of_pos (by positivity : (0 : ℝ)<2/ω),
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    dsimp only [D]
    have he : |x| /ω^2*((2/ω)*φ (x/ω))=(2/ω^3)*|x| *φ (x/ω) := by
      field_simp [hω.ne']
    rw [he] at hfirst
    nlinarith

lemma logSlope_antitone {ω c : ℝ} (_hω : 0 < ω) (hc : 0 ≤ c) :
    Antitone (logSlope ω c) := by
  intro x y hxy
  dsimp only [logSlope]
  exact add_le_add
    (div_le_div_of_nonneg_right (neg_le_neg hxy) (sq_nonneg ω))
    (mul_le_mul_of_nonneg_left
      (inverseMills_strictAnti.antitone (mul_le_mul_of_nonneg_left hxy hc)) hc)

lemma foldedKernel_tendsto_atBot {ω c : ℝ} (hω : 0 < ω) :
    Tendsto (foldedKernel ω c) atBot (𝓝 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => hasDerivAt_foldedKernel hω x)
    (integrable_logSlope_mul hω).integrableOn (integrable_foldedKernel hω).integrableOn

theorem actual_reverse_hazard_antitone {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Antitone (fun s =>
      foldedKernel (totalScale a b) (b/(a*totalScale a b)) s /
        cdf (EntryGaussianLaw.law a b) s) := by
  have hω := totalScale_pos ha b
  have hc : 0 ≤ b/(a*totalScale a b) := div_nonneg hb (mul_pos ha hω).le
  exact EntryHazard.reverse_hazard_antitone _ _ _
    (foldedKernel_pos hω) (EntryGaussianLaw.cdf_pos ha b)
    (hasDerivAt_foldedKernel hω) (hasDerivAt_actual_cdf_explicit ha b)
    (integrable_foldedKernel hω) (integrable_logSlope_mul hω)
    (foldedKernel_tendsto_atBot hω) (tendsto_cdf_atBot _)
    (logSlope_antitone hω hc)

theorem actual_positive_shortfall_survival_submul {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (z : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cdf (EntryGaussianLaw.law a b) (z-(x+y))/cdf (EntryGaussianLaw.law a b) z ≤
      (cdf (EntryGaussianLaw.law a b) (z-x)/cdf (EntryGaussianLaw.law a b) z)*
      (cdf (EntryGaussianLaw.law a b) (z-y)/cdf (EntryGaussianLaw.law a b) z) :=
  EntryHazard.conditional_shortfall_survival_submul _ _
    (EntryGaussianLaw.cdf_pos ha b) (hasDerivAt_actual_cdf_explicit ha b)
    (actual_reverse_hazard_antitone ha hb) z hx hy

end FCAppendix.Affine.Uniform06.EntryConvolution
