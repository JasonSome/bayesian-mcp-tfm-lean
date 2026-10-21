import FCAppendix.Affine.Uniform07.SourceLaw
import Mathlib.Probability.Moments.SubGaussian

namespace FCAppendix.Affine.Uniform07
open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

theorem centered_mgf_under_tilt (mu : Measure Ω) (X : Ω→ℝ)
    (theta s r : ℝ) :
    mgf (fun w => X w-r) (mu.tilted (fun w => -theta*X w)) s =
      Real.exp (-s*r)/mgf X mu (-theta)*mgf X mu (s-theta) := by
  unfold mgf
  rw [integral_tilted_mul_eq_mgf]
  have he (w : Ω) :
      (Real.exp (-theta*X w)/(∫ z,Real.exp (-theta*X z)∂mu))*
        Real.exp (s*(X w-r)) =
      (Real.exp (-s*r)/(∫ z,Real.exp (-theta*X z)∂mu))*
        Real.exp ((s-theta)*X w) := by
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,← Real.exp_add,← Real.exp_add]
    congr 2
    ring
  simp only [mgf, smul_eq_mul]
  simp_rw [he]
  rw [integral_const_mul]

theorem centered_cgf_le_eighth (nu : Measure Ω) [IsProbabilityMeasure nu]
    (X : Ω→ℝ) (hX : AEMeasurable X nu)
    (hb : ∀ᵐ w∂nu,X w∈Icc 0 1) {r s : ℝ} (hmean : (∫ w,X w∂nu)=r) :
    cgf (fun w => X w-r) nu s≤s^2/8 := by
  have h := hasSubgaussianMGF_of_mem_Icc hX hb
  rw [hmean] at h
  have hh := h.cgf_le s
  norm_num at hh
  nlinarith [hh]

theorem objective_difference_as_cgf (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω→ℝ) (hX : AEMeasurable X mu)
    (hb : ∀ᵐ w∂mu,X w∈Icc 0 1) (theta mid r : ℝ) :
    (-theta*r-cgf X mu (-theta))-(-mid*r-cgf X mu (-mid)) =
      cgf (fun w => X w-r) (mu.tilted (fun w => -theta*X w)) (theta-mid) := by
  have hint (s : ℝ) := integrable_exp_mul_of_mem_Icc hX hb (t := s)
  have hpos (s : ℝ) : 0<mgf X mu s := mgf_pos (hint s)
  unfold cgf
  rw [centered_mgf_under_tilt]
  have hid : theta-mid-theta=-mid := by ring
  rw [hid,Real.log_mul (div_ne_zero (Real.exp_ne_zero _) (hpos _).ne') (hpos _).ne',
    Real.log_div (Real.exp_ne_zero _) (hpos _).ne',Real.log_exp]
  ring

theorem tilt_bracket_allowance (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω→ℝ) (hX : AEMeasurable X mu)
    (hb : ∀ᵐ w∂mu,X w∈Icc 0 1) {theta lo hi r : ℝ}
    (hlo : lo≤theta) (hhi : theta≤hi)
    (hmean : (∫ w,X w∂mu.tilted (fun w => -theta*X w))=r) :
    (-theta*r-cgf X mu (-theta)) ≤
      (-((lo+hi)/2)*r-cgf X mu (-((lo+hi)/2)))+((hi-lo)/2)^2/8 := by
  have hint := integrable_exp_mul_of_mem_Icc hX hb (t := -theta)
  let nu := mu.tilted (fun w => -theta*X w)
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hint
  have hac := tilted_absolutelyContinuous mu (fun w => -theta*X w)
  have hsub := centered_cgf_le_eighth nu X (hX.mono_ac hac) (hac hb) hmean
    (s := theta-(lo+hi)/2)
  rw [← objective_difference_as_cgf mu X hX hb theta ((lo+hi)/2) r] at hsub
  have hsquare : (theta-(lo+hi)/2)^2≤((hi-lo)/2)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  linarith

theorem first_allowance_exact :
    (((2585/100000:ℝ)-(2584/100000))/2)^2/8=3125/10^15 := by norm_num

theorem second_allowance_exact :
    (((2844/100000:ℝ)-(2842/100000))/2)^2/8=125/10^13 := by norm_num

theorem centered_cgf_nonneg (nu : Measure Ω) [IsProbabilityMeasure nu]
    (X : Ω → ℝ) (hX : AEMeasurable X nu)
    (hb : ∀ᵐ w ∂nu, X w ∈ Icc (0:ℝ) 1) {r s : ℝ}
    (hmean : (∫ w, X w ∂nu)=r) :
    0 ≤ cgf (fun w => X w-r) nu s := by
  have hiX : Integrable X nu := Integrable.of_mem_Icc 0 1 hX hb
  have hiY : Integrable (fun w => X w-r) nu := hiX.sub (integrable_const r)
  have hY : ∀ᵐ w ∂nu, X w-r ∈ Icc (-r) (1-r) := by
    filter_upwards [hb] with w hw
    constructor <;> linarith [hw.1,hw.2]
  have hiE : Integrable (fun w => Real.exp (s*(X w-r))) nu :=
    integrable_exp_mul_of_mem_Icc (hX.sub_const r) hY
  have hymean : (∫ w, X w-r ∂nu)=0 := by
    rw [integral_sub hiX (integrable_const r),hmean]
    simp
  have hiL : Integrable (fun w => (1:ℝ)+s*(X w-r)) nu :=
    (integrable_const 1).add (hiY.const_mul s)
  have hlinear : (∫ w, (1:ℝ)+s*(X w-r) ∂nu) ≤
      ∫ w, Real.exp (s*(X w-r)) ∂nu := by
    exact integral_mono hiL hiE (fun w => by
      simpa only [add_comm] using Real.add_one_le_exp (s*(X w-r)))
  have hone : (∫ w, (1:ℝ)+s*(X w-r) ∂nu)=1 := by
    rw [integral_add (integrable_const 1) (hiY.const_mul s), integral_const_mul, hymean]
    simp
  rw [hone] at hlinear
  exact Real.log_nonneg hlinear

theorem root_tilt_global_max (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ) (hX : AEMeasurable X mu)
    (hb : ∀ᵐ w ∂mu, X w ∈ Icc (0:ℝ) 1) {r theta : ℝ}
    (hmean : (∫ w, X w ∂mu.tilted (fun w => -theta*X w))=r) (s : ℝ) :
    -s*r-cgf X mu (-s) ≤ -theta*r-cgf X mu (-theta) := by
  have hint := integrable_exp_mul_of_mem_Icc hX hb (t := -theta)
  let nu := mu.tilted (fun w => -theta*X w)
  letI : IsProbabilityMeasure nu := isProbabilityMeasure_tilted hint
  have hac := tilted_absolutelyContinuous mu (fun w => -theta*X w)
  have hpos := centered_cgf_nonneg nu X (hX.mono_ac hac) (hac.ae_le hb) hmean
    (s := theta-s)
  rw [← objective_difference_as_cgf mu X hX hb theta s r] at hpos
  linarith

end FCAppendix.Affine.Uniform07
