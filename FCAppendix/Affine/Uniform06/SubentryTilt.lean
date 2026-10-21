import FCAppendix.Probability.MeanZeroTilt
import Mathlib

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SubentryTilt

open MeasureTheory ProbabilityTheory Set Filter
open FCAppendix.ExponentialTilt

variable {Ω : Type*} [MeasurableSpace Ω]

def mean (μ : Measure Ω) (X : Ω → ℝ) (θ : ℝ) : ℝ :=
  ∫ ω, X ω ∂μ.tilted (fun ω => -θ*X ω)

theorem continuous_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) : Continuous (mean μ X) := by
  have hc : Continuous (fun u : ℝ => ∫ ω, X ω ∂μ.tilted (fun ω => u*X ω)) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasDerivAt_tilted_mean μ hX hb u).continuousAt
  exact hc.comp continuous_neg

theorem mean_zero (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} :
    mean μ X 0 = ∫ ω, X ω ∂μ := by
  simp [mean]

theorem integral_weighted_unit (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) (θ : ℝ) :
    Integrable (fun ω => X ω*Real.exp (-θ*X ω)) μ := by
  apply (integrable_const (Real.exp |θ|)).mono' (by fun_prop)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω.1,
    abs_of_pos (Real.exp_pos _)]
  have harg : -θ*X ω ≤ |θ| := by
    have hmul : |θ| *X ω ≤ |θ| := by
      simpa using mul_le_mul_of_nonneg_left hω.2 (abs_nonneg θ)
    have hneg : -θ ≤ |θ| := neg_le_abs θ
    exact (mul_le_mul_of_nonneg_right hneg hω.1).trans hmul
  exact (mul_le_mul_of_nonneg_right hω.2 (Real.exp_pos _).le).trans
    (by simpa using Real.exp_le_exp.mpr harg)

theorem mean_eq_ratio (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) (θ : ℝ) :
    mean μ X θ = (∫ ω, X ω*Real.exp (-θ*X ω) ∂μ)/mgf X μ (-θ) := by
  have he := integrable_exp_mul_of_bounded μ hX.aemeasurable hb (-θ)
  rw [mean, integral_tilted_mul_eq_cgf _ he]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [Real.exp_sub, exp_cgf he]
  simp [smul_eq_mul, mul_div_assoc, mul_comm]

theorem weighted_unit_upper {θ x : ℝ} (hθ : 0 < θ) (_hx : 0 ≤ x) :
    x*Real.exp (-θ*x) ≤ 1/θ := by
  have hex := Real.add_one_le_exp (θ*x)
  have he : θ*x ≤ Real.exp (θ*x) := by linarith
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-θ*x)).le
  have hid : Real.exp (θ*x)*Real.exp (-θ*x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hid] at hm
  apply (le_div_iff₀ hθ).mpr
  nlinarith

theorem mgf_ge_zero_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1) (θ : ℝ) :
    μ.real {ω | X ω=0} ≤ mgf X μ (-θ) := by
  have hs : MeasurableSet {ω | X ω=0} := hX (measurableSet_singleton 0)
  have hi := (integrable_const (μ := μ) (1:ℝ)).indicator hs
  have he := integrable_exp_mul_of_bounded μ hX.aemeasurable hb (-θ)
  have h := integral_mono_ae hi he (Filter.Eventually.of_forall fun ω => by
    by_cases hz : X ω=0
    · simp [Set.indicator, hz]
    · simp only [Set.indicator_of_notMem (show ω ∉ {ω | X ω=0} from hz)]
      positivity)
  have heq : (∫ ω, ({ω | X ω=0}.indicator (fun _ => (1:ℝ))) ω ∂μ) =
      μ.real {ω | X ω=0} := by
    convert! integral_indicator_one (μ := μ) hs using 1
  rw [heq] at h
  exact h

theorem mean_upper_from_zero_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)
    {z θ : ℝ} (hz : 0 < z) (hzero : z ≤ μ.real {ω | X ω=0})
    (hθ : 0 < θ) : mean μ X θ ≤ 1/(θ*z) := by
  have hZ : z ≤ mgf X μ (-θ) := hzero.trans (mgf_ge_zero_mass μ hX hb θ)
  have hZ0 := hz.trans_le hZ
  have hnum : (∫ ω, X ω*Real.exp (-θ*X ω) ∂μ) ≤ 1/θ := by
    have hi := integral_mono_ae (integral_weighted_unit μ hX hb θ)
      (integrable_const (1/θ:ℝ)) (hb.mono fun _ hω => weighted_unit_upper hθ hω.1)
    simpa using hi
  rw [mean_eq_ratio μ hX hb θ]
  calc
    _ ≤ (1/θ)/mgf X μ (-θ) := div_le_div_of_nonneg_right hnum hZ0.le
    _ ≤ (1/θ)/z := div_le_div_of_nonneg_left (by positivity) hz hZ
    _ = _ := by field_simp

theorem exists_matching_tilt (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)
    {r z : ℝ} (hr : 0 < r) (hz : 0 < z)
    (hzero : z ≤ μ.real {ω | X ω=0})
    (hmean : r < ∫ ω, X ω ∂μ) :
    ∃ θ ∈ Ioo (0:ℝ) (2/(r*z)), mean μ X θ = r := by
  let T : ℝ := 2/(r*z)
  have hT : 0 < T := by dsimp [T]; positivity
  have hupper := mean_upper_from_zero_mass μ hX hb hz hzero hT
  have hratio : 1/(T*z)=r/2 := by
    dsimp [T]
    field_simp [hr.ne',hz.ne']
  rw [hratio] at hupper
  have hbelow : mean μ X T < r := by linarith
  have habove : r < mean μ X 0 := by simpa [mean_zero] using hmean
  obtain ⟨θ,hθ,hmatch⟩ := intermediate_value_Icc' hT.le
    (continuous_mean μ hX hb).continuousOn ⟨hbelow.le,habove.le⟩
  have hθ0 : θ ≠ 0 := by intro h; subst θ; linarith
  have hθT : θ ≠ T := by intro h; subst θ; linarith
  exact ⟨θ,⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0),
    lt_of_le_of_ne hθ.2 hθT⟩,hmatch⟩

theorem matching_tilt_unique (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (0:ℝ) 1)
    (hv : 0 < variance X μ) {θ₁ θ₂ r : ℝ}
    (h₁ : mean μ X θ₁=r) (h₂ : mean μ X θ₂=r) : θ₁=θ₂ := by
  have hder (θ : ℝ) : HasDerivAt (mean μ X)
      (-variance X (μ.tilted (fun ω => -θ*X ω))) θ := by
    convert! (hasDerivAt_tilted_mean μ hX hb (-θ)).comp θ
      (hasDerivAt_neg θ) using 1
    simp
  have hpos (θ : ℝ) : 0 < variance X (μ.tilted (fun ω => -θ*X ω)) :=
    (mul_pos (Real.exp_pos _) hv).trans_le
      (tilted_variance_bounds μ hX hb (show |(-θ)| ≤ |θ| by simp)).1
  have hanti : StrictAnti (mean μ X) :=
    strictAnti_of_hasDerivAt_neg hder (fun θ => by have h := hpos θ; linarith)
  exact hanti.injective (h₁.trans h₂.symm)

end FCAppendix.Affine.Uniform06.SubentryTilt
