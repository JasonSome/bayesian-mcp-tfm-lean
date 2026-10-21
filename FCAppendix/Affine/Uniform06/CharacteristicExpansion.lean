import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Tactic

noncomputable section

namespace FCAppendix.Affine.Uniform06.CharacteristicExpansion

open MeasureTheory Filter
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def phase (z : ℝ) : ℂ := Complex.exp ((z : ℂ) * Complex.I)

def rowCharacteristic (μ : Measure Ω) (Z : Ω → ℝ) : ℂ :=
  ∫ ω, phase (Z ω) ∂μ

lemma continuous_phase : Continuous phase :=
  Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const)

@[simp] lemma norm_phase (z : ℝ) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma integrable_phase (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) :
    Integrable (fun ω => phase (Z ω)) μ := by
  exact Integrable.of_bound
    (continuous_phase.measurable.comp hZ).aestronglyMeasurable 1
    (ae_of_all _ fun ω => (norm_phase (Z ω)).le)

lemma integrable_pow_of_abs_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) (n : ℕ) :
    Integrable (fun ω => Z ω ^ n) μ := by
  apply Integrable.of_bound (hZ.pow_const n).aestronglyMeasurable (r ^ n)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg (Z ω)) hω n

lemma integrable_abs_pow_of_abs_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) (n : ℕ) :
    Integrable (fun ω => |Z ω| ^ n) μ := by
  simpa only [abs_pow] using
    (integrable_pow_of_abs_le μ hZ hbound n).abs

lemma integrable_complex_pow_of_abs_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) (n : ℕ) :
    Integrable (fun ω => ((Z ω ^ n : ℝ) : ℂ)) μ := by
  apply Integrable.of_bound
    (Complex.continuous_ofReal.measurable.comp (hZ.pow_const n)).aestronglyMeasurable
    (r ^ n)
  filter_upwards [hbound] with ω hω
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg (Z ω)) hω n

theorem phase_taylor_three {z : ℝ} (hz : |z| ≤ 1) :
    ‖phase z - (1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2)‖ ≤ |z| ^ 3 := by
  have hn : ‖(z : ℂ) * Complex.I‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one] using hz
  have h := Complex.exp_bound hn (n := 3) (by decide)
  have hpoly :
      (∑ m ∈ Finset.range 3,
        ((z : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial, mul_pow, Complex.I_sq]; ring
  rw [hpoly] at h
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] at h
  norm_num [Nat.factorial] at h
  change ‖Complex.exp ((z : ℂ) * Complex.I) -
    (1 + (z : ℂ) * Complex.I - (z : ℂ) ^ 2 / 2)‖ ≤ _
  nlinarith [pow_nonneg (abs_nonneg z) 3]

lemma integral_phase_polynomial (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) :
    (∫ ω, (1 + (Z ω : ℂ) * Complex.I - (Z ω : ℂ) ^ 2 / 2) ∂μ) =
      1 + Complex.ofReal (∫ ω, Z ω ∂μ) * Complex.I -
        Complex.ofReal (∫ ω, Z ω ^ 2 ∂μ) / 2 := by
  have h1 : Integrable (fun ω => (Z ω : ℂ)) μ := by
    simpa only [pow_one] using
      integrable_complex_pow_of_abs_le μ hZ hbound 1
  have h2 : Integrable (fun ω => (Z ω : ℂ) ^ 2) μ := by
    simpa only [Complex.ofReal_pow] using
      integrable_complex_pow_of_abs_le μ hZ hbound 2
  have hsub := integral_sub ((integrable_const (1 : ℂ) (μ := μ)).add
    (h1.mul_const Complex.I)) (h2.div_const (2 : ℂ))
  have hadd := integral_add (integrable_const (1 : ℂ) (μ := μ))
    (h1.mul_const Complex.I)
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_mul_const, integral_div]
  simp only [integral_const, probReal_univ, one_smul]
  have hcast2 : (∫ ω, (Z ω : ℂ) ^ 2 ∂μ) =
      Complex.ofReal (∫ ω, Z ω ^ 2 ∂μ) := by
    convert! (integral_complex_ofReal (μ := μ) (f := fun ω => Z ω ^ 2)) using 1
    congr 1
    funext ω
    exact (Complex.ofReal_pow (Z ω) 2).symm
  rw [integral_complex_ofReal, hcast2]

theorem bounded_characteristic_expansion (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ 1) :
    ‖rowCharacteristic μ Z -
      (1 + Complex.ofReal (∫ ω, Z ω ∂μ) * Complex.I -
        Complex.ofReal (∫ ω, Z ω ^ 2 ∂μ) / 2)‖ ≤
      ∫ ω, |Z ω| ^ 3 ∂μ := by
  let P : Ω → ℂ := fun ω =>
    1 + (Z ω : ℂ) * Complex.I - (Z ω : ℂ) ^ 2 / 2
  have h1 : Integrable (fun ω => (Z ω : ℂ)) μ := by
    simpa only [pow_one] using
      integrable_complex_pow_of_abs_le μ hZ hbound 1
  have h2 : Integrable (fun ω => (Z ω : ℂ) ^ 2) μ := by
    simpa only [Complex.ofReal_pow] using
      integrable_complex_pow_of_abs_le μ hZ hbound 2
  have hP : Integrable P μ :=
    ((integrable_const (1 : ℂ)).add (h1.mul_const _)).sub (h2.div_const _)
  have hdiff : Integrable (fun ω => phase (Z ω) - P ω) μ :=
    (integrable_phase μ hZ).sub hP
  calc
    ‖rowCharacteristic μ Z -
        (1 + Complex.ofReal (∫ ω, Z ω ∂μ) * Complex.I -
          Complex.ofReal (∫ ω, Z ω ^ 2 ∂μ) / 2)‖ =
        ‖∫ ω, phase (Z ω) - P ω ∂μ‖ := by
      rw [integral_sub (integrable_phase μ hZ) hP]
      rw [show (∫ ω, P ω ∂μ) = _ from
        integral_phase_polynomial μ hZ hbound]
      rfl
    _ ≤ ∫ ω, ‖phase (Z ω) - P ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |Z ω| ^ 3 ∂μ := by
      apply integral_mono_ae hdiff.norm
        (integrable_abs_pow_of_abs_le μ hZ hbound 3)
      filter_upwards [hbound] with ω hω
      exact phase_taylor_three hω

lemma third_moment_le_bound_mul_second (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) :
    (∫ ω, |Z ω| ^ 3 ∂μ) ≤ r * ∫ ω, Z ω ^ 2 ∂μ := by
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_abs_pow_of_abs_le μ hZ hbound 3)
    ((integrable_pow_of_abs_le μ hZ hbound 2).const_mul r)
  filter_upwards [hbound] with ω hω
  calc
    |Z ω| ^ 3 = |Z ω| * Z ω ^ 2 := by rw [pow_succ, sq_abs]; ring
    _ ≤ r * Z ω ^ 2 := mul_le_mul_of_nonneg_right hω (sq_nonneg _)

lemma second_moment_le_bound_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {r : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ r) :
    (∫ ω, Z ω ^ 2 ∂μ) ≤ r ^ 2 := by
  calc
    (∫ ω, Z ω ^ 2 ∂μ) ≤ ∫ _ : Ω, r ^ 2 ∂μ := by
      apply integral_mono_ae (integrable_pow_of_abs_le μ hZ hbound 2)
        (integrable_const _)
      filter_upwards [hbound] with ω hω
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
    _ = r ^ 2 := by simp

theorem centered_characteristic_norm_le_exp (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ (1 : ℝ) / 4)
    (hmean : ∫ ω, Z ω ∂μ = 0) :
    ‖rowCharacteristic μ Z‖ ≤
      Real.exp (-(∫ ω, Z ω ^ 2 ∂μ) / 4) := by
  let q : ℝ := ∫ ω, Z ω ^ 2 ∂μ
  have hq0 : 0 ≤ q := integral_nonneg fun ω => sq_nonneg (Z ω)
  have hq1 : q ≤ (1 : ℝ) / 16 := by
    have h := second_moment_le_bound_sq μ hZ hbound
    norm_num at h
    exact h
  have hbound1 : ∀ᵐ ω ∂μ, |Z ω| ≤ 1 :=
    hbound.mono fun ω hω => hω.trans (by norm_num)
  have he := bounded_characteristic_expansion μ hZ hbound1
  rw [hmean] at he
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at he
  have h3 := third_moment_le_bound_mul_second μ hZ hbound
  have hpoly : ‖(1 : ℂ) - (q : ℂ) / 2‖ = 1 - q / 2 := by
    rw [show (1 : ℂ) - (q : ℂ) / 2 = ((1 - q / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have htriangle := norm_add_le
    (rowCharacteristic μ Z - ((1 : ℂ) - (q : ℂ) / 2))
    ((1 : ℂ) - (q : ℂ) / 2)
  rw [sub_add_cancel, hpoly] at htriangle
  have hlin : ‖rowCharacteristic μ Z‖ ≤ 1 - q / 4 := by
    change ‖rowCharacteristic μ Z - ((1 : ℂ) - (q : ℂ) / 2)‖ ≤ _ at he
    change (∫ ω, |Z ω| ^ 3 ∂μ) ≤ (1 : ℝ) / 4 * q at h3
    linarith
  calc
    ‖rowCharacteristic μ Z‖ ≤ 1 - q / 4 := hlin
    _ ≤ Real.exp (-q / 4) := by
      simpa only [neg_div] using Real.one_sub_le_exp_neg (q / 4)

theorem centered_characteristic_pow_norm_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ (1 : ℝ) / 4)
    (hmean : ∫ ω, Z ω ∂μ = 0) (N : ℕ) :
    ‖rowCharacteristic μ Z ^ N‖ ≤
      Real.exp (-(N : ℝ) * (∫ ω, Z ω ^ 2 ∂μ) / 4) := by
  rw [norm_pow]
  calc
    ‖rowCharacteristic μ Z‖ ^ N ≤
        (Real.exp (-(∫ ω, Z ω ^ 2 ∂μ) / 4)) ^ N :=
      pow_le_pow_left₀ (norm_nonneg _)
        (centered_characteristic_norm_le_exp μ hZ hbound hmean) N
    _ = Real.exp (-(N : ℝ) * (∫ ω, Z ω ^ 2 ∂μ) / 4) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem rowCharacteristic_eq_charFun_map_one (μ : Measure Ω)
    {Z : Ω → ℝ} (hZ : Measurable Z) :
    rowCharacteristic μ Z = charFun (μ.map Z) 1 := by
  rw [charFun_apply_real]
  simp only [Complex.ofReal_one, one_mul]
  have h := integral_map (μ := μ) hZ.aemeasurable continuous_phase.aestronglyMeasurable
  convert! h.symm using 1

end FCAppendix.Affine.Uniform06.CharacteristicExpansion
