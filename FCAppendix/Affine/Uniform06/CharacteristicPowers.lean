import FCAppendix.Affine.Uniform06.CharacteristicExpansion
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

namespace FCAppendix.Affine.Uniform06.CharacteristicPowers

open MeasureTheory Filter
open scoped Topology
open CharacteristicExpansion

variable {Ω : Type*} [MeasurableSpace Ω]

lemma norm_rowCharacteristic_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) : ‖rowCharacteristic μ Z‖ ≤ 1 := by
  calc
    ‖rowCharacteristic μ Z‖ ≤ ∫ ω, ‖phase (Z ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = 1 := by simp

theorem norm_pow_sub_pow_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (N : ℕ) : ‖a ^ N - b ^ N‖ ≤ (N : ℝ) * ‖a - b‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hbpow : ‖b ^ N‖ ≤ 1 := by
        rw [norm_pow]
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg b) hb N
      have hsplit : a ^ (N + 1) - b ^ (N + 1) =
          (a ^ N - b ^ N) * a + b ^ N * (a - b) := by
        rw [pow_succ, pow_succ]
        ring
      rw [hsplit]
      calc
        ‖(a ^ N - b ^ N) * a + b ^ N * (a - b)‖ ≤
            ‖a ^ N - b ^ N‖ * ‖a‖ + ‖b ^ N‖ * ‖a - b‖ := by
          simpa only [norm_mul] using
            norm_add_le ((a ^ N - b ^ N) * a) (b ^ N * (a - b))
        _ ≤ ((N : ℝ) * ‖a - b‖) * 1 + 1 * ‖a - b‖ := by
          exact add_le_add
            (mul_le_mul ih ha (norm_nonneg a)
              (mul_nonneg (Nat.cast_nonneg N) (norm_nonneg _)))
            (mul_le_mul_of_nonneg_right hbpow (norm_nonneg _))
        _ = ((N + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

theorem characteristic_pow_gaussian_error (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ 1)
    (hmean : ∫ ω, Z ω ∂μ = 0) (N : ℕ) :
    ‖rowCharacteristic μ Z ^ N -
      Complex.exp (-((N : ℝ) * (∫ ω, Z ω ^ 2 ∂μ) : ℝ) / 2)‖ ≤
      (N : ℝ) * ((∫ ω, |Z ω| ^ 3 ∂μ) +
        ((∫ ω, Z ω ^ 2 ∂μ) / 2) ^ 2) := by
  let q : ℝ := ∫ ω, Z ω ^ 2 ∂μ
  let z : ℂ := -(q : ℂ) / 2
  let g : ℂ := Complex.exp z
  have hq0 : 0 ≤ q := integral_nonneg fun ω => sq_nonneg (Z ω)
  have hq1 : q ≤ 1 := by
    simpa only [one_pow] using second_moment_le_bound_sq μ hZ hbound
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0]
    norm_num
    linarith
  have hg : ‖g‖ ≤ 1 := by
    have hgval : g = (Real.exp (-q / 2) : ℂ) := by
      dsimp [g, z]
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hgval, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hz_norm : ‖z‖ ^ 2 = (q / 2) ^ 2 := by
    dsimp [z]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0]
    norm_num
  have hexp := Complex.norm_exp_sub_one_sub_id_le hz
  have hexp' : ‖g - ((1 : ℂ) - (q : ℂ) / 2)‖ ≤ (q / 2) ^ 2 := by
    have hid : Complex.exp z - 1 - z = g - ((1 : ℂ) - (q : ℂ) / 2) := by
      dsimp [g, z]
      ring
    rwa [hid, hz_norm] at hexp
  have hrow := bounded_characteristic_expansion μ hZ hbound
  rw [hmean] at hrow
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hrow
  have hsingle : ‖rowCharacteristic μ Z - g‖ ≤
      (∫ ω, |Z ω| ^ 3 ∂μ) + (q / 2) ^ 2 := by
    calc
      ‖rowCharacteristic μ Z - g‖ ≤
          ‖rowCharacteristic μ Z - ((1 : ℂ) - (q : ℂ) / 2)‖ +
          ‖((1 : ℂ) - (q : ℂ) / 2) - g‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (∫ ω, |Z ω| ^ 3 ∂μ) + (q / 2) ^ 2 := by
        rw [norm_sub_rev ((1 : ℂ) - (q : ℂ) / 2) g]
        exact add_le_add hrow hexp'
  have hgn : g ^ N =
      Complex.exp (-((N : ℝ) * q : ℝ) / 2) := by
    dsimp [g, z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← hgn]
  exact (norm_pow_sub_pow_le _ _ (norm_rowCharacteristic_le_one μ Z) hg N).trans
    (mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg N))

theorem tendsto_triangular_characteristic_powers
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (Z : ℕ → Ω → ℝ) (N : ℕ → ℕ) (r : ℕ → ℝ)
    (hZ : ∀ n, Measurable (Z n))
    (hbound : ∀ n, ∀ᵐ ω ∂μ n, |Z n ω| ≤ r n)
    (hmean : ∀ n, ∫ ω, Z n ω ∂μ n = 0)
    (hr : Tendsto r atTop (𝓝 0)) {q : ℝ}
    (hvar : Tendsto (fun n => (N n : ℝ) * ∫ ω, Z n ω ^ 2 ∂μ n)
      atTop (𝓝 q)) :
    Tendsto (fun n => rowCharacteristic (μ n) (Z n) ^ N n)
      atTop (𝓝 (Complex.exp (-(q : ℂ) / 2))) := by
  let v : ℕ → ℝ := fun n => ∫ ω, Z n ω ^ 2 ∂μ n
  have hv0 : ∀ n, 0 ≤ v n := fun n =>
    integral_nonneg fun ω => sq_nonneg (Z n ω)
  have hv : Tendsto v atTop (𝓝 0) := by
    apply squeeze_zero hv0
      (fun n => second_moment_le_bound_sq (μ n) (hZ n) (hbound n))
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hr.pow 2
  let e : ℕ → ℝ := fun n =>
    r n * ((N n : ℝ) * v n) + ((N n : ℝ) * v n) * v n / 4
  have he : Tendsto e atTop (𝓝 0) := by
    have h := (hr.mul hvar).add ((hvar.mul hv).div_const 4)
    simpa only [zero_mul, mul_zero, zero_div, add_zero] using h
  have hr1 : ∀ᶠ n in atTop, r n ≤ 1 := by
    have h := hr.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact h.mono fun n hn => le_of_lt hn
  have herror : ∀ᶠ n in atTop,
      ‖rowCharacteristic (μ n) (Z n) ^ N n -
        Complex.exp (-((N n : ℝ) * v n : ℝ) / 2)‖ ≤ e n := by
    filter_upwards [hr1] with n hn
    have hbn : ∀ᵐ ω ∂μ n, |Z n ω| ≤ 1 :=
      (hbound n).mono fun ω hω => hω.trans hn
    have hfinite := characteristic_pow_gaussian_error (μ n) (hZ n) hbn
      (hmean n) (N n)
    have hthird := third_moment_le_bound_mul_second (μ n) (hZ n) (hbound n)
    calc
      ‖rowCharacteristic (μ n) (Z n) ^ N n -
          Complex.exp (-((N n : ℝ) * v n : ℝ) / 2)‖ ≤
          (N n : ℝ) * ((∫ ω, |Z n ω| ^ 3 ∂μ n) + (v n / 2) ^ 2) := hfinite
      _ ≤ (N n : ℝ) * (r n * v n + (v n / 2) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (N n))
        change (∫ ω, |Z n ω| ^ 3 ∂μ n) ≤ r n*v n at hthird
        linarith
      _ = e n := by dsimp [e]; ring
  have hdiff : Tendsto (fun n =>
      ‖rowCharacteristic (μ n) (Z n) ^ N n -
        Complex.exp (-((N n : ℝ) * v n : ℝ) / 2)‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) herror he
  have hexp : Tendsto (fun n => Complex.exp (-((N n : ℝ) * v n : ℝ) / 2))
      atTop (𝓝 (Complex.exp (-(q : ℂ) / 2))) := by
    exact (((Complex.continuous_ofReal.tendsto q).comp hvar).neg.div_const 2).cexp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := hdiff.add (tendsto_iff_norm_sub_tendsto_zero.mp hexp)
  refine squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_sub_le_norm_sub_add_norm_sub _
      (Complex.exp (-((N n : ℝ)*v n : ℝ)/2)) _) ?_
  simpa only [zero_add] using hlim

end FCAppendix.Affine.Uniform06.CharacteristicPowers
