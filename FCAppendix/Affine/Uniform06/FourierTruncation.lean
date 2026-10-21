import FCAppendix.Affine.Uniform06.CharacteristicWeakConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

namespace FCAppendix.Affine.Uniform06.FourierTruncation

open MeasureTheory Filter Set
open scoped Topology

variable {A : Type*} [MeasurableSpace A]

theorem integral_amplitude_power_bound (ν : Measure A) [IsFiniteMeasure ν]
    {a φ : A → ℂ} (ha : Measurable a) (hφ : Measurable φ)
    {B r : ℝ} (hB : 0 ≤ B) (_hr : 0 ≤ r)
    (haB : ∀ᵐ x ∂ν, ‖a x‖ ≤ B) (hφr : ∀ᵐ x ∂ν, ‖φ x‖ ≤ r)
    (N : ℕ) :
    ‖∫ x, a x * φ x ^ N ∂ν‖ ≤ ν.real univ * (B * r ^ N) := by
  have hfB : ∀ᵐ x ∂ν, ‖a x * φ x ^ N‖ ≤ B * r ^ N := by
    filter_upwards [haB, hφr] with x hx hy
    rw [norm_mul, norm_pow]
    exact mul_le_mul hx (pow_le_pow_left₀ (norm_nonneg _) hy N)
      (pow_nonneg (norm_nonneg _) _) hB
  have hfi : Integrable (fun x => a x * φ x ^ N) ν :=
    Integrable.of_bound (ha.mul (hφ.pow_const N)).aestronglyMeasurable
      (B * r ^ N) hfB
  calc
    ‖∫ x, a x * φ x ^ N ∂ν‖ ≤ ∫ x, ‖a x * φ x ^ N‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : A, B * r ^ N ∂ν :=
      integral_mono_ae hfi.norm (integrable_const _) hfB
    _ = ν.real univ * (B * r ^ N) := by simp

theorem tendsto_market_scaled_compact_tail (ν : Measure A) [IsFiniteMeasure ν]
    (a φ : ℕ → A → ℂ) (N : ℕ → ℕ)
    (ha : ∀ n, Measurable (a n)) (hφ : ∀ n, Measurable (φ n))
    {B r : ℝ} (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (haB : ∀ n, ∀ᵐ x ∂ν, ‖a n x‖ ≤ B)
    (hgap : ∀ᶠ n in atTop, ∀ᵐ x ∂ν, ‖φ n x‖ ≤ r)
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => (N n : ℂ) * ∫ x, a n x * φ n x ^ N n ∂ν)
      atTop (𝓝 0) := by
  have hgeom : Tendsto (fun n => (N n : ℝ) * r ^ N n) atTop (𝓝 0) :=
    (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN
  have hbound : ∀ᶠ n in atTop,
      ‖(N n : ℂ) * ∫ x, a n x * φ n x ^ N n ∂ν‖ ≤
        (ν.real univ * B) * ((N n : ℝ) * r ^ N n) := by
    filter_upwards [hgap] with n hn
    rw [norm_mul, Complex.norm_natCast]
    calc
      (N n : ℝ) * ‖∫ x, a n x * φ n x ^ N n ∂ν‖ ≤
          (N n : ℝ) * (ν.real univ * (B * r ^ N n)) :=
        mul_le_mul_of_nonneg_left
          (integral_amplitude_power_bound ν (ha n) (hφ n) hB hr0 (haB n) hn (N n))
          (Nat.cast_nonneg _)
      _ = (ν.real univ * B) * ((N n : ℝ) * r ^ N n) := by ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hbound
  simpa only [mul_zero] using hgeom.const_mul (ν.real univ * B)

theorem integral_pair_scale (f : (ℝ × ℝ) → ℂ) (N : ℕ) {d : ℝ}
    (hscale : (N : ℝ) * d ^ 2 = 1) :
    (∫ q, f (d * q.1, d * q.2) ∂(volume.prod volume)) =
      (N : ℂ) * ∫ q, f q ∂(volume.prod volume) := by
  have hd2 : d ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hscale
    norm_num at hscale
  have hinv : (d ^ 2)⁻¹ = (N : ℝ) := by
    apply (mul_right_cancel₀ hd2)
    rw [inv_mul_cancel₀ hd2]
    exact hscale.symm
  have h := (volume.prod volume).integral_comp_smul f d
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hdim, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg d)), hinv] at h
  convert! h using 1

end FCAppendix.Affine.Uniform06.FourierTruncation
