import FCAppendix.Affine.Uniform06.CharacteristicExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedFourierInversion

open MeasureTheory Set
open scoped Topology
open CharacteristicExpansion

abbrev latticeMeasure : Measure ℝ := volume.restrict (Icc (-Real.pi) Real.pi)

abbrev frequencyMeasure : Measure (ℝ × ℝ) := volume.prod latticeMeasure

def inverseNormalization : ℂ := (2 * (Real.pi : ℂ))⁻¹

lemma inverseNormalization_ne_zero : inverseNormalization ≠ 0 := by
  unfold inverseNormalization
  exact inv_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))

lemma phase_add (u v : ℝ) : phase (u + v) = phase u * phase v := by
  simp [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma phase_zero : phase 0 = 1 := by simp [phase]

theorem integral_integer_phase (k : ℤ) :
    (∫ r, phase (r * (k : ℝ)) ∂latticeMeasure) =
      if k = 0 then 2 * (Real.pi : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]
  by_cases hk : k = 0
  · subst k
    simp [phase, two_mul]
  · rw [if_neg hk]
    let c : ℂ := (k : ℂ) * Complex.I
    have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have hphase : (fun r : ℝ => phase (r * (k : ℝ))) =
        fun r : ℝ => Complex.exp (c * (r : ℂ)) := by
      funext r
      dsimp [phase, c]
      congr 1
      push_cast
      ring
    rw [hphase, integral_exp_mul_complex hc]
    have hperiod : Complex.exp (c * (Real.pi : ℂ)) =
        Complex.exp (c * ((-Real.pi : ℝ) : ℂ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨k, ?_⟩
      dsimp [c]
      push_cast
      ring
    rw [hperiod, sub_self, zero_div]

theorem integer_projection (k y : ℤ) :
    inverseNormalization *
        (∫ r, phase (r * ((k - y : ℤ) : ℝ)) ∂latticeMeasure) =
      if k = y then (1 : ℂ) else 0 := by
  rw [integral_integer_phase]
  by_cases h : k = y
  · rw [sub_eq_zero.mpr h, if_pos rfl, if_pos h]
    exact inv_mul_cancel₀ (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero))
  · simp [h, sub_ne_zero.mpr h]

def inverseTest (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  inverseNormalization * ∫ s, g s * phase (s * x)

def mixedCharacteristic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω → ℝ) (Y : Ω → ℤ) (q : ℝ × ℝ) : ℂ :=
  ∫ ω, phase (q.1 * W ω + q.2 * (Y ω : ℝ)) ∂μ

lemma integrable_inverse_amplitude {g : ℝ → ℂ}
    (hg : Measurable g) (hgi : Integrable g) (x : ℝ) :
    Integrable (fun s => g s * phase (s * x)) := by
  apply hgi.norm.mono'
    ((hg.mul (continuous_phase.measurable.comp
      (measurable_id.mul measurable_const))).aestronglyMeasurable)
  exact ae_of_all _ fun s => by change ‖g s * phase (s*x)‖ ≤ ‖g s‖; rw [norm_mul, norm_phase, mul_one]

lemma norm_inverseTest_le {g : ℝ → ℂ} (x : ℝ) :
    ‖inverseTest g x‖ ≤ ‖inverseNormalization‖ * ∫ s, ‖g s‖ := by
  unfold inverseTest
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_mul, norm_phase, mul_one] using
    norm_integral_le_integral_norm (fun s => g s * phase (s * x))

lemma pointwise_mixed_inversion (g : ℝ → ℂ) (x : ℝ) (k y : ℤ) :
    inverseTest g x * (if k = y then (1 : ℂ) else 0) =
      inverseNormalization ^ 2 *
        ∫ q, g q.1 * phase (q.1 * x + q.2 * ((k - y : ℤ) : ℝ))
          ∂frequencyMeasure := by
  have hfactor : (fun q : ℝ × ℝ =>
      g q.1 * phase (q.1 * x + q.2 * ((k - y : ℤ) : ℝ))) =
      fun q => (g q.1 * phase (q.1 * x)) *
        phase (q.2 * ((k - y : ℤ) : ℝ)) := by
    funext q
    rw [phase_add]
    ring
  rw [hfactor]
  rw [integral_prod_mul (fun s : ℝ => g s * phase (s*x))
    (fun r : ℝ => phase (r * ((k-y : ℤ) : ℝ))), ← integer_projection k y]
  unfold inverseTest
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_joint_fourier_integrand (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} {Y : Ω → ℤ} (hW : Measurable W) (hY : Measurable Y)
    {g : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g) (y : ℤ) :
    Integrable (fun z : Ω × (ℝ × ℝ) =>
      g z.2.1 * phase (z.2.1 * W z.1 +
        z.2.2 * ((Y z.1 - y : ℤ) : ℝ))) (μ.prod frequencyMeasure) := by
  have hYr : Measurable (fun ω => ((Y ω - y : ℤ) : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => ((k - y : ℤ) : ℝ))).comp hY
  have hdom : Integrable (fun z : Ω × (ℝ × ℝ) => ‖g z.2.1‖)
      (μ.prod frequencyMeasure) :=
    (hgi.norm.comp_fst latticeMeasure).comp_snd μ
  apply hdom.mono'
    (((hg.comp measurable_fst).comp measurable_snd).mul
      (continuous_phase.measurable.comp
        (((measurable_fst.comp measurable_snd).mul (hW.comp measurable_fst)).add
          ((measurable_snd.comp measurable_snd).mul (hYr.comp measurable_fst))))).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖g z.2.1 * phase (z.2.1 * W z.1 + z.2.2 * ((Y z.1-y:ℤ):ℝ))‖ ≤ ‖g z.2.1‖
    rw [norm_mul, norm_phase, mul_one]

theorem mixed_fourier_inversion (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} {Y : Ω → ℤ} (hW : Measurable W) (hY : Measurable Y)
    {g : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g) (y : ℤ) :
    (∫ ω, inverseTest g (W ω) * (if Y ω = y then (1 : ℂ) else 0) ∂μ) =
      inverseNormalization ^ 2 *
        ∫ q, g q.1 * phase (-q.2 * (y : ℝ)) *
          mixedCharacteristic μ W Y q ∂frequencyMeasure := by
  calc
    (∫ ω, inverseTest g (W ω) * (if Y ω = y then (1 : ℂ) else 0) ∂μ) =
        ∫ ω, inverseNormalization ^ 2 *
          (∫ q, g q.1 * phase (q.1 * W ω +
            q.2 * ((Y ω - y : ℤ) : ℝ)) ∂frequencyMeasure) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => pointwise_mixed_inversion g (W ω) (Y ω) y
    _ = inverseNormalization ^ 2 *
        ∫ q, (∫ ω, g q.1 * phase (q.1 * W ω +
          q.2 * ((Y ω - y : ℤ) : ℝ)) ∂μ) ∂frequencyMeasure := by
      rw [integral_const_mul,
        integral_integral_swap (integrable_joint_fourier_integrand μ hW hY hg hgi y)]
    _ = inverseNormalization ^ 2 *
        ∫ q, g q.1 * phase (-q.2 * (y : ℝ)) *
          mixedCharacteristic μ W Y q ∂frequencyMeasure := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun q => by
        have hsplit : (fun ω => g q.1 * phase (q.1 * W ω +
            q.2 * ((Y ω - y : ℤ) : ℝ))) =
            fun ω => (g q.1 * phase (-q.2 * (y : ℝ))) *
              phase (q.1 * W ω + q.2 * (Y ω : ℝ)) := by
          funext ω
          have hid : q.1 * W ω + q.2 * ((Y ω - y : ℤ) : ℝ) =
              -q.2 * (y : ℝ) + (q.1 * W ω + q.2 * (Y ω : ℝ)) := by
            push_cast
            ring
          rw [hid, phase_add]
          ring
        change (∫ ω, g q.1 * phase (q.1*W ω+q.2*((Y ω-y:ℤ):ℝ)) ∂μ) = _
        rw [hsplit, integral_const_mul]
        rfl

end FCAppendix.Affine.Uniform06.MixedFourierInversion
