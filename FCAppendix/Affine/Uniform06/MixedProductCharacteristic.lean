import FCAppendix.Affine.Uniform06.MixedFourierInversion
import FCAppendix.Affine.Uniform06.BoundedMixedGaussian
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedProductCharacteristic

open MeasureTheory Set
open scoped BigOperators
open CharacteristicExpansion MixedFourierInversion BoundedMixedGaussian

variable {Ω : Type*} [MeasurableSpace Ω]

def continuousSum (X : Ω → ℝ) (N : ℕ) (ω : Fin N → Ω) : ℝ := ∑ k, X (ω k)

def integerSum (Y : Ω → ℤ) (N : ℕ) (ω : Fin N → Ω) : ℤ := ∑ k, Y (ω k)

lemma measurable_continuousSum {X : Ω → ℝ} (hX : Measurable X) (N : ℕ) :
    Measurable (continuousSum X N) :=
  Finset.measurable_sum _ fun k _ => hX.comp (measurable_pi_apply k)

lemma measurable_integerSum {Y : Ω → ℤ} (hY : Measurable Y) (N : ℕ) :
    Measurable (integerSum Y N) :=
  Finset.measurable_sum _ fun k _ => hY.comp (measurable_pi_apply k)

lemma phase_finite_sum {ι : Type*} (s : Finset ι) (z : ι → ℝ) :
    phase (∑ k ∈ s, z k) = ∏ k ∈ s, phase (z k) := by
  simp only [phase, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

theorem integral_phase_continuousSum (μ : Measure Ω) [SigmaFinite μ]
    (X : Ω → ℝ) (N : ℕ) :
    (∫ ω, phase (continuousSum X N ω) ∂Measure.pi (fun _ : Fin N => μ)) =
      rowCharacteristic μ X ^ N := by
  have hphase (ω : Fin N → Ω) : phase (continuousSum X N ω) =
      ∏ k : Fin N, phase (X (ω k)) := by
    simpa [continuousSum] using phase_finite_sum Finset.univ (fun k => X (ω k))
  simp_rw [hphase]
  rw [integral_fintype_prod_eq_pow (ι := Fin N) (fun ω => phase (X ω)), Fintype.card_fin]
  rfl

theorem shifted_product_mixedCharacteristic (μ : Measure Ω) [SigmaFinite μ]
    (X : Ω → ℝ) (Y : Ω → ℤ) (N : ℕ) (c : ℝ) (j : ℤ) (q : ℝ × ℝ) :
    mixedCharacteristic (Measure.pi (fun _ : Fin N => μ))
      (fun ω => c + continuousSum X N ω) (fun ω => j + integerSum Y N ω) q =
      phase (q.1 * c + q.2 * (j : ℝ)) *
        rowCharacteristic μ (projection X (fun ω => (Y ω : ℝ)) q) ^ N := by
  have hid (ω : Fin N → Ω) :
      q.1 * (c + continuousSum X N ω) + q.2 * ((j + integerSum Y N ω : ℤ) : ℝ) =
      (q.1 * c + q.2 * (j : ℝ)) +
        continuousSum (projection X (fun ω => (Y ω : ℝ)) q) N ω := by
    simp only [continuousSum, integerSum, projection, Int.cast_add, Int.cast_sum,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  unfold mixedCharacteristic
  simp_rw [hid, phase_add]
  rw [integral_const_mul, integral_phase_continuousSum]

theorem shifted_product_fourier_inversion (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) (c : ℝ) (j y : ℤ) {g : ℝ → ℂ}
    (hg : Measurable g) (hgi : Integrable g) :
    (∫ ω, inverseTest g (c + continuousSum X N ω) *
      (if j + integerSum Y N ω = y then (1 : ℂ) else 0)
        ∂Measure.pi (fun _ : Fin N => μ)) =
      inverseNormalization ^ 2 *
        ∫ q, g q.1 * phase (q.1 * c + q.2 * ((j - y : ℤ) : ℝ)) *
          rowCharacteristic μ (projection X (fun ω => (Y ω : ℝ)) q) ^ N
            ∂frequencyMeasure := by
  have he := mixed_fourier_inversion (Measure.pi (fun _ : Fin N => μ))
    (W := fun ω => c+continuousSum X N ω) (Y := fun ω => j+integerSum Y N ω)
    (measurable_const.add (measurable_continuousSum hX N))
    (measurable_const.add (measurable_integerSum hY N)) hg hgi y
  convert! he.trans ?_ using 1
  change inverseNormalization^2 * (∫ q, g q.1 * phase (-q.2 * (y:ℝ)) *
    mixedCharacteristic (Measure.pi (fun _ : Fin N => μ))
      (fun ω => c+continuousSum X N ω) (fun ω => j+integerSum Y N ω) q ∂frequencyMeasure) = _
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    change g q.1 * phase (-q.2*(y:ℝ)) * mixedCharacteristic _ _ _ q = _
    rw [shifted_product_mixedCharacteristic]
    have hid : q.1 * c + q.2 * ((j - y : ℤ) : ℝ) =
        -q.2 * (y : ℝ) + (q.1 * c + q.2 * (j : ℝ)) := by
      push_cast
      ring
    change _ = g q.1 * phase (q.1*c+q.2*((j-y:ℤ):ℝ))*_
    rw [hid, phase_add]
    simp_rw [phase_add, neg_mul]
    ring

end FCAppendix.Affine.Uniform06.MixedProductCharacteristic
