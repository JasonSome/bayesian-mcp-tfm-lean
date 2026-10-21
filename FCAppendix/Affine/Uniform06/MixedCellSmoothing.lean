import FCAppendix.Affine.Uniform06.MixedSpectralLimit
import FCAppendix.Affine.Uniform06.KernelConcentration
import FCAppendix.Affine.Uniform06.BandlimitedSmoother

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedCellSmoothing

open MeasureTheory Filter Set
open scoped Topology
open CharacteristicExpansion CharacteristicPowers BoundedMixedGaussian
open MixedFourierInversion MixedProductCharacteristic MixedSpectralLimit
open KernelConcentration BandlimitedSmoother

variable {Ω : Type*} [MeasurableSpace Ω]

def productCell (μ : Measure Ω) (X : Ω → ℝ) (Y : Ω → ℤ)
    (N : ℕ) (c : ℝ) (j y : ℤ) : Measure ℝ :=
  ((Measure.pi (fun _ : Fin N => μ)).restrict
    {ω | j + integerSum Y N ω = y}).map (fun ω => c + continuousSum X N ω)

instance productCell_finite (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Y : Ω → ℤ) (N : ℕ) (c : ℝ) (j y : ℤ) :
    IsFiniteMeasure (productCell μ X Y N c j y) := by
  unfold productCell
  infer_instance

lemma kernelMean_productCell (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) (c : ℝ) (j y : ℤ) {K : ℝ → ℝ} (hK : Continuous K) (a : ℝ) :
    kernelMean (productCell μ X Y N c j y) K a =
      ∫ ω, K (c + continuousSum X N ω - a) *
        (if j + integerSum Y N ω = y then (1 : ℝ) else 0)
          ∂Measure.pi (fun _ : Fin N => μ) := by
  have hsum : Measurable (fun ω => c + continuousSum X N ω) :=
    measurable_const.add (measurable_continuousSum hX N)
  have hcell : MeasurableSet {ω : Fin N → Ω | j + integerSum Y N ω = y} :=
    measurableSet_eq_fun (measurable_const.add (measurable_integerSum hY N)) measurable_const
  unfold kernelMean productCell
  rw [integral_map (f := fun x : ℝ => K (x-a)) hsum.aemeasurable
    (hK.comp (continuous_id.sub continuous_const)).aestronglyMeasurable,
    ← integral_indicator hcell]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases h : j + integerSum Y N ω = y <;> simp [h]

lemma scaledK_eq_inverseTest {T : ℝ} (hT : 0 < T) (w : ℝ) :
    (scaledK T w : ℂ) = inverseTest (rawAmplitude T) w := by
  simpa only [inverseTest, inverseNormalization, phase] using scaledK_raw_inverse hT w

theorem kernelMean_productCell_spectral (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) (c a : ℝ) (j y : ℤ) {T : ℝ} (hT : 0 < T) :
    (kernelMean (productCell μ X Y N c j y) (scaledK T) a : ℂ) =
      inverseNormalization ^ 2 *
        ∫ q, baseIntegrand μ X (fun ω => (Y ω : ℝ)) N
          (rawAmplitude T) (c - a) ((j - y : ℤ) : ℝ) q ∂frequencyMeasure := by
  rw [kernelMean_productCell μ hX hY N c j y (scaledK_continuous T) a,
    ← integral_complex_ofReal]
  have heq : (fun ω : Fin N → Ω =>
      ((scaledK T (c + continuousSum X N ω - a) *
        (if j + integerSum Y N ω = y then (1 : ℝ) else 0) : ℝ) : ℂ)) =
      fun ω => inverseTest (rawAmplitude T) ((c - a) + continuousSum X N ω) *
        (if j + integerSum Y N ω = y then (1 : ℂ) else 0) := by
    funext ω
    have hid : c + continuousSum X N ω - a = (c - a) + continuousSum X N ω := by ring
    by_cases h : j + integerSum Y N ω = y
    · simp only [h, if_true, mul_one, hid]
      exact scaledK_eq_inverseTest hT _
    · simp only [h, if_false, mul_zero, Complex.ofReal_zero]
  rw [heq, shifted_product_fourier_inversion μ hX hY N (c - a) j y
    (rawAmplitude_continuous T).measurable (rawAmplitude_integrable hT)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    dsimp [baseIntegrand]
    congr 2
    ring

theorem kernelMean_productCell_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Y : Ω → ℤ) (N : ℕ) (c a : ℝ) (j y : ℤ)
    {T : ℝ} (hT : 0 < T) :
    0 ≤ kernelMean (productCell μ X Y N c j y) (scaledK T) a :=
  integral_nonneg fun _ => scaledK_nonneg hT _

theorem kernelMean_productCell_bound_of_spectral (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hY : Measurable Y) (N : ℕ)
    {T C : ℝ} (hT : 0 < T)
    (hFourier : ∀ c e : ℝ,
      ‖(N : ℂ) * ∫ q, baseIntegrand μ X (fun ω => (Y ω : ℝ)) N
        (rawAmplitude T) c e q ∂frequencyMeasure‖ ≤ C) :
    ∀ c a : ℝ, ∀ j y : ℤ,
      (N : ℝ) * kernelMean (productCell μ X Y N c j y) (scaledK T) a ≤
        ‖inverseNormalization ^ 2‖ * C := by
  intro c a j y
  have hnonneg := mul_nonneg (Nat.cast_nonneg N)
    (kernelMean_productCell_nonneg μ X Y N c a j y hT)
  calc
    (N : ℝ) * kernelMean (productCell μ X Y N c j y) (scaledK T) a =
        ‖((N : ℝ) * kernelMean (productCell μ X Y N c j y) (scaledK T) a : ℝ)‖ :=
      (Real.norm_of_nonneg hnonneg).symm
    _ = ‖(N : ℂ) *
        (kernelMean (productCell μ X Y N c j y) (scaledK T) a : ℂ)‖ := by
      rw [← Complex.norm_real]
      congr 1
      push_cast
      rfl
    _ = ‖inverseNormalization ^ 2‖ *
        ‖(N : ℂ) * ∫ q, baseIntegrand μ X (fun ω => (Y ω : ℝ)) N
          (rawAmplitude T) (c - a) ((j - y : ℤ) : ℝ) q ∂frequencyMeasure‖ := by
      rw [kernelMean_productCell_spectral μ hX hY N c a j y hT,
        show (N : ℂ) * (inverseNormalization ^ 2 *
            ∫ q, baseIntegrand μ X (fun ω => (Y ω : ℝ)) N
              (rawAmplitude T) (c - a) ((j - y : ℤ) : ℝ) q ∂frequencyMeasure) =
          inverseNormalization ^ 2 * ((N : ℂ) *
            ∫ q, baseIntegrand μ X (fun ω => (Y ω : ℝ)) N
              (rawAmplitude T) (c - a) ((j - y : ℤ) : ℝ) q ∂frequencyMeasure) by ring,
        norm_mul]
    _ ≤ ‖inverseNormalization ^ 2‖ * C :=
      mul_le_mul_of_nonneg_left (hFourier _ _) (norm_nonneg _)

end FCAppendix.Affine.Uniform06.MixedCellSmoothing
