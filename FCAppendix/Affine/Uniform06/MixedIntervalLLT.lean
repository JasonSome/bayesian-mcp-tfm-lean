import FCAppendix.Affine.Uniform06.MixedCellSmoothing

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedIntervalLLT

open MeasureTheory Filter Set
open scoped Topology
open CharacteristicExpansion BoundedMixedGaussian MixedFourierInversion
open MixedProductCharacteristic MixedSpectralLimit MixedCellSmoothing
open KernelConcentration IntervalRecovery BandlimitedSmoother

variable (Ω : Type*) [MeasurableSpace Ω]

structure CenteredArray where
  law : ℕ → Measure Ω
  probability : ∀ n, IsProbabilityMeasure (law n)
  X : ℕ → Ω → ℝ
  Y : ℕ → Ω → ℤ
  N : ℕ → ℕ
  d : ℕ → ℝ
  measurable_X : ∀ n, Measurable (X n)
  measurable_Y : ∀ n, Measurable (Y n)
  bounded : ∀ n, ∀ᵐ ω ∂law n, |X n ω| ≤ 1 ∧ |(Y n ω : ℝ)| ≤ 1
  mean_X : ∀ n, ∫ ω, X n ω ∂law n = 0
  mean_Y : ∀ n, ∫ ω, (Y n ω : ℝ) ∂law n = 0
  covariance : ∀ n, ∫ ω, X n ω * (Y n ω : ℝ) ∂law n = 0
  d_nonneg : ∀ n, 0 ≤ d n
  d_zero : Tendsto d atTop (𝓝 0)
  scale : ∀ n, (N n : ℝ) * d n ^ 2 = 1
  market : Tendsto N atTop atTop
  vX : ℝ
  vY : ℝ
  lowerVariance : ℝ
  lowerVariance_pos : 0 < lowerVariance
  variance_X_lower : ∀ n, lowerVariance ≤ ∫ ω, X n ω ^ 2 ∂law n
  variance_Y_lower : ∀ n, lowerVariance ≤ ∫ ω, (Y n ω : ℝ) ^ 2 ∂law n
  variance_X_limit : Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂law n) atTop (𝓝 vX)
  variance_Y_limit : Tendsto (fun n => ∫ ω, (Y n ω : ℝ) ^ 2 ∂law n) atTop (𝓝 vY)

attribute [instance] CenteredArray.probability

variable {Ω}

namespace CenteredArray

def realY (A : CenteredArray Ω) (n : ℕ) (ω : Ω) : ℝ := A.Y n ω

lemma measurable_realY (A : CenteredArray Ω) (n : ℕ) : Measurable (A.realY n) := by
  have hcast : Measurable (fun k : ℤ => (k : ℝ)) := measurable_of_countable _
  exact hcast.comp (A.measurable_Y n)

lemma N_pos (A : CenteredArray Ω) (n : ℕ) : 0 < (A.N n : ℝ) := by
  have h : A.N n ≠ 0 := by
    intro hz
    have hs := A.scale n
    simp only [hz, Nat.cast_zero, zero_mul] at hs
    exact zero_ne_one hs
  exact_mod_cast Nat.pos_of_ne_zero h

lemma vX_pos (A : CenteredArray Ω) : 0 < A.vX := by
  have h : A.lowerVariance ≤ A.vX := le_of_tendsto_of_tendsto
    tendsto_const_nhds A.variance_X_limit (Eventually.of_forall A.variance_X_lower)
  exact A.lowerVariance_pos.trans_le h

lemma vY_pos (A : CenteredArray Ω) : 0 < A.vY := by
  have h : A.lowerVariance ≤ A.vY := le_of_tendsto_of_tendsto
    tendsto_const_nhds A.variance_Y_limit (Eventually.of_forall A.variance_Y_lower)
  exact A.lowerVariance_pos.trans_le h

def CompactGap (A : CenteredArray Ω) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
    ∀ᶠ n in atTop, ∀ q ∈ bandExterior T,
      ‖rowCharacteristic (A.law n) (projection (A.X n) (A.realY n) q)‖ ≤ r

def cell (A : CenteredArray Ω) (c : ℕ → ℝ) (j y : ℕ → ℤ) (n : ℕ) : Measure ℝ :=
  productCell (A.law n) (A.X n) (A.Y n) (A.N n) (c n) (j n) (y n)

instance cell_finite (A : CenteredArray Ω) (c : ℕ → ℝ) (j y : ℕ → ℤ) (n : ℕ) :
    IsFiniteMeasure (A.cell c j y n) := by
  unfold cell
  infer_instance

end CenteredArray

def density (vX vY : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ ^ 2 *
    Real.sqrt (Real.pi / (vX / 2)) * Real.sqrt (Real.pi / (vY / 2))

lemma normalized_gaussian_integral {vX vY : ℝ} (_hX : 0 < vX) (_hY : 0 < vY) :
    inverseNormalization ^ 2 * (∫ q, gaussian vX vY q ∂planeMeasure) =
      (density vX vY : ℂ) := by
  rw [integral_gaussian_pair vX vY]
  unfold density inverseNormalization
  push_cast
  ring

lemma density_pos {vX vY : ℝ} (hX : 0 < vX) (hY : 0 < vY) :
    0 < density vX vY := by
  unfold density
  positivity

lemma density_eq {vX vY : ℝ} (hX : 0 < vX) (hY : 0 < vY) :
    density vX vY = 1 / (2 * Real.pi * Real.sqrt vX * Real.sqrt vY) := by
  have hx : Real.sqrt vX ≠ 0 := (Real.sqrt_pos_of_pos hX).ne'
  have hy : Real.sqrt vY ≠ 0 := (Real.sqrt_pos_of_pos hY).ne'
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  unfold density
  rw [show Real.pi / (vX / 2) = (2 * Real.pi) / vX by field_simp [hX.ne'],
    show Real.pi / (vY / 2) = (2 * Real.pi) / vY by field_simp [hY.ne'],
    Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
  calc
    _ = Real.sqrt (2 * Real.pi) ^ 2 /
        ((2 * Real.pi) ^ 2 * Real.sqrt vX * Real.sqrt vY) := by
      field_simp [hp, hx, hy]
    _ = _ := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp [hp, hx, hy]

theorem tendsto_scaled_kernelMean (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {T : ℝ} (hT : 0 < T) (a : ℝ) :
    Tendsto (fun n => (A.N n : ℝ) *
      kernelMean (A.cell c j y n) (scaledK T) a) atTop (𝓝 (density A.vX A.vY)) := by
  obtain ⟨B, hB, hgB⟩ := rawAmplitude_uniform_bound
  obtain ⟨r, hr0, hr1, hgr⟩ := hgap (8 * Real.pi * T) (by positivity)
  have hca : Tendsto (fun n => A.d n * (c n - a)) atTop (𝓝 0) := by
    have h := hc.sub (A.d_zero.mul_const a)
    simpa only [mul_sub, zero_mul, sub_zero] using h
  have hF := tendsto_mixed_fourier_test A.law A.X A.realY A.N A.d
    (fun n => c n - a) (fun n => ((j n - y n : ℤ) : ℝ))
    A.measurable_X A.measurable_realY A.bounded A.mean_X A.mean_Y A.covariance
    A.d_nonneg A.d_zero A.scale A.market hca he A.lowerVariance_pos
    A.variance_X_lower A.variance_Y_lower A.variance_X_limit A.variance_Y_limit
    (rawAmplitude_continuous T) (rawAmplitude_integrable hT) hB.le (hgB T)
    (fun s hs => rawAmplitude_zero_outside hT hs.le) hr0 hr1 hgr
  rw [rawAmplitude_zero, one_mul] at hF
  have hM := hF.const_mul (inverseNormalization ^ 2)
  rw [normalized_gaussian_integral A.vX_pos A.vY_pos] at hM
  have heq (n : ℕ) :
      ((A.N n : ℝ) * kernelMean (A.cell c j y n) (scaledK T) a : ℂ) =
        inverseNormalization ^ 2 * ((A.N n : ℂ) *
          ∫ q, baseIntegrand (A.law n) (A.X n) (A.realY n) (A.N n)
            (rawAmplitude T) (c n - a) ((j n - y n : ℤ) : ℝ) q ∂frequencyMeasure) := by
    push_cast
    rw [CenteredArray.cell, kernelMean_productCell_spectral _
      (A.measurable_X n) (A.measurable_Y n) _ _ _ _ _ hT]
    simp only [Int.cast_sub]
    rw [show A.realY n = (fun ω : Ω => (A.Y n ω : ℝ)) from rfl]
    ring
  have hR := (Complex.continuous_re.tendsto _).comp hM
  simp_rw [← heq, Complex.ofReal_re] at hR
  convert! hR using 1
  funext n
  simp only [Function.comp_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero]

theorem exists_uniform_kernel_bound (A : CenteredArray Ω) (hgap : A.CompactGap) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      ∀ᶠ n in atTop, ∀ c a : ℝ, ∀ j y : ℤ,
        (A.N n : ℝ) *
          kernelMean (productCell (A.law n) (A.X n) (A.Y n)
            (A.N n) c j y) (scaledK T) a ≤ C := by
  obtain ⟨B, hB, hgB⟩ := rawAmplitude_uniform_bound
  let C := ‖inverseNormalization ^ 2‖ *
    (B * Real.sqrt (Real.pi / (A.lowerVariance / 4)) ^ 2 + 1) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨r, hr0, hr1, hgr⟩ := hgap (8 * Real.pi * T) (by positivity)
  have hF := eventually_uniform_spectral_bound A.law A.X A.realY A.N A.d
    A.measurable_X A.measurable_realY A.bounded A.mean_X A.mean_Y A.covariance
    A.lowerVariance_pos A.variance_X_lower A.variance_Y_lower
    A.d_nonneg A.scale A.market
    (rawAmplitude_continuous T) (rawAmplitude_integrable hT) hB.le (hgB T)
    (fun s hs => rawAmplitude_zero_outside hT hs.le) hr0 hr1 hgr
  filter_upwards [hF] with n hn c a j y
  exact (kernelMean_productCell_bound_of_spectral (A.law n)
    (A.measurable_X n) (A.measurable_Y n) (A.N n) hT hn c a j y).trans
      (by dsimp [C]; linarith)

theorem tendsto_scaled_blurredMass (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {T : ℝ} (hT : 0 < T) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => (A.N n : ℝ) *
      blurredMass (A.cell c j y n) (scaledK T) a b)
        atTop (𝓝 ((b - a) * density A.vX A.vY)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_kernel_bound A hgap
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc a b)) (bound := fun _ : ℝ => C)
    (F := fun n z => (A.N n : ℝ) * kernelMean (A.cell c j y n) (scaledK T) z)
    (f := fun _ => density A.vX A.vY)
    (Eventually.of_forall fun n =>
      ((integrable_kernelMean (A.cell c j y n) (scaledK_continuous T)
        (scaledK_integrable hT)).const_mul (A.N n : ℝ)).aestronglyMeasurable.restrict)
    (by
      filter_upwards [hbound T hT] with n hn
      exact ae_of_all _ fun z => by
        change ‖(A.N n : ℝ)*kernelMean (productCell (A.law n) (A.X n) (A.Y n)
          (A.N n) (c n) (j n) (y n)) (scaledK T) z‖ ≤ C
        rw [Real.norm_of_nonneg (mul_nonneg (A.N_pos n).le
          (kernelMean_productCell_nonneg _ _ _ _ _ _ _ _ hT))]
        exact hn (c n) z (j n) (y n))
    (integrable_const _)
    (ae_of_all _ fun z => tendsto_scaled_kernelMean A hgap c j y hc he hT z)
  rw [integral_const_Icc_real hab] at hD
  convert! hD using 1
  funext n
  rw [blurredMass_eq_integral_kernelMean (A.cell c j y n)
    (scaledK_continuous T) (scaledK_integrable hT), integral_const_mul]

theorem exists_interval_concentration (A : CenteredArray Ω) (hgap : A.CompactGap) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ T : ℝ, 0 < T →
      ∀ᶠ n in atTop, ∀ c : ℝ, ∀ j y : ℤ, ∀ l h : ℝ, l ≤ h →
        intervalMass (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) l h ≤
          (C / (A.N n : ℝ)) * (h - l + 2 * δ / T) := by
  obtain ⟨Ck, hCk, hbound⟩ := exists_uniform_kernel_bound A hgap
  obtain ⟨δ, hδ, κ, hκ, hnear⟩ := scaledK_positive_near_zero
  let C := Ck / (2 * δ * κ)
  refine ⟨C, δ, by dsimp [C]; positivity, hδ, ?_⟩
  intro T hT
  filter_upwards [hbound T hT] with n hn c j y l h hlh
  have hmean : ∀ a, kernelMean
      (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) (scaledK T) a ≤
        Ck / (A.N n : ℝ) := by
    intro a
    apply (le_div_iff₀ (A.N_pos n)).mpr
    simpa only [mul_comm] using hn c a j y
  have hconc := interval_mass_le_from_kernelMean
    (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y)
    (scaledK_continuous T) (scaledK_integrable hT) (scaledK_nonneg hT)
    (show 0 < δ / T by positivity) (show 0 < κ * T by positivity)
    (fun t ht => hnear T hT t ht) hmean hlh
  have hden : 2 * (δ / T) * (κ * T) = 2 * δ * κ := by
    field_simp [hT.ne']
  rw [hden] at hconc
  convert! hconc using 1
  dsimp only [C]
  ring

theorem tendsto_scaled_interval (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => (A.N n : ℝ) * (A.cell c j y n).real (Icc a b))
      atTop (𝓝 ((b - a) * density A.vX A.vY)) := by
  obtain ⟨C, δ, hC, hδ, hconcentration⟩ := exists_interval_concentration A hgap
  let T : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hT (k : ℕ) : 0 < T k := by dsimp [T]; positivity
  have hwidth : Tendsto (fun k => 2 * δ / T k) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * δ)
    simpa only [T, mul_one_div, mul_zero] using h
  have hlim := recover_interval_limit (A.cell c j y) (fun n => (A.N n : ℝ))
    (Eventually.of_forall A.N_pos) (fun k => scaledK (T k))
    (fun k => scaledK_integrable (hT k)) (fun k => scaledK_nonneg (hT k))
    (fun k => scaledK_mass (hT k)) (fun k => scaledK_first_moment_integrable (hT k))
    (fun k => 2 * δ / T k) C a b ((b - a) * density A.vX A.vY)
    (by simpa only [T, add_zero] using first_moment_tendsto_zero.add hwidth)
    (by
      intro k
      filter_upwards [hconcentration (T k) (hT k)] with n hn l h hlh
      exact hn (c n) (j n) (y n) l h hlh)
    (fun k => tendsto_scaled_blurredMass A hgap c j y hc he (hT k) hab)
  simpa only [intervalMass_eq_measure] using hlim

theorem tendsto_relative_interval (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun n => (A.cell c j y n).real (Icc a b) /
      (((b - a) * density A.vX A.vY) / (A.N n : ℝ))) atTop (𝓝 1) := by
  have hD : 0 < (b - a) * density A.vX A.vY :=
    mul_pos (sub_pos.mpr hab) (density_pos A.vX_pos A.vY_pos)
  have h := (tendsto_scaled_interval A hgap c j y hc he hab.le).div_const
    ((b - a) * density A.vX A.vY)
  rw [div_self hD.ne'] at h
  convert! h using 1
  funext n
  field_simp [(A.N_pos n).ne', hD.ne']

end FCAppendix.Affine.Uniform06.MixedIntervalLLT
