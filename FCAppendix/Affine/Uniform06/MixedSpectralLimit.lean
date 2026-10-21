import FCAppendix.Affine.Uniform06.BoundedMixedGaussian
import FCAppendix.Affine.Uniform06.FourierTruncation
import FCAppendix.Affine.Uniform06.MixedProductCharacteristic

noncomputable section

namespace FCAppendix.Affine.Uniform06.MixedSpectralLimit

open MeasureTheory Filter Set
open scoped Topology
open CharacteristicExpansion CharacteristicPowers BoundedMixedGaussian
open MixedFourierInversion MixedProductCharacteristic FourierTruncation

abbrev planeMeasure : Measure (ℝ × ℝ) := volume.prod volume

def latticeStrip : Set (ℝ × ℝ) := univ ×ˢ Icc (-Real.pi) Real.pi

def bandRectangle (T : ℝ) : Set (ℝ × ℝ) :=
  Icc (-T) T ×ˢ Icc (-Real.pi) Real.pi

def bandExterior (T : ℝ) : Set (ℝ × ℝ) :=
  bandRectangle T \ originRegion 1

lemma frequencyMeasure_eq_restrict :
    frequencyMeasure = planeMeasure.restrict latticeStrip := by
  simpa [frequencyMeasure, latticeMeasure, latticeStrip] using
    (Measure.prod_restrict (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) univ (Icc (-Real.pi) Real.pi))

lemma originRegion_subset_latticeStrip : originRegion 1 ⊆ latticeStrip := by
  intro q hq
  have hq' : |q.1| + |q.2| ≤ (1 : ℝ) / 4 := by simpa [originRegion] using hq
  have hsmall : |q.2| ≤ (1 : ℝ) / 4 := by linarith [abs_nonneg q.1]
  have hpi : (1 : ℝ) / 4 ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact ⟨mem_univ _, abs_le.mp (hsmall.trans hpi)⟩

lemma measurableSet_bandRectangle (T : ℝ) : MeasurableSet (bandRectangle T) :=
  measurableSet_Icc.prod measurableSet_Icc

lemma measurableSet_bandExterior (T : ℝ) : MeasurableSet (bandExterior T) :=
  (measurableSet_bandRectangle T).diff (measurableSet_originRegion 1)

instance bandExterior_finite (T : ℝ) :
    IsFiniteMeasure (planeMeasure.restrict (bandExterior T)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact (measure_mono sdiff_subset).trans_lt
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)

variable {Ω : Type*} [MeasurableSpace Ω]

def baseIntegrand (μ : Measure Ω) (X Y : Ω → ℝ)
    (N : ℕ) (g : ℝ → ℂ) (c e : ℝ) (q : ℝ × ℝ) : ℂ :=
  g q.1 * phase (c * q.1 + e * q.2) *
    rowCharacteristic μ (projection X Y q) ^ N

lemma continuous_baseIntegrand (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) {g : ℝ → ℂ} (hg : Continuous g) (c e : ℝ) :
    Continuous (baseIntegrand μ X Y N g c e) := by
  have hφ : Continuous (fun q : ℝ × ℝ => rowCharacteristic μ (projection X Y q)) := by
    simpa only [one_mul] using continuous_projection_characteristic μ hX hY 1
  exact ((hg.comp continuous_fst).mul
    (continuous_phase.comp ((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)))).mul (hφ.pow N)

lemma norm_baseIntegrand_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (N : ℕ) (g : ℝ → ℂ) (c e : ℝ) (q : ℝ × ℝ) :
    ‖baseIntegrand μ X Y N g c e q‖ ≤ ‖g q.1‖ := by
  unfold baseIntegrand
  rw [norm_mul, norm_mul, norm_phase, mul_one, norm_pow]
  apply mul_le_of_le_one_right (norm_nonneg _)
  simpa only [one_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (norm_rowCharacteristic_le_one μ _) N

lemma integrable_baseIntegrand_frequency (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (N : ℕ) {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g) (c e : ℝ) :
    Integrable (baseIntegrand μ X Y N g c e) frequencyMeasure := by
  apply (hgi.norm.comp_fst latticeMeasure).mono'
    (continuous_baseIntegrand μ hX hY N hg c e).aestronglyMeasurable
  exact ae_of_all _ fun q => norm_baseIntegrand_le μ X Y N g c e q

lemma scaled_origin_integrand (μ : Measure Ω) (X Y : Ω → ℝ)
    (N : ℕ) {d : ℝ} (hd : 0 ≤ d) (g : ℝ → ℂ) (c e : ℝ) :
    (fun q : ℝ × ℝ =>
      (originRegion 1).indicator (baseIntegrand μ X Y N g c e)
        (d * q.1, d * q.2)) =
      originIntegrand μ X Y N d g (d * c) (d * e) := by
  funext q
  have hregion : (d * q.1, d * q.2) ∈ originRegion 1 ↔ q ∈ originRegion d := by
    simp only [originRegion, mem_setOf_eq, one_mul, abs_mul, abs_of_nonneg hd]
    ring_nf
  by_cases hq : q ∈ originRegion d
  · rw [indicator_of_mem (hregion.mpr hq), originIntegrand, indicator_of_mem hq]
    unfold baseIntegrand
    have hp : projection X Y (d * q.1, d * q.2) =
        fun ω => d * projection X Y q ω := by
      funext ω
      dsimp [projection]
      ring
    rw [hp]
    have hs : c * (d * q.1) + e * (d * q.2) = (d * c) * q.1 + (d * e) * q.2 := by ring
    rw [hs]
  · rw [indicator_of_notMem (fun h => hq (hregion.mp h)),
      originIntegrand, indicator_of_notMem hq]

theorem integral_frequency_eq_origin_add_exterior (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (N : ℕ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    {T : ℝ} (hsupp : ∀ s, T < |s| → g s = 0) (c e : ℝ) :
    (∫ q, baseIntegrand μ X Y N g c e q ∂frequencyMeasure) =
      (∫ q in originRegion 1, baseIntegrand μ X Y N g c e q ∂planeMeasure) +
      ∫ q in bandExterior T, baseIntegrand μ X Y N g c e q ∂planeMeasure := by
  let f := baseIntegrand μ X Y N g c e
  have hfi : IntegrableOn f latticeStrip planeMeasure := by
    change Integrable (baseIntegrand μ X Y N g c e) (planeMeasure.restrict latticeStrip)
    rw [← frequencyMeasure_eq_restrict]
    exact integrable_baseIntegrand_frequency μ hX hY N hg hgi c e
  have hOi : IntegrableOn f (originRegion 1) planeMeasure :=
    hfi.mono_set originRegion_subset_latticeStrip
  have hEi : IntegrableOn f (bandExterior T) planeMeasure := by
    apply hfi.mono_set
    intro q hq
    exact ⟨mem_univ _, hq.1.2⟩
  have heq : latticeStrip.indicator f =
      (originRegion 1).indicator f + (bandExterior T).indicator f := by
    funext q
    by_cases hO : q ∈ originRegion 1
    · have hD := originRegion_subset_latticeStrip hO
      have hE : q ∉ bandExterior T := fun h => h.2 hO
      simp only [Pi.add_apply, indicator_of_mem hD, indicator_of_mem hO,
        indicator_of_notMem hE, add_zero]
    · by_cases hD : q ∈ latticeStrip
      · by_cases hT : q.1 ∈ Icc (-T) T
        · have hE : q ∈ bandExterior T := ⟨⟨hT, hD.2⟩, hO⟩
          simp only [Pi.add_apply, indicator_of_mem hD, indicator_of_notMem hO,
            indicator_of_mem hE, zero_add]
        · have hz : g q.1 = 0 := hsupp _
            (lt_of_not_ge (fun h => hT (abs_le.mp h)))
          have hfz : f q = 0 := by simp [f, baseIntegrand, hz]
          have hE : q ∉ bandExterior T := fun h => hT h.1.1
          simp only [Pi.add_apply,indicator_of_mem hD,indicator_of_notMem hO,
            indicator_of_notMem hE,hfz,zero_add]
      · have hE : q ∉ bandExterior T := by
          intro h
          exact hD ⟨mem_univ _, h.1.2⟩
        simp only [Pi.add_apply, indicator_of_notMem hD, indicator_of_notMem hO,
          indicator_of_notMem hE, zero_add]
  change (∫ q, f q ∂frequencyMeasure) =
    (∫ q in originRegion 1, f q ∂planeMeasure) + ∫ q in bandExterior T, f q ∂planeMeasure
  have hD : MeasurableSet latticeStrip := MeasurableSet.univ.prod measurableSet_Icc
  rw [frequencyMeasure_eq_restrict, ← integral_indicator hD, heq]
  simp only [Pi.add_apply]
  rw [integral_add ((integrable_indicator_iff (measurableSet_originRegion 1)).mpr hOi)
      ((integrable_indicator_iff (measurableSet_bandExterior T)).mpr hEi),
    integral_indicator (measurableSet_originRegion 1),
    integral_indicator (measurableSet_bandExterior T)]

theorem tendsto_mixed_fourier_test
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ℕ → Ω → ℝ) (N : ℕ → ℕ) (d c e : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hb : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ 1 ∧ |Y n ω| ≤ 1)
    (hXm : ∀ n, ∫ ω, X n ω ∂μ n = 0)
    (hYm : ∀ n, ∫ ω, Y n ω ∂μ n = 0)
    (hXY : ∀ n, ∫ ω, X n ω * Y n ω ∂μ n = 0)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Tendsto d atTop (𝓝 0))
    (hscale : ∀ n, (N n : ℝ) * d n ^ 2 = 1) (hN : Tendsto N atTop atTop)
    (hc : Tendsto (fun n => d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => d n * e n) atTop (𝓝 0))
    {vX vY lambdaBound : ℝ} (hlambdaBound : 0 < lambdaBound)
    (hlambdaBoundX : ∀ n, lambdaBound ≤ ∫ ω, X n ω ^ 2 ∂μ n)
    (hlambdaBoundY : ∀ n, lambdaBound ≤ ∫ ω, Y n ω ^ 2 ∂μ n)
    (hvX : Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂μ n) atTop (𝓝 vX))
    (hvY : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂μ n) atTop (𝓝 vY))
    {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    {B T r : ℝ} (hB : 0 ≤ B) (hgB : ∀ t, ‖g t‖ ≤ B)
    (hsupp : ∀ s, T < |s| → g s = 0) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hgap : ∀ᶠ n in atTop, ∀ q ∈ bandExterior T,
      ‖rowCharacteristic (μ n) (projection (X n) (Y n) q)‖ ≤ r) :
    Tendsto (fun n => (N n : ℂ) *
      ∫ q, baseIntegrand (μ n) (X n) (Y n) (N n) g (c n) (e n) q
        ∂frequencyMeasure) atTop
      (𝓝 (g 0 * ∫ q, gaussian vX vY q ∂planeMeasure)) := by
  have horigin := tendsto_origin_integral μ X Y N d
    (fun n => d n * c n) (fun n => d n * e n)
    hX hY hb hXm hYm hXY hd0 hd hscale hc he hlambdaBound hlambdaBoundX hlambdaBoundY hvX hvY hg hB hgB
  have hscaled (n : ℕ) :
      (∫ q, originIntegrand (μ n) (X n) (Y n) (N n) (d n) g
        (d n * c n) (d n * e n) q ∂planeMeasure) =
      (N n : ℂ) * ∫ q in originRegion 1,
        baseIntegrand (μ n) (X n) (Y n) (N n) g (c n) (e n) q ∂planeMeasure := by
    rw [← scaled_origin_integrand _ _ _ _ (hd0 n),
      integral_pair_scale _ _ (hscale n),
      integral_indicator (measurableSet_originRegion 1)]
  simp_rw [hscaled] at horigin
  have htail := tendsto_market_scaled_compact_tail
    (planeMeasure.restrict (bandExterior T))
    (fun n q => g q.1 * phase (c n * q.1 + e n * q.2))
    (fun n q => rowCharacteristic (μ n) (projection (X n) (Y n) q)) N
    (fun n => ((hg.comp continuous_fst).mul
      (continuous_phase.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd)))).measurable)
    (fun n => by
      simpa only [one_mul] using
        (continuous_projection_characteristic (μ n) (hX n) (hY n) 1).measurable)
    hB hr0 hr1
    (fun n => ae_of_all _ fun q => by simpa only [norm_mul, norm_phase, mul_one] using hgB q.1)
    (by
      filter_upwards [hgap] with n hn
      filter_upwards [self_mem_ae_restrict (measurableSet_bandExterior T)] with q hq
      exact hn q hq) hN
  have h := horigin.add htail
  simp only [add_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [integral_frequency_eq_origin_add_exterior (μ n) (hX n) (hY n)
      (N n) hg hgi hsupp (c n) (e n), mul_add]
    rfl

theorem market_scaled_spectral_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1)
    (hXm : ∫ ω, X ω ∂μ = 0) (hYm : ∫ ω, Y ω ∂μ = 0)
    (hXY : ∫ ω, X ω * Y ω ∂μ = 0)
    {lambdaBound : ℝ} (hlambdaBound : 0 < lambdaBound)
    (hlambdaBoundX : lambdaBound ≤ ∫ ω, X ω ^ 2 ∂μ) (hlambdaBoundY : lambdaBound ≤ ∫ ω, Y ω ^ 2 ∂μ)
    (N : ℕ) {d : ℝ} (hd : 0 ≤ d) (hscale : (N : ℝ) * d ^ 2 = 1)
    {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    {B T r : ℝ} (hB : 0 ≤ B) (hgB : ∀ t, ‖g t‖ ≤ B)
    (hsupp : ∀ s, T < |s| → g s = 0) (hr : 0 ≤ r)
    (hgap : ∀ q ∈ bandExterior T,
      ‖rowCharacteristic μ (projection X Y q)‖ ≤ r) (c e : ℝ) :
    ‖(N : ℂ) * ∫ q, baseIntegrand μ X Y N g c e q ∂frequencyMeasure‖ ≤
      B * (Real.sqrt (Real.pi / (lambdaBound / 4))) ^ 2 +
      (planeMeasure.restrict (bandExterior T)).real univ * B *
        ((N : ℝ) * r ^ N) := by
  let H : (ℝ × ℝ) → ℝ := fun q =>
    B * (Real.exp (-(lambdaBound / 4) * q.1 ^ 2) * Real.exp (-(lambdaBound / 4) * q.2 ^ 2))
  have hHi : Integrable H planeMeasure :=
    ((integrable_exp_neg_mul_sq (show 0 < lambdaBound / 4 by linarith)).mul_prod
      (integrable_exp_neg_mul_sq (show 0 < lambdaBound / 4 by linarith))).const_mul B
  have hdom : ∀ q, ‖originIntegrand μ X Y N d g (d * c) (d * e) q‖ ≤ H q := by
    intro q
    by_cases hq : q ∈ originRegion d
    · rw [originIntegrand, indicator_of_mem hq, norm_mul, norm_mul, norm_phase, mul_one]
      exact mul_le_mul (hgB _)
        (scaled_mixed_pow_gaussian_bound μ hX hY hb hXm hYm hXY hlambdaBoundX hlambdaBoundY
          N hd hscale q hq) (norm_nonneg _) hB
    · rw [originIntegrand, indicator_of_notMem hq, norm_zero]
      dsimp [H]
      positivity
  have hmeas : AEStronglyMeasurable
      (originIntegrand μ X Y N d g (d * c) (d * e)) planeMeasure := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ (measurableSet_originRegion _)
    exact ((hg.comp (continuous_const.mul continuous_fst)).mul
      (continuous_phase.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd)))).mul
      ((continuous_projection_characteristic μ hX hY d).pow N) |>.measurable
  have hOi := hHi.mono' hmeas (ae_of_all _ hdom)
  have horigin : ‖(N : ℂ) *
      ∫ q in originRegion 1, baseIntegrand μ X Y N g c e q ∂planeMeasure‖ ≤
        B * (Real.sqrt (Real.pi / (lambdaBound / 4))) ^ 2 := by
    rw [← integral_indicator (measurableSet_originRegion 1),
      ← integral_pair_scale _ _ hscale, scaled_origin_integrand _ _ _ _ hd]
    calc
      ‖∫ q, originIntegrand μ X Y N d g (d * c) (d * e) q ∂planeMeasure‖ ≤
          ∫ q, ‖originIntegrand μ X Y N d g (d * c) (d * e) q‖ ∂planeMeasure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ q, H q ∂planeMeasure := integral_mono_ae hOi.norm hHi (ae_of_all _ hdom)
      _ = B * (Real.sqrt (Real.pi / (lambdaBound / 4))) ^ 2 := by
        dsimp [H,planeMeasure]
        rw [integral_const_mul]
        have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (fun x : ℝ => Real.exp (-(lambdaBound/4)*x^2))
          (fun y : ℝ => Real.exp (-(lambdaBound/4)*y^2))
        have hp' : (∫ q : ℝ × ℝ, Real.exp (-(lambdaBound/4)*q.1^2) *
            Real.exp (-(lambdaBound/4)*q.2^2) ∂volume.prod volume) =
            (Real.sqrt (Real.pi/(lambdaBound/4)))^2 := by
          convert! hp using 1
          simp only [integral_gaussian]
          ring
        rw [hp']
  have htail : ‖(N : ℂ) *
      ∫ q in bandExterior T, baseIntegrand μ X Y N g c e q ∂planeMeasure‖ ≤
        (planeMeasure.restrict (bandExterior T)).real univ * B *
          ((N : ℝ) * r ^ N) := by
    rw [norm_mul, Complex.norm_natCast]
    have ht := integral_amplitude_power_bound
      (planeMeasure.restrict (bandExterior T))
      (((hg.comp continuous_fst).mul
        (continuous_phase.comp ((continuous_const.mul continuous_fst).add
          (continuous_const.mul continuous_snd)))).measurable)
      (by simpa only [one_mul] using (continuous_projection_characteristic μ hX hY 1).measurable)
      hB hr
      (ae_of_all _ fun q => by
        change ‖g q.1 * phase (c*q.1+e*q.2)‖ ≤ B
        simpa only [norm_mul, norm_phase, mul_one] using hgB q.1)
      (by
        filter_upwards [self_mem_ae_restrict (measurableSet_bandExterior T)] with q hq
        exact hgap q hq) N
    calc
      (N : ℝ) * ‖∫ q in bandExterior T, baseIntegrand μ X Y N g c e q ∂planeMeasure‖ ≤
          (N : ℝ) * ((planeMeasure.restrict (bandExterior T)).real univ * (B * r ^ N)) :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      _ = _ := by ring
  rw [integral_frequency_eq_origin_add_exterior μ hX hY N hg hgi hsupp c e, mul_add]
  exact (norm_add_le _ _).trans (add_le_add horigin htail)

theorem eventually_uniform_spectral_bound
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ℕ → Ω → ℝ) (N : ℕ → ℕ) (d : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hb : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ 1 ∧ |Y n ω| ≤ 1)
    (hXm : ∀ n, ∫ ω, X n ω ∂μ n = 0)
    (hYm : ∀ n, ∫ ω, Y n ω ∂μ n = 0)
    (hXY : ∀ n, ∫ ω, X n ω * Y n ω ∂μ n = 0)
    {lambdaBound : ℝ} (hlambdaBound : 0 < lambdaBound)
    (hlambdaBoundX : ∀ n, lambdaBound ≤ ∫ ω, X n ω ^ 2 ∂μ n)
    (hlambdaBoundY : ∀ n, lambdaBound ≤ ∫ ω, Y n ω ^ 2 ∂μ n)
    (hd : ∀ n, 0 ≤ d n) (hscale : ∀ n, (N n : ℝ) * d n ^ 2 = 1)
    (hN : Tendsto N atTop atTop)
    {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable g)
    {B T r : ℝ} (hB : 0 ≤ B) (hgB : ∀ t, ‖g t‖ ≤ B)
    (hsupp : ∀ s, T < |s| → g s = 0) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hgap : ∀ᶠ n in atTop, ∀ q ∈ bandExterior T,
      ‖rowCharacteristic (μ n) (projection (X n) (Y n) q)‖ ≤ r) :
    ∀ᶠ n in atTop, ∀ c e : ℝ,
      ‖(N n : ℂ) * ∫ q,
        baseIntegrand (μ n) (X n) (Y n) (N n) g c e q ∂frequencyMeasure‖ ≤
        B * (Real.sqrt (Real.pi / (lambdaBound / 4))) ^ 2 + 1 := by
  have ht : Tendsto (fun n =>
      (planeMeasure.restrict (bandExterior T)).real univ * B *
        ((N n : ℝ) * r ^ N n)) atTop (𝓝 0) := by
    have h := ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN).const_mul
      ((planeMeasure.restrict (bandExterior T)).real univ * B)
    convert! h using 1
    simp only [mul_zero]
  have hsmall := ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hgap, hsmall] with n hn hs c e
  exact (market_scaled_spectral_bound (μ n) (hX n) (hY n) (hb n)
    (hXm n) (hYm n) (hXY n) hlambdaBound (hlambdaBoundX n) (hlambdaBoundY n) (N n) (hd n) (hscale n)
    hg hgi hB hgB hsupp hr0 hn c e).trans (by linarith)

end FCAppendix.Affine.Uniform06.MixedSpectralLimit
