import FCAppendix.Affine.Uniform06.CharacteristicPowers
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace FCAppendix.Affine.Uniform06.BoundedMixedGaussian

open MeasureTheory Filter Set
open scoped Topology
open CharacteristicExpansion CharacteristicPowers

variable {Ω : Type*} [MeasurableSpace Ω]

def projection (X Y : Ω → ℝ) (q : ℝ × ℝ) (ω : Ω) : ℝ :=
  q.1 * X ω + q.2 * Y ω

omit [MeasurableSpace Ω] in
lemma projection_abs_le {X Y : Ω → ℝ} (q : ℝ × ℝ) {ω : Ω}
    (hω : |X ω| ≤ 1 ∧ |Y ω| ≤ 1) :
    |projection X Y q ω| ≤ |q.1| + |q.2| := by
  calc
    |projection X Y q ω| ≤ |q.1| * |X ω| + |q.2| * |Y ω| := by
      simpa only [projection, abs_mul] using abs_add_le (q.1 * X ω) (q.2 * Y ω)
    _ ≤ |q.1| * 1 + |q.2| * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hω.1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg _))
    _ = |q.1| + |q.2| := by ring

lemma integrable_coordinate (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hXb : ∀ᵐ ω ∂μ, |X ω| ≤ 1) :
    Integrable X μ := by
  simpa only [pow_one] using integrable_pow_of_abs_le μ hX hXb 1

lemma integrable_cross (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1) :
    Integrable (fun ω => X ω * Y ω) μ := by
  apply Integrable.of_bound (hX.mul hY).aestronglyMeasurable 1
  filter_upwards [hb] with ω hω
  change |X ω * Y ω| ≤ 1
  rw [abs_mul]
  exact mul_le_one₀ hω.1 (abs_nonneg _) hω.2

lemma integral_projection (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1) (q : ℝ × ℝ) :
    (∫ ω, projection X Y q ω ∂μ) =
      q.1 * (∫ ω, X ω ∂μ) + q.2 * (∫ ω, Y ω ∂μ) := by
  unfold projection
  rw [integral_add
    ((integrable_coordinate μ hX (hb.mono fun _ h => h.1)).const_mul _)
    ((integrable_coordinate μ hY (hb.mono fun _ h => h.2)).const_mul _),
    integral_const_mul, integral_const_mul]

lemma integral_projection_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1) (q : ℝ × ℝ) :
    (∫ ω, projection X Y q ω ^ 2 ∂μ) =
      q.1 ^ 2 * (∫ ω, X ω ^ 2 ∂μ) +
      q.2 ^ 2 * (∫ ω, Y ω ^ 2 ∂μ) +
      (2 * q.1 * q.2) * (∫ ω, X ω * Y ω ∂μ) := by
  have hX2 := integrable_pow_of_abs_le μ hX (hb.mono fun _ h => h.1) 2
  have hY2 := integrable_pow_of_abs_le μ hY (hb.mono fun _ h => h.2) 2
  have hXY := integrable_cross μ hX hY hb
  have hpoly : (fun ω => projection X Y q ω ^ 2) =
      fun ω => (q.1 ^ 2 * X ω ^ 2 + q.2 ^ 2 * Y ω ^ 2) +
        (2 * q.1 * q.2) * (X ω * Y ω) := by
    funext ω
    dsimp [projection]
    ring
  rw [hpoly]
  rw [integral_add
    (show Integrable (fun ω => q.1 ^ 2 * X ω ^ 2 + q.2 ^ 2 * Y ω ^ 2) μ from
      (hX2.const_mul _).add (hY2.const_mul _))
    (hXY.const_mul _), integral_add (hX2.const_mul _) (hY2.const_mul _)]
  simp only [integral_const_mul]

lemma scaled_projection_mean_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1)
    (hXm : ∫ ω, X ω ∂μ = 0) (hYm : ∫ ω, Y ω ∂μ = 0)
    (d : ℝ) (q : ℝ × ℝ) :
    (∫ ω, d * projection X Y q ω ∂μ) = 0 := by
  rw [integral_const_mul, integral_projection μ hX hY hb q, hXm, hYm]
  ring

lemma accumulated_scaled_second_moment (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1)
    (hXY : ∫ ω, X ω * Y ω ∂μ = 0)
    (N : ℕ) (d : ℝ) (hd : (N : ℝ) * d ^ 2 = 1) (q : ℝ × ℝ) :
    (N : ℝ) * (∫ ω, (d * projection X Y q ω) ^ 2 ∂μ) =
      q.1 ^ 2 * (∫ ω, X ω ^ 2 ∂μ) +
      q.2 ^ 2 * (∫ ω, Y ω ^ 2 ∂μ) := by
  simp_rw [mul_pow]
  rw [integral_const_mul, ← mul_assoc, hd, one_mul,
    integral_projection_sq μ hX hY hb q, hXY, mul_zero, add_zero]

lemma continuous_projection_characteristic (μ : Measure Ω) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (d : ℝ) :
    Continuous (fun q : ℝ × ℝ =>
      rowCharacteristic μ (fun ω => d * projection X Y q ω)) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact (continuous_phase.measurable.comp
      (measurable_const.mul
        ((measurable_const.mul hX).add (measurable_const.mul hY)))).aestronglyMeasurable
  · intro q
    exact ae_of_all _ fun ω => (norm_phase _).le
  · exact integrable_const 1
  · exact ae_of_all _ fun ω => continuous_phase.comp
      (continuous_const.mul ((continuous_fst.mul continuous_const).add
        (continuous_snd.mul continuous_const)))

def gaussian (vX vY : ℝ) (q : ℝ × ℝ) : ℂ :=
  Complex.exp (-((q.1 ^ 2 * vX + q.2 ^ 2 * vY : ℝ) : ℂ) / 2)

theorem tendsto_scaled_mixed_powers
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ℕ → Ω → ℝ) (N : ℕ → ℕ) (d : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hb : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ 1 ∧ |Y n ω| ≤ 1)
    (hXm : ∀ n, ∫ ω, X n ω ∂μ n = 0)
    (hYm : ∀ n, ∫ ω, Y n ω ∂μ n = 0)
    (hXY : ∀ n, ∫ ω, X n ω * Y n ω ∂μ n = 0)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Tendsto d atTop (𝓝 0))
    (hscale : ∀ n, (N n : ℝ) * d n ^ 2 = 1)
    {vX vY : ℝ}
    (hvX : Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂μ n) atTop (𝓝 vX))
    (hvY : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂μ n) atTop (𝓝 vY))
    (q : ℝ × ℝ) :
    Tendsto (fun n =>
      rowCharacteristic (μ n) (fun ω => d n * projection (X n) (Y n) q ω) ^ N n)
      atTop (𝓝 (gaussian vX vY q)) := by
  apply tendsto_triangular_characteristic_powers μ
    (fun n ω => d n * projection (X n) (Y n) q ω) N
    (fun n => d n * (|q.1| + |q.2|))
  · intro n
    exact measurable_const.mul
      ((measurable_const.mul (hX n)).add (measurable_const.mul (hY n)))
  · intro n
    filter_upwards [hb n] with ω hω
    rw [abs_mul, abs_of_nonneg (hd0 n)]
    exact mul_le_mul_of_nonneg_left (projection_abs_le q hω) (hd0 n)
  · intro n
    exact scaled_projection_mean_zero (μ n) (hX n) (hY n) (hb n)
      (hXm n) (hYm n) (d n) q
  · simpa only [zero_mul] using hd.mul_const (|q.1| + |q.2|)
  · have h := (hvX.const_mul (q.1 ^ 2)).add (hvY.const_mul (q.2 ^ 2))
    apply h.congr'
    exact Eventually.of_forall fun n =>
      (accumulated_scaled_second_moment (μ n) (hX n) (hY n) (hb n)
        (hXY n) (N n) (d n) (hscale n) q).symm

theorem scaled_mixed_pow_gaussian_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1 ∧ |Y ω| ≤ 1)
    (hXm : ∫ ω, X ω ∂μ = 0) (hYm : ∫ ω, Y ω ∂μ = 0)
    (hXY : ∫ ω, X ω * Y ω ∂μ = 0)
    {lambdaBound : ℝ} (hlambdaBoundX : lambdaBound ≤ ∫ ω, X ω ^ 2 ∂μ)
    (hlambdaBoundY : lambdaBound ≤ ∫ ω, Y ω ^ 2 ∂μ)
    (N : ℕ) {d : ℝ} (hd0 : 0 ≤ d) (hscale : (N : ℝ) * d ^ 2 = 1)
    (q : ℝ × ℝ) (hq : d * (|q.1| + |q.2|) ≤ (1 : ℝ) / 4) :
    ‖rowCharacteristic μ (fun ω => d * projection X Y q ω) ^ N‖ ≤
      Real.exp (-(lambdaBound / 4) * q.1 ^ 2) * Real.exp (-(lambdaBound / 4) * q.2 ^ 2) := by
  have hsmall : ∀ᵐ ω ∂μ, |d * projection X Y q ω| ≤ (1 : ℝ) / 4 := by
    filter_upwards [hb] with ω hω
    rw [abs_mul, abs_of_nonneg hd0]
    exact (mul_le_mul_of_nonneg_left (projection_abs_le q hω) hd0).trans hq
  have h := centered_characteristic_pow_norm_le μ
    (measurable_const.mul ((measurable_const.mul hX).add (measurable_const.mul hY)))
    hsmall (scaled_projection_mean_zero μ hX hY hb hXm hYm d q) N
  have hv := accumulated_scaled_second_moment μ hX hY hb hXY N d hscale q
  have hlo : lambdaBound * (q.1 ^ 2 + q.2 ^ 2) ≤
      q.1 ^ 2 * (∫ ω, X ω ^ 2 ∂μ) + q.2 ^ 2 * (∫ ω, Y ω ^ 2 ∂μ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlambdaBoundX (sq_nonneg q.1),
      mul_le_mul_of_nonneg_left hlambdaBoundY (sq_nonneg q.2)]
  calc
    ‖rowCharacteristic μ (fun ω => d * projection X Y q ω) ^ N‖ ≤
        Real.exp (-((N : ℝ) * ∫ ω, (d * projection X Y q ω) ^ 2 ∂μ) / 4) := by
      convert! h using 1
      simp only [projection, Pi.mul_apply, Pi.add_apply, neg_mul]
    _ ≤ Real.exp (-(lambdaBound * (q.1 ^ 2 + q.2 ^ 2)) / 4) := by
      apply Real.exp_le_exp.mpr
      rw [hv]
      linarith
    _ = Real.exp (-(lambdaBound / 4) * q.1 ^ 2) * Real.exp (-(lambdaBound / 4) * q.2 ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

def originRegion (d : ℝ) : Set (ℝ × ℝ) :=
  {q | d * (|q.1| + |q.2|) ≤ (1 : ℝ) / 4}

lemma measurableSet_originRegion (d : ℝ) : MeasurableSet (originRegion d) := by
  exact measurableSet_le (by fun_prop) measurable_const

def originIntegrand (μ : Measure Ω) (X Y : Ω → ℝ)
    (N : ℕ) (d : ℝ) (g : ℝ → ℂ) (a b : ℝ) (q : ℝ × ℝ) : ℂ :=
  (originRegion d).indicator (fun q =>
    g (d * q.1) * phase (a * q.1 + b * q.2) *
      rowCharacteristic μ (fun ω => d * projection X Y q ω) ^ N) q

theorem tendsto_origin_integral
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (X Y : ℕ → Ω → ℝ) (N : ℕ → ℕ) (d a b : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hb : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ 1 ∧ |Y n ω| ≤ 1)
    (hXm : ∀ n, ∫ ω, X n ω ∂μ n = 0)
    (hYm : ∀ n, ∫ ω, Y n ω ∂μ n = 0)
    (hXY : ∀ n, ∫ ω, X n ω * Y n ω ∂μ n = 0)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Tendsto d atTop (𝓝 0))
    (hscale : ∀ n, (N n : ℝ) * d n ^ 2 = 1)
    (ha : Tendsto a atTop (𝓝 0)) (hbshift : Tendsto b atTop (𝓝 0))
    {vX vY lambdaBound : ℝ} (hlambdaBound : 0 < lambdaBound)
    (hlambdaBoundX : ∀ n, lambdaBound ≤ ∫ ω, X n ω ^ 2 ∂μ n)
    (hlambdaBoundY : ∀ n, lambdaBound ≤ ∫ ω, Y n ω ^ 2 ∂μ n)
    (hvX : Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂μ n) atTop (𝓝 vX))
    (hvY : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂μ n) atTop (𝓝 vY))
    {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hgB : ∀ t, ‖g t‖ ≤ B) :
    Tendsto (fun n => ∫ q, originIntegrand (μ n) (X n) (Y n)
      (N n) (d n) g (a n) (b n) q ∂(volume.prod volume)) atTop
      (𝓝 (g 0 * (∫ q, gaussian vX vY q ∂(volume.prod volume)))) := by
  let H : (ℝ × ℝ) → ℝ := fun q =>
    B * (Real.exp (-(lambdaBound / 4) * q.1 ^ 2) * Real.exp (-(lambdaBound / 4) * q.2 ^ 2))
  have hHi : Integrable H (volume.prod volume) :=
    ((integrable_exp_neg_mul_sq (show 0 < lambdaBound / 4 by linarith)).mul_prod
      (integrable_exp_neg_mul_sq (show 0 < lambdaBound / 4 by linarith))).const_mul B
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (originIntegrand (μ n) (X n) (Y n) (N n) (d n) g (a n) (b n))
      (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ (measurableSet_originRegion _)
    exact ((hg.comp (continuous_const.mul continuous_fst)).mul
      (continuous_phase.comp ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd)))).mul
      ((continuous_projection_characteristic (μ n) (hX n) (hY n) (d n)).pow
        (N n)) |>.measurable
  have hdom (n : ℕ) : ∀ᵐ q ∂(volume.prod volume),
      ‖originIntegrand (μ n) (X n) (Y n) (N n) (d n) g (a n) (b n) q‖ ≤ H q := by
    exact ae_of_all _ fun q => by
      by_cases hq : q ∈ originRegion (d n)
      · rw [originIntegrand, indicator_of_mem hq, norm_mul, norm_mul, norm_phase, mul_one]
        exact mul_le_mul (hgB _)
          (scaled_mixed_pow_gaussian_bound (μ n) (hX n) (hY n) (hb n)
            (hXm n) (hYm n) (hXY n) (hlambdaBoundX n) (hlambdaBoundY n) (N n)
            (hd0 n) (hscale n) q hq)
          (norm_nonneg _) hB
      · rw [originIntegrand, indicator_of_notMem hq, norm_zero]
        dsimp [H]
        positivity
  have hpoint : ∀ᵐ q ∂(volume.prod volume),
      Tendsto (fun n => originIntegrand (μ n) (X n) (Y n)
        (N n) (d n) g (a n) (b n) q) atTop (𝓝 (g 0 * gaussian vX vY q)) := by
    exact ae_of_all _ fun q => by
      have hregion : ∀ᶠ n in atTop, q ∈ originRegion (d n) := by
        have hsmall : Tendsto (fun n => d n * (|q.1| + |q.2|)) atTop (𝓝 0) := by
          simpa only [zero_mul] using hd.mul_const (|q.1| + |q.2|)
        exact (hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
          fun n hn => hn.le
      have hgq : Tendsto (fun n => g (d n * q.1)) atTop (𝓝 (g 0)) :=
        (hg.tendsto 0).comp (by simpa only [zero_mul] using hd.mul_const q.1)
      have hphase : Tendsto (fun n => phase (a n * q.1 + b n * q.2))
          atTop (𝓝 (1 : ℂ)) := by
        have harg := (ha.mul_const q.1).add (hbshift.mul_const q.2)
        have h := (continuous_phase.tendsto 0).comp
          (by simpa only [zero_mul, zero_add] using harg)
        convert! h using 1
        simp only [phase, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      have hp := tendsto_scaled_mixed_powers μ X Y N d hX hY hb hXm hYm hXY
        hd0 hd hscale hvX hvY q
      have h := (hgq.mul hphase).mul hp
      simp only [mul_one] at h
      apply h.congr'
      filter_upwards [hregion] with n hn
      change _ = (originRegion (d n)).indicator _ q
      exact (indicator_of_mem hn (fun q =>
        g (d n*q.1) * phase (a n*q.1+b n*q.2) *
          rowCharacteristic (μ n) (fun ω => d n * projection (X n) (Y n) q ω)^N n)).symm
  have hlim := tendsto_integral_of_dominated_convergence H hmeas hHi hdom hpoint
  simpa only [integral_const_mul] using hlim

theorem integral_gaussian_pair (vX vY : ℝ) :
    (∫ q, gaussian vX vY q ∂(volume.prod volume)) =
      ((Real.sqrt (Real.pi / (vX / 2)) * Real.sqrt (Real.pi / (vY / 2)) : ℝ) : ℂ) := by
  have hfactor : (fun q : ℝ × ℝ => gaussian vX vY q) =
      fun q => ((Real.exp (-(vX / 2) * q.1 ^ 2) : ℝ) : ℂ) *
        ((Real.exp (-(vY / 2) * q.2 ^ 2) : ℝ) : ℂ) := by
    funext q
    dsimp [gaussian]
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor]
  rw [integral_prod_mul (fun x : ℝ => ((Real.exp (-(vX/2)*x^2) : ℝ) : ℂ))
    (fun y : ℝ => ((Real.exp (-(vY/2)*y^2) : ℝ) : ℂ)), integral_complex_ofReal,
    integral_complex_ofReal, integral_gaussian, integral_gaussian]
  push_cast
  rfl

end FCAppendix.Affine.Uniform06.BoundedMixedGaussian
