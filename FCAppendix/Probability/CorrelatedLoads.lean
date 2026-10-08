import FCAppendix.Probability.BernoulliApproximation

namespace FCAppendix.CorrelatedLoads

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem joint_lower_of_difference_sq (X Y : Ω → ℝ) (a δ : ℝ) (hδ : 0 < δ)
    (hint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ) :
    μ.real {ω | X ω ≤ a - δ} - (∫ ω, (X ω - Y ω) ^ 2 ∂μ) / δ ^ 2 ≤
      μ.real {ω | X ω ≤ a ∧ Y ω ≤ a} := by
  have hcover : {ω | X ω ≤ a - δ} ⊆
      {ω | X ω ≤ a ∧ Y ω ≤ a} ∪ {ω | δ ^ 2 ≤ (X ω - Y ω) ^ 2} := by
    intro ω hω
    by_cases hd : δ ^ 2 ≤ (X ω - Y ω) ^ 2
    · exact Or.inr hd
    · left
      refine ⟨by dsimp only [mem_setOf_eq] at hω ⊢; linarith, ?_⟩
      by_contra hy
      have hyx : δ < Y ω - X ω := by dsimp only [mem_setOf_eq] at hω; linarith
      have hs := (sq_lt_sq₀ hδ.le (by linarith : 0 ≤ Y ω - X ω)).mpr hyx
      have hn := not_le.mp hd
      nlinarith
  have hprob := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - Y ω)) hint (δ ^ 2)
  have hsmall : μ.real {ω | δ ^ 2 ≤ (X ω - Y ω) ^ 2} ≤
      (∫ ω, (X ω - Y ω) ^ 2 ∂μ) / δ ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by nlinarith [hmarkov])
  linarith

theorem difference_sq_eq (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0)
    (hvX : variance X μ = 1) (hvY : variance Y μ = 1) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂μ) = 2 * (1 - covariance X Y μ) := by
  have hm : ∫ ω, X ω - Y ω ∂μ = 0 := by
    rw [integral_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num)), hmX, hmY]
    ring
  have hv := variance_fun_sub hX hY
  rw [variance_eq_integral (X := fun ω => X ω - Y ω) (hX.aemeasurable.sub hY.aemeasurable), hm, hvX, hvY] at hv
  simp only [sub_zero] at hv
  linarith

theorem joint_lower_of_covariance (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0)
    (hvX : variance X μ = 1) (hvY : variance Y μ = 1)
    (a δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | X ω ≤ a - δ} - 2 * (1 - covariance X Y μ) / δ ^ 2 ≤
      μ.real {ω | X ω ≤ a ∧ Y ω ≤ a} := by
  have h := joint_lower_of_difference_sq X Y a δ hδ (hX.sub hY).integrable_sq
  rwa [difference_sq_eq X Y hX hY hmX hmY hvX hvY] at h

theorem gaussian_cdf_pos (a : ℝ) : 0 < cdf (gaussianReal 0 1) a := by
  rw [cdf_eq_real]
  apply ENNReal.toReal_pos
  · intro h
    have hvol := gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0) h
    simp at hvol
  · exact measure_ne_top _ _

theorem bernoulli_correlation_bounds (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) (hY : ∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hmX : ∫ ω, X ω ∂μ = p) (hmY : ∫ ω, Y ω ∂μ = p) :
    -p / (1 - p) ≤ covariance X Y μ / (p * (1 - p)) ∧
      covariance X Y μ / (p * (1 - p)) ≤ 1 := by
  have hX2 := BernoulliApproximation.memLp_bernoulli hXm hX 2
  have hY2 := BernoulliApproximation.memLp_bernoulli hYm hY 2
  have hcov := covariance_eq_sub hX2 hY2
  rw [hmX, hmY] at hcov
  simp only [Pi.mul_apply] at hcov
  have hprod : 0 ≤ ∫ ω, X ω * Y ω ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [BernoulliApproximation.bernoulli_mem_Icc hX,
      BernoulliApproximation.bernoulli_mem_Icc hY] with ω hx hy
    exact mul_nonneg hx.1 hy.1
  have hvX : variance X μ = p * (1 - p) := by
    simpa only [hmX] using BernoulliApproximation.bernoulli_variance hXm hX
  have hvY : variance Y μ = p * (1 - p) := by
    simpa only [hmY] using BernoulliApproximation.bernoulli_variance hYm hY
  have hvar := variance_nonneg (fun ω => X ω - Y ω) μ
  rw [variance_fun_sub hX2 hY2, hvX, hvY] at hvar
  have hd : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  constructor
  · apply (le_div_iff₀ hd).mpr
    have he : -p / (1 - p) * (p * (1 - p)) = -p * p := by
      field_simp [show 1 - p ≠ 0 by linarith]
    rw [he]
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith

theorem correlation_lower_gt_neg_one {p : ℝ} (hp : p < 1 / 2) :
    -1 < -p / (1 - p) := by
  apply (lt_div_iff₀ (by linarith : 0 < 1 - p)).mpr
  linarith

section Rows

variable {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (μ' : (n : ℕ) → Measure (Ω' n)) [∀ n, IsProbabilityMeasure (μ' n)]
    (X Y : (n : ℕ) → Ω' n → ℝ)

theorem eventually_joint_pos_of_covariance_tendsto_one
    (hX : ∀ n, MemLp (X n) 2 (μ' n)) (hY : ∀ n, MemLp (Y n) 2 (μ' n))
    (hmX : ∀ n, ∫ ω, X n ω ∂μ' n = 0) (hmY : ∀ n, ∫ ω, Y n ω ∂μ' n = 0)
    (hvX : ∀ n, variance (X n) (μ' n) = 1) (hvY : ∀ n, variance (Y n) (μ' n) = 1)
    (hc : Tendsto (fun n => covariance (X n) (Y n) (μ' n)) atTop (𝓝 1))
    (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n)
    (hCDF : Tendsto (fun n => (μ' n).real {ω | X n ω ≤ a - 1}) atTop
      (𝓝 (cdf (gaussianReal 0 1) (a - 1)))) :
    ∀ᶠ n in atTop, cdf (gaussianReal 0 1) (a - 1) / 2 ≤
      (μ' n).real {ω | X n ω ≤ t n ∧ Y n ω ≤ t n} := by
  have hp := gaussian_cdf_pos (a - 1)
  have hdef : Tendsto (fun n => 2 * (1 - covariance (X n) (Y n) (μ' n)))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.sub hc).const_mul 2 using 1
    simp
  have hlim := hCDF.sub hdef
  simp only [sub_zero] at hlim
  have hev := hlim.eventually (eventually_gt_nhds (by linarith :
    cdf (gaussianReal 0 1) (a - 1) / 2 < cdf (gaussianReal 0 1) (a - 1)))
  filter_upwards [hev, ht] with n hn htn
  have hb := joint_lower_of_covariance (X n) (Y n) (hX n) (hY n)
    (hmX n) (hmY n) (hvX n) (hvY n) a 1 (by norm_num)
  simp only [one_pow, div_one] at hb
  exact le_trans (le_trans hn.le hb) (measureReal_mono (fun ω hω =>
    And.intro (hω.1.trans htn) (hω.2.trans htn)))

end Rows

end FCAppendix.CorrelatedLoads
