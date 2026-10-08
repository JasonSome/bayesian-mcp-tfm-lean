import ProbabilityApproximation.ChenShao.NonuniformBerryEsseen

noncomputable section

namespace FCAppendix.BernoulliApproximation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

universe uι uΩ

theorem exists_nonuniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ) (B σ : ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i, ∫ ω, X i ω ∂μ = 0) →
        (∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ B) →
        0 < σ → (∑ i, variance (X i) μ) = σ ^ 2 →
        ∀ x : ℝ,
          |cdf (μ.map (fun ω ↦ (∑ i, X i ω) / σ)) x -
              cdf (gaussianReal 0 1) x| ≤ C * (B / σ) / (1 + |x| ^ 3) := by
  obtain ⟨C, hC, hBE⟩ := nonuniformBerryEsseen.{uι, uΩ}
  refine ⟨C, hC, ?_⟩
  intro ι Ω _ _ μ _ X B σ hXm hXi hX0 hXB hσ hv x
  let Y : ι → Ω → ℝ := fun i ω => X i ω / σ
  have hYm : ∀ i, Measurable (Y i) := fun i => (hXm i).div_const σ
  have hYi : iIndepFun Y μ := by
    exact hXi.comp (fun (_ : ι) (x : ℝ) => x / σ) (fun _ => measurable_id.div_const σ)
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [Y, integral_div, hX0, zero_div]
  have hYB : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ B / σ := by
    intro i
    filter_upwards [hXB i] with ω hω
    simpa only [Y, abs_div, abs_of_pos hσ] using
      div_le_div_of_nonneg_right hω hσ.le
  have hY3 : ∀ i, MemLp (Y i) 3 μ := by
    intro i
    exact MemLp.of_bound (hYm i).aestronglyMeasurable (B / σ)
      (by simpa only [Real.norm_eq_abs] using hYB i)
  have hYv : (∑ i, variance (Y i) μ) = 1 := by
    simp only [Y, div_eq_mul_inv, variance_mul_const]
    rw [← Finset.sum_mul, hv]
    field_simp
  have hthird : (∑ i, ∫ ω, |Y i ω| ^ 3 ∂μ) ≤ B / σ := by
    calc
      _ ≤ ∑ i, (B / σ) * variance (Y i) μ := by
        apply Finset.sum_le_sum
        intro i _
        have hY2 : MemLp (Y i) 2 μ := (hY3 i).mono_exponent (by norm_num)
        calc
          _ ≤ ∫ ω, (B / σ) * (Y i ω) ^ 2 ∂μ := by
            apply integral_mono_ae
            · simpa only [Real.norm_eq_abs] using
                (hY3 i).integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)
            · exact hY2.integrable_sq.const_mul _
            · filter_upwards [hYB i] with ω hω
              calc
                |Y i ω| ^ 3 = |Y i ω| * (Y i ω) ^ 2 := by
                  rw [pow_succ, sq_abs, mul_comm]
                _ ≤ _ := mul_le_mul_of_nonneg_right hω (sq_nonneg _)
          _ = (B / σ) * variance (Y i) μ := by
            rw [integral_const_mul, variance_eq_integral (hYm i).aemeasurable]
            simp only [hY0, sub_zero]
      _ = B / σ := by rw [← Finset.mul_sum, hYv, mul_one]
  have hb := hBE μ Y hYm hYi hY0 hY3 hYv x
  have hs : (fun ω => ∑ i, Y i ω) = (fun ω => (∑ i, X i ω) / σ) := by
    funext ω
    exact (Finset.sum_div _ _ _).symm
  rw [hs] at hb
  exact hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hthird hC.le)
    (by positivity))

section Bernoulli

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

lemma bernoulli_mem_Icc {X : Ω → ℝ} (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1 := by
  filter_upwards [hX] with ω hω
  rcases hω with hω | hω <;> simp [hω]

lemma memLp_bernoulli {X : Ω → ℝ} (hXm : Measurable X)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) (q : ENNReal) : MemLp X q μ :=
  memLp_of_bounded (bernoulli_mem_Icc hX) hXm.aestronglyMeasurable q

lemma bernoulli_mean_mem_Icc {X : Ω → ℝ} (hXm : Measurable X)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    (∫ ω, X ω ∂μ) ∈ Set.Icc 0 1 := by
  have hi : Integrable X μ := (memLp_bernoulli hXm hX 1).integrable le_rfl
  have hr := bernoulli_mem_Icc hX
  refine ⟨integral_nonneg_of_ae (hr.mono fun _ h => h.1), ?_⟩
  have hh := integral_mono_ae hi (integrable_const (1 : ℝ)) (hr.mono fun _ h => h.2)
  simpa using hh

lemma bernoulli_variance {X : Ω → ℝ} (hXm : Measurable X)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    variance X μ = (∫ ω, X ω ∂μ) * (1 - ∫ ω, X ω ∂μ) := by
  rw [variance_eq_sub (memLp_bernoulli hXm hX 2)]
  have hs : (fun ω => (X ω) ^ 2) =ᵐ[μ] X := by
    filter_upwards [hX] with ω hω
    rcases hω with hω | hω <;> simp [hω]
  simp only [Pi.pow_apply]
  rw [integral_congr_ae hs]
  ring

end Bernoulli

theorem exists_bernoulli_nonuniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ι → Ω → ℝ) (σ : ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1) → 0 < σ →
        (∑ i, (∫ ω, X i ω ∂μ) * (1 - ∫ ω, X i ω ∂μ)) = σ ^ 2 →
        ∀ x : ℝ,
          |cdf (μ.map (fun ω ↦ (∑ i, (X i ω - ∫ ω', X i ω' ∂μ)) / σ)) x -
              cdf (gaussianReal 0 1) x| ≤ C / σ / (1 + |x| ^ 3) := by
  obtain ⟨C, hC, hBE⟩ := exists_nonuniform_bound.{uι, uΩ}
  refine ⟨C, hC, ?_⟩
  intro ι Ω _ _ μ _ X σ hXm hXi hX hσ hv x
  let Y : ι → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂μ
  have hYm : ∀ i, Measurable (Y i) := fun i => (hXm i).sub_const _
  have hYi : iIndepFun Y μ :=
    hXi.comp (fun i x => x - ∫ ω, X i ω ∂μ) (fun _ => measurable_id.sub_const _)
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    have hi := (memLp_bernoulli (hXm i) (hX i) 1).integrable le_rfl
    simp only [Y, integral_sub hi (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hY1 : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 := by
    intro i
    have hp := bernoulli_mean_mem_Icc (hXm i) (hX i)
    filter_upwards [bernoulli_mem_Icc (hX i)] with ω hω
    exact abs_le.mpr ⟨by dsimp [Y]; linarith [hp.2, hω.1],
      by dsimp [Y]; linarith [hp.1, hω.2]⟩
  have hYv : (∑ i, variance (Y i) μ) = σ ^ 2 := by
    convert hv using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show Y i = fun ω => X i ω - ∫ ω', X i ω' ∂μ from rfl,
      variance_sub_const (hXm i).aestronglyMeasurable, bernoulli_variance (hXm i) (hX i)]
  have hb := hBE μ Y 1 σ hYm hYi hY0 hY1 hσ hYv x
  simpa only [Y, mul_one_div] using hb

section TriangularRows

variable {ι : ℕ → Type uι} {Ω : ℕ → Type uΩ}
  [∀ n, Fintype (ι n)] [∀ n, MeasurableSpace (Ω n)]
  (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
  (X : (n : ℕ) → ι n → Ω n → ℝ) (σ : ℕ → ℝ)

theorem bernoulli_cdf_error_tendsto_zero
    (hXm : ∀ n i, Measurable (X n i)) (hXi : ∀ n, iIndepFun (X n) (μ n))
    (hX : ∀ n i, ∀ᵐ ω ∂μ n, X n i ω = 0 ∨ X n i ω = 1)
    (hv : ∀ n, (∑ i, (∫ ω, X n i ω ∂μ n) * (1 - ∫ ω, X n i ω ∂μ n)) = σ n ^ 2)
    (hσ : Tendsto σ atTop atTop) (x : ℕ → ℝ) :
    Tendsto (fun n =>
      |cdf ((μ n).map (fun ω ↦ (∑ i, (X n i ω - ∫ ω', X n i ω' ∂μ n)) / σ n)) (x n) -
        cdf (gaussianReal 0 1) (x n)|) atTop (𝓝 0) := by
  obtain ⟨C, hC, hBE⟩ := exists_bernoulli_nonuniform_bound.{uι, uΩ}
  have hlim : Tendsto (fun n => C / σ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hσ
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
  filter_upwards [hσ.eventually (eventually_gt_atTop 0)] with n hn
  have hb := hBE (μ n) (X n) (σ n) (hXm n) (hXi n) (hX n) hn (hv n) (x n)
  exact hb.trans (div_le_self (div_nonneg hC.le hn.le)
    (by have := pow_nonneg (abs_nonneg (x n)) 3; linarith))

theorem bernoulli_cdf_tendsto_gaussian
    (hXm : ∀ n i, Measurable (X n i)) (hXi : ∀ n, iIndepFun (X n) (μ n))
    (hX : ∀ n i, ∀ᵐ ω ∂μ n, X n i ω = 0 ∨ X n i ω = 1)
    (hv : ∀ n, (∑ i, (∫ ω, X n i ω ∂μ n) * (1 - ∫ ω, X n i ω ∂μ n)) = σ n ^ 2)
    (hσ : Tendsto σ atTop atTop) (x : ℝ) :
    Tendsto (fun n =>
      cdf ((μ n).map (fun ω ↦ (∑ i, (X n i ω - ∫ ω', X n i ω' ∂μ n)) / σ n)) x)
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have hh := bernoulli_cdf_error_tendsto_zero μ X σ hXm hXi hX hv hσ (fun _ => x)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hh)

end TriangularRows

end FCAppendix.BernoulliApproximation
