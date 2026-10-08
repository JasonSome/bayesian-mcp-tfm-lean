import FCAppendix.Probability.CorrelationMatrix
import FCAppendix.Probability.CorrelatedLoads

noncomputable section

namespace FCAppendix.BernoulliPairs

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {N : ℕ}

def pair (X : Fin N → Fin 2 → Ω → ℝ) (i : Fin N) (ω : Ω) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j => X i j ω)

def normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ) (i : Fin N) (ω : Ω) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j => (X i j ω - p) / σ)

lemma measurable_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j)) (i : Fin N) : Measurable (normalized X p σ i) := by
  unfold normalized
  fun_prop

omit [IsProbabilityMeasure μ] in
lemma indep_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXi : iIndepFun (pair X) μ) : iIndepFun (normalized X p σ) μ := by
  change iIndepFun (fun i ω => WithLp.toLp 2 (fun j => (X i j ω - p) / σ)) μ
  have hh := hXi.comp
    (fun (_ : Fin N) (x : EuclideanSpace ℝ (Fin 2)) =>
      WithLp.toLp 2 (fun j => (x j - p) / σ)) (fun _ => by fun_prop)
  simpa only [Function.comp_def, pair, normalized, WithLp.ofLp_toLp] using hh

lemma memLp_normalized_coordinate (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (q : ENNReal) (i : Fin N) (j : Fin 2) :
    MemLp (fun ω => normalized X p σ i ω j) q μ := by
  simpa only [normalized, WithLp.ofLp_toLp, div_eq_mul_inv, Pi.sub_apply] using
    ((BernoulliApproximation.memLp_bernoulli (hXm i j) (hX i j) q).sub
      (memLp_const p)).mul_const σ⁻¹

lemma memLp_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (q : ENNReal) (i : Fin N) : MemLp (normalized X p σ i) q μ :=
  MemLp.of_eval_piLp (memLp_normalized_coordinate X p σ hXm hX q i)

lemma integral_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (i : Fin N) :
    ∫ ω, normalized X p σ i ω ∂μ = 0 := by
  ext j
  rw [eval_integral_piLp (fun j =>
    (memLp_normalized_coordinate X p σ hXm hX 1 i j).integrable le_rfl)]
  simp only [normalized, WithLp.ofLp_toLp, integral_div]
  rw [integral_sub ((BernoulliApproximation.memLp_bernoulli (hXm i j) (hX i j) 1).integrable le_rfl)
    (integrable_const _), hm]
  simp

omit [IsProbabilityMeasure μ] in

lemma norm_normalized_le (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hσ : 0 < σ)
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1) (i : Fin N) :
    ∀ᵐ ω ∂μ, ‖normalized X p σ i ω‖ ≤ 2 / σ := by
  filter_upwards [ae_all_iff.mpr (hX i)] with ω hω
  have hc (j : Fin 2) : |X i j ω - p| ≤ 1 := by
    rcases hω j with hj | hj <;> rw [hj] <;> apply abs_le.mpr <;> constructor <;> linarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 / σ)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, normalized, WithLp.ofLp_toLp]
  have h0 : (X i 0 ω - p) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hc 0)
  have h1 : (X i 1 ω - p) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hc 1)
  rw [div_pow, div_pow, div_pow]
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hσ)).mpr
  nlinarith

lemma covariance_normalized_coordinate (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (i : Fin N) (j k : Fin 2) :
    covariance (fun ω => normalized X p σ i ω j)
      (fun ω => normalized X p σ i ω k) μ = covariance (X i j) (X i k) μ / σ ^ 2 := by
  simp only [normalized, WithLp.ofLp_toLp]
  rw [covariance_fun_div_left, covariance_fun_div_right,
    covariance_sub_const_left ((BernoulliApproximation.memLp_bernoulli (hXm i j) (hX i j) 1).integrable le_rfl),
    covariance_sub_const_right ((BernoulliApproximation.memLp_bernoulli (hXm i k) (hX i k) 1).integrable le_rfl)]
  ring

lemma covarianceBilin_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (i : Fin N)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin (μ.map (normalized X p σ i)) x y =
      (p * (1 - p) / σ ^ 2) * (x 0 * y 0 + x 1 * y 1) +
        (covariance (X i 0) (X i 1) μ / σ ^ 2) * (x 0 * y 1 + x 1 * y 0) := by
  have h := covarianceBilin_apply_pi (memLp_normalized_coordinate X p σ hXm hX 2 i) x y
  have he : (fun ω => WithLp.toLp 2 (fun j => normalized X p σ i ω j)) =
      normalized X p σ i := rfl
  rw [he] at h
  rw [h]
  simp only [Fin.sum_univ_two, covariance_normalized_coordinate X p σ hXm hX]
  have hswap : covariance (X i 1) (X i 0) μ = covariance (X i 0) (X i 1) μ := covariance_comm _ _
  rw [covariance_self (hXm i 0).aemeasurable, covariance_self (hXm i 1).aemeasurable,
    BernoulliApproximation.bernoulli_variance (hXm i 0) (hX i 0),
    BernoulliApproximation.bernoulli_variance (hXm i 1) (hX i 1), hm, hm, hswap]
  ring

theorem covarianceBilin_sum_normalized (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (hXi : iIndepFun (pair X) μ)
    (hσ : 0 < σ) (hvar : (N : ℝ) * p * (1 - p) = σ ^ 2)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    covarianceBilin (μ.map (fun ω => ∑ i, normalized X p σ i ω)) x y =
      x ⬝ᵥ CorrelationMatrix.corr ((∑ i, covariance (X i 0) (X i 1) μ) / σ ^ 2) *ᵥ y := by
  rw [covarianceBilin_map_sum_eq_sum (memLp_normalized X p σ hXm hX 2)
    (indep_normalized X p σ hXi)]
  simp_rw [covarianceBilin_normalized X p σ hXm hX hm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  simp [CorrelationMatrix.corr, dotProduct, mulVec, Fin.sum_univ_two]
  have hσ0 : σ ≠ 0 := hσ.ne'
  field_simp
  rw [hvar]
  ring

lemma corr_posSemidef_sum (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (hXi : iIndepFun (pair X) μ)
    (hσ : 0 < σ) (hvar : (N : ℝ) * p * (1 - p) = σ ^ 2) :
    (CorrelationMatrix.corr ((∑ i, covariance (X i 0) (X i 1) μ) / σ ^ 2)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (CorrelationMatrix.corr_hermitian _)
  intro x
  have h := covarianceBilin_self_nonneg
    (μ := μ.map (fun ω => ∑ i, normalized X p σ i ω)) (WithLp.toLp 2 x)
  rw [covarianceBilin_sum_normalized X p σ hXm hX hm hXi hσ hvar] at h
  simpa using h

def load (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ) (j : Fin 2) (ω : Ω) : ℝ :=
  (∑ i, normalized X p σ i ω) j

lemma memLp_load (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (q : ENNReal) (j : Fin 2) : MemLp (load X p σ j) q μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ => memLp_normalized X p σ hXm hX q i)).eval_piLp j

lemma integral_load (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (j : Fin 2) :
    ∫ ω, load X p σ j ω ∂μ = 0 := by
  have hvec : ∫ ω, ∑ i, normalized X p σ i ω ∂μ = 0 := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (memLp_normalized X p σ hXm hX 1 i).integrable le_rfl)]
    simp only [integral_normalized X p σ hXm hX hm, Finset.sum_const_zero]
  have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x j) hvec
  rw [eval_integral_piLp (fun k => (memLp_load X p σ hXm hX 1 k).integrable le_rfl)] at hh
  exact hh

theorem covariance_load (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (hXi : iIndepFun (pair X) μ)
    (hσ : 0 < σ) (hvar : (N : ℝ) * p * (1 - p) = σ ^ 2) (j k : Fin 2) :
    covariance (load X p σ j) (load X p σ k) μ =
      CorrelationMatrix.corr ((∑ i, covariance (X i 0) (X i 1) μ) / σ ^ 2) j k := by
  rw [← covarianceBilin_apply_basisFun (memLp_load X p σ hXm hX 2)]
  have he : (fun ω => WithLp.toLp 2 (fun j => load X p σ j ω)) =
      (fun ω => ∑ i, normalized X p σ i ω) := by
    funext ω
    rfl
  rw [he, covarianceBilin_sum_normalized X p σ hXm hX hm hXi hσ hvar]
  fin_cases j <;> fin_cases k <;>
    simp [CorrelationMatrix.corr, dotProduct, mulVec, EuclideanSpace.basisFun_apply]

lemma variance_load (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p) (hXi : iIndepFun (pair X) μ)
    (hσ : 0 < σ) (hvar : (N : ℝ) * p * (1 - p) = σ ^ 2) (j : Fin 2) :
    variance (load X p σ j) μ = 1 := by
  rw [← covariance_self (memLp_load X p σ hXm hX 2 j).aemeasurable,
    covariance_load X p σ hXm hX hm hXi hσ hvar]
  fin_cases j <;> simp [CorrelationMatrix.corr]

theorem correlation_bounds (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ)
    (hXm : ∀ i j, Measurable (X i j))
    (hX : ∀ i j, ∀ᵐ ω ∂μ, X i j ω = 0 ∨ X i j ω = 1)
    (hm : ∀ i j, ∫ ω, X i j ω ∂μ = p)
    (hp0 : 0 < p) (hp1 : p < 1) (hσ : 0 < σ)
    (hvar : (N : ℝ) * p * (1 - p) = σ ^ 2) :
    -p / (1 - p) ≤ (∑ i, covariance (X i 0) (X i 1) μ) / σ ^ 2 ∧
      (∑ i, covariance (X i 0) (X i 1) μ) / σ ^ 2 ≤ 1 := by
  have hd : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hpair (i : Fin N) := CorrelatedLoads.bernoulli_correlation_bounds
    (X i 0) (X i 1) (hXm i 0) (hXm i 1) (hX i 0) (hX i 1)
    p hp0 hp1 (hm i 0) (hm i 1)
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (le_div_iff₀ hd).mp (hpair i).1)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    calc
      _ = (N : ℝ) * (-p / (1 - p) * (p * (1 - p))) := by rw [← hvar]; ring
      _ ≤ _ := hb
  · apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (div_le_iff₀ hd).mp (hpair i).2)
    simpa only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, hvar] using hb

omit [IsProbabilityMeasure μ] in

lemma indep_coordinate (X : Fin N → Fin 2 → Ω → ℝ)
    (hXi : iIndepFun (pair X) μ) (j : Fin 2) :
    iIndepFun (fun i => X i j) μ := by
  simpa only [Function.comp_def, pair, WithLp.ofLp_toLp] using
    hXi.comp (fun (_ : Fin N) (x : EuclideanSpace ℝ (Fin 2)) => x j)
      (fun _ => by fun_prop)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma load_eq (X : Fin N → Fin 2 → Ω → ℝ) (p σ : ℝ) (j : Fin 2) (ω : Ω) :
    load X p σ j ω = (∑ i, (X i j ω - p)) / σ := by
  simp [load, normalized, ← Finset.sum_div]

lemma eventually_pos_of_compact_subsequences (r P : ℕ → ℝ) (l u : ℝ)
    (hr : ∀ᶠ n in atTop, r n ∈ Set.Icc l u) (hP : ∀ n, 0 ≤ P n)
    (hsub : ∀ f : ℕ → ℕ, Tendsto f atTop atTop → ∀ r₀ : ℝ,
      Tendsto (r ∘ f) atTop (𝓝 r₀) → ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤ P (f n)) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤ P n := by
  classical
  by_contra hnot
  have hex : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ P n < 1 / ((k : ℝ) + 1) := by
    intro k
    have hbad : ¬ ∀ᶠ n in atTop, 1 / ((k : ℝ) + 1) ≤ P n := by
      intro hn
      exact hnot ⟨1 / ((k : ℝ) + 1), by positivity, hn⟩
    simp only [eventually_atTop] at hbad
    push Not at hbad
    exact hbad k
  choose s hs hsmall using hex
  have hstop : Tendsto s atTop atTop := tendsto_atTop_mono hs tendsto_id
  have hs0 : Tendsto (P ∘ s) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hP (s n)) (fun n => (hsmall n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨r₀, _, f, hf, hrf⟩ := isCompact_Icc.isSeqCompact.subseq_of_frequently_in
    (hstop.eventually hr).frequently
  obtain ⟨q, hq, hqp⟩ := hsub (s ∘ f) (hstop.comp hf.tendsto_atTop) r₀ hrf
  have hq0 : q ≤ 0 := ge_of_tendsto (hs0.comp hf.tendsto_atTop) hqp
  linarith

section Rows

variable {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (μ' : (n : ℕ) → Measure (Ω' n)) [∀ n, IsProbabilityMeasure (μ' n)]
    (N' : ℕ → ℕ) (X' : (n : ℕ) → Fin (N' n) → Fin 2 → Ω' n → ℝ)
    (p' σ' : ℕ → ℝ)

theorem load_cdf_tendsto_gaussian
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσ : Tendsto σ' atTop atTop) (j : Fin 2) (a : ℝ) :
    Tendsto (fun n => (μ' n).real {ω | load (X' n) (p' n) (σ' n) j ω ≤ a})
      atTop (𝓝 (cdf (gaussianReal 0 1) a)) := by
  have hv : ∀ n, (∑ i, (∫ ω, X' n i j ω ∂μ' n) *
      (1 - ∫ ω, X' n i j ω ∂μ' n)) = σ' n ^ 2 := by
    intro n
    simpa only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc] using hvar n
  have h := BernoulliApproximation.bernoulli_cdf_tendsto_gaussian μ'
    (fun n i => X' n i j) σ' (fun n i => hXm n i j)
    (fun n => indep_coordinate (X' n) (hXi n) j) (fun n i => hX n i j) hv hσ a
  have he (n : ℕ) : (fun ω => (∑ i, (X' n i j ω - ∫ ω', X' n i j ω' ∂μ' n)) / σ' n) =
      load (X' n) (p' n) (σ' n) j := by
    funext ω
    simp only [hm, load_eq]
  simp_rw [he] at h
  convert h using 1
  funext n
  have hmload := (memLp_load (X' n) (p' n) (σ' n) (hXm n) (hX n) 2 j).aemeasurable
  haveI := Measure.isProbabilityMeasure_map hmload
  simp only [cdf_eq_real, Measure.real, Measure.map_apply_of_aemeasurable hmload measurableSet_Iic]
  rfl

theorem eventually_joint_pos_of_correlation_one
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hσ : ∀ n, 0 < σ' n)
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop)
    (hr : Tendsto (fun n => (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2)
      atTop (𝓝 1)) (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n) :
    ∀ᶠ n in atTop, cdf (gaussianReal 0 1) (a - 1) / 2 ≤
      (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
        load (X' n) (p' n) (σ' n) 1 ω ≤ t n} := by
  apply CorrelatedLoads.eventually_joint_pos_of_covariance_tendsto_one μ'
    (fun n => load (X' n) (p' n) (σ' n) 0) (fun n => load (X' n) (p' n) (σ' n) 1)
    (fun n => memLp_load _ _ _ (hXm n) (hX n) 2 0)
    (fun n => memLp_load _ _ _ (hXm n) (hX n) 2 1)
    (fun n => integral_load _ _ _ (hXm n) (hX n) (hm n) 0)
    (fun n => integral_load _ _ _ (hXm n) (hX n) (hm n) 1)
    (fun n => variance_load _ _ _ (hXm n) (hX n) (hm n) (hXi n) (hσ n) (hvar n) 0)
    (fun n => variance_load _ _ _ (hXm n) (hX n) (hm n) (hXi n) (hσ n) (hvar n) 1)
    ?_ a t ht
    (load_cdf_tendsto_gaussian μ' N' X' p' σ' hXm hX hm hXi hvar hσlim 0 (a - 1))
  simpa only [covariance_load _ _ _ (hXm _) (hX _) (hm _) (hXi _) (hσ _) (hvar _),
    CorrelationMatrix.corr, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    using hr

theorem moment_error_tendsto_zero
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1) (K : ℝ) :
    Tendsto (fun n => (N' n : ℝ) * (K * (2 / σ' n)) ^ 3) atTop (𝓝 0) := by
  have hden : p₀ * (1 - p₀) ≠ 0 := ne_of_gt (mul_pos hp₀ (sub_pos.mpr hp₁))
  have hd : Tendsto (fun n => p' n * (1 - p' n)) atTop (𝓝 (p₀ * (1 - p₀))) :=
    hp.mul (tendsto_const_nhds.sub hp)
  have hh := ((tendsto_const_nhds.div hd hden).mul
    (tendsto_inv_atTop_zero.comp hσlim) :
    Tendsto (fun n => (8 * K ^ 3 / (p' n * (1 - p' n))) * (σ' n)⁻¹)
      atTop (𝓝 ((8 * K ^ 3 / (p₀ * (1 - p₀))) * 0)))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_gt_nhds hp₀),
    hp.eventually (eventually_lt_nhds hp₁), hσlim.eventually_gt_atTop 0] with n hn0 hn1 hnσ
  have h0 : p' n ≠ 0 := ne_of_gt hn0
  have h1 : 1 - p' n ≠ 0 := ne_of_gt (sub_pos.mpr hn1)
  have hs : σ' n ≠ 0 := ne_of_gt hnσ
  dsimp only [Pi.div_apply]
  field_simp [h0, h1, hs]
  nlinarith [congrArg (fun z : ℝ => 8 * K ^ 3 * z) (hvar n)]

theorem whitening_error_tendsto_zero
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1)
    {r : ℕ → ℝ} {r₀ : ℝ} (hr : Tendsto r atTop (𝓝 r₀)) (hr₀ : |r₀| < 1) :
    Tendsto (fun n => (N' n : ℝ) *
      (‖bentkusWhiteningCLM (CorrelationMatrix.corr (r n))‖ * (2 / σ' n)) ^ 3)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := CorrelationMatrix.eventually_corr_whitening_bounded hr hr₀
  apply squeeze_zero'
  · filter_upwards [hσlim.eventually_gt_atTop 0] with n hn
    positivity
  · filter_upwards [hb, hσlim.eventually_gt_atTop 0] with n hn hσn
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hn.2 (by positivity)) 3) (by positivity)
  · exact moment_error_tendsto_zero N' p' σ' hvar hσlim hp hp₀ hp₁ K

theorem eventually_joint_pos_of_nondegenerate_correlation
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hσ : ∀ n, 0 < σ' n)
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ r₀ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1)
    (hr : Tendsto (fun n => (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2)
      atTop (𝓝 r₀)) (hr₀ : |r₀| < 1)
    (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤
      (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
        load (X' n) (p' n) (σ' n) 1 ω ≤ t n} := by
  let r : ℕ → ℝ := fun n =>
    (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2
  let S := fun n => CorrelationMatrix.corr (r n)
  have hlim : Tendsto S atTop (𝓝 (CorrelationMatrix.corr r₀)) := by
    have hc : Continuous CorrelationMatrix.corr := by
      unfold CorrelationMatrix.corr
      fun_prop
    exact (hc.tendsto r₀).comp hr
  have hPSD : ∀ n, (S n).PosSemidef := fun n =>
    corr_posSemidef_sum _ _ _ (hXm n) (hX n) (hm n) (hXi n) (hσ n) (hvar n)
  have hPD : ∀ᶠ n in atTop, (S n).PosDef := by
    filter_upwards [hr.abs.eventually (eventually_lt_nhds hr₀)] with n hn
    exact CorrelationMatrix.corr_posDef hn
  obtain ⟨q, hq, hgauss⟩ := BoundedVectorApproximation.eventually_gaussian_lowerOrthant_pos
    S (CorrelationMatrix.corr r₀) hPSD (CorrelationMatrix.corr_posDef hr₀) hlim (fun _ => a)
  obtain ⟨C, hC, hBE⟩ := BoundedVectorApproximation.exists_bounded_convex_bound
  have herr := whitening_error_tendsto_zero N' p' σ' hvar hσlim hp hp₀ hp₁ hr hr₀
  have he0 : Tendsto (fun n => C * (2 : ℝ) ^ (1 / 4 : ℝ) *
      ((N' n : ℝ) * (‖bentkusWhiteningCLM (S n)‖ * (2 / σ' n)) ^ 3))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using herr.const_mul (C * (2 : ℝ) ^ (1 / 4 : ℝ))
  have hsmall := he0.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < q / 2))
  refine ⟨q / 2, by linarith, ?_⟩
  filter_upwards [hgauss, hsmall, ht, hPD, hp.eventually (eventually_gt_nhds hp₀),
    hp.eventually (eventually_lt_nhds hp₁)] with n hgn hsn htn hPDn hp0n hp1n
  let Y := normalized (X' n) (p' n) (σ' n)
  have hYm : ∀ i, Measurable (Y i) := measurable_normalized _ _ _ (hXm n)
  have hsum : Measurable (fun ω => ∑ i, Y i ω) :=
    Finset.measurable_sum _ (fun i _ => hYm i)
  haveI : IsProbabilityMeasure ((μ' n).map (fun ω => ∑ i, Y i ω)) :=
    Measure.isProbabilityMeasure_map hsum.aemeasurable
  have hb := hBE (by norm_num : 0 < 2) (μ' n) Y (S n) (2 / σ' n) hYm
    (norm_normalized_le _ _ _ hp0n.le hp1n.le (hσ n) (hX n))
    (indep_normalized _ _ _ (hXi n)) (integral_normalized _ _ _ (hXm n) (hX n) (hm n))
    hPDn (covarianceBilin_sum_normalized _ _ _ (hXm n) (hX n) (hm n) (hXi n) (hσ n) (hvar n))
    (BoundedVectorApproximation.lowerOrthant (fun _ => a))
    (BoundedVectorApproximation.measurableSet_lowerOrthant _)
    (BoundedVectorApproximation.convex_lowerOrthant _)
  have hlow : q / 2 ≤ ((μ' n).map (fun ω => ∑ i, Y i ω)).real
      (BoundedVectorApproximation.lowerOrthant (fun _ => a)) := by
    have hl := (abs_le.mp hb).1
    nlinarith
  have hmon := hlow.trans (measureReal_mono (μ := (μ' n).map (fun ω => ∑ i, Y i ω))
    (show BoundedVectorApproximation.lowerOrthant (fun _ => a) ⊆
      BoundedVectorApproximation.lowerOrthant (fun _ => t n) from fun _ hx j => (hx j).trans htn))
  have he : (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
      load (X' n) (p' n) (σ' n) 1 ω ≤ t n} =
      ((μ' n).map (fun ω => ∑ i, Y i ω)).real
        (BoundedVectorApproximation.lowerOrthant (fun _ => t n)) := by
    simp only [Measure.real, Measure.map_apply hsum (BoundedVectorApproximation.measurableSet_lowerOrthant _)]
    congr 2
    ext ω
    change (_ ∧ _) ↔ ∀ j, (∑ i, Y i ω) j ≤ t n
    constructor
    · rintro ⟨h0, h1⟩ j
      fin_cases j
      · exact h0
      · exact h1
    · intro hh
      exact ⟨hh 0, hh 1⟩
  rw [he]
  exact hmon

theorem eventually_joint_pos_of_correlation_tendsto
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hσ : ∀ n, 0 < σ' n)
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ r₀ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1 / 2)
    (hr : Tendsto (fun n => (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2)
      atTop (𝓝 r₀))
    (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤
      (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
        load (X' n) (p' n) (σ' n) 1 ω ≤ t n} := by
  have hp₁' : p₀ < 1 := by linarith
  have hbounds : ∀ᶠ n in atTop,
      -p' n / (1 - p' n) ≤ (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2 ∧
      (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2 ≤ 1 := by
    filter_upwards [hp.eventually (eventually_gt_nhds hp₀),
      hp.eventually (eventually_lt_nhds hp₁')] with n hn0 hn1
    exact correlation_bounds _ _ _ (hXm n) (hX n) (hm n) hn0 hn1 (hσ n) (hvar n)
  have hlo : -p₀ / (1 - p₀) ≤ r₀ :=
    le_of_tendsto_of_tendsto (hp.neg.div (tendsto_const_nhds.sub hp) (by linarith)) hr
      (hbounds.mono fun _ h => h.1)
  have hhi : r₀ ≤ 1 := le_of_tendsto hr (hbounds.mono fun _ h => h.2)
  by_cases he : r₀ = 1
  · subst r₀
    exact ⟨cdf (gaussianReal 0 1) (a - 1) / 2,
      div_pos (CorrelatedLoads.gaussian_cdf_pos _) (by norm_num),
      eventually_joint_pos_of_correlation_one μ' N' X' p' σ' hXm hX hm hXi hσ hvar hσlim hr a t ht⟩
  · have hr₀ : |r₀| < 1 := abs_lt.mpr
      ⟨(CorrelatedLoads.correlation_lower_gt_neg_one hp₁).trans_le hlo, lt_of_le_of_ne hhi he⟩
    exact eventually_joint_pos_of_nondegenerate_correlation μ' N' X' p' σ' hXm hX hm hXi
      hσ hvar hσlim hp hp₀ hp₁' hr hr₀ a t ht

theorem eventually_joint_pos
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hσ : ∀ n, 0 < σ' n)
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1 / 2)
    (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤
      (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
        load (X' n) (p' n) (σ' n) 1 ω ≤ t n} := by
  let r : ℕ → ℝ := fun n =>
    (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2
  have hr : ∀ᶠ n in atTop, r n ∈ Set.Icc (-1) 1 := by
    filter_upwards [hp.eventually (eventually_gt_nhds hp₀),
      hp.eventually (eventually_lt_nhds hp₁)] with n hn0 hn1
    have hb := correlation_bounds _ _ _ (hXm n) (hX n) (hm n) hn0
      (by linarith : p' n < 1) (hσ n) (hvar n)
    exact ⟨(CorrelatedLoads.correlation_lower_gt_neg_one hn1).le.trans hb.1, hb.2⟩
  apply eventually_pos_of_compact_subsequences r _ (-1) 1 hr
    (fun _ => measureReal_nonneg)
  intro f hf r₀ hrf
  exact eventually_joint_pos_of_correlation_tendsto (fun n => μ' (f n))
    (fun n => N' (f n)) (fun n => X' (f n)) (fun n => p' (f n)) (fun n => σ' (f n))
    (fun n => hXm (f n)) (fun n => hX (f n)) (fun n => hm (f n)) (fun n => hXi (f n))
    (fun n => hσ (f n)) (fun n => hvar (f n)) (hσlim.comp hf) (hp.comp hf) hp₀ hp₁
    hrf a (fun n => t (f n)) (hf.eventually ht)

end Rows

end FCAppendix.BernoulliPairs
