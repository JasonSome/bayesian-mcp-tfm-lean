import FCAppendix.PayOnce.ActivePairCovariance

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

theorem integral_positive_pair_marginal_gap_tendsto_zero
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    {n : ℕ} (hn : 0 < n) (hm : ∀ t, 0 < Fintype.card (ι t))
    (A p : ∀ t, Ω t → ι t → ℝ)
    (hA : ∀ t i, Measurable (fun ω => A t ω i))
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0 : ℝ) 1)
    (hgap : Tendsto (fun t => ∫ ω, populationPairMean
      (fun i j => positiveMask (A t ω i)*positiveMask (A t ω j)*|success n (p t ω i)-success n (p t ω j)|) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationPairMean (fun i j => positiveMask (A t ω i)*positiveMask (A t ω j)*|p t ω i-p t ω j|) ∂P t)
      atTop (𝓝 0) := by
  have hpi t := integrable_populationPairMean (P t) (fun ω i j => positiveMask (A t ω i)*positiveMask (A t ω j)*|p t ω i-p t ω j|)
    (fun i j => integrable_positive_pair_gap (P t) (hA t i) (hA t j) (hp t i) (hp t j) (fun ω => hpb t ω i) (fun ω => hpb t ω j))
  have hsi t := integrable_populationPairMean (P t)
    (fun ω i j => positiveMask (A t ω i)*positiveMask (A t ω j)*|success n (p t ω i)-success n (p t ω j)|)
    (fun i j => integrable_positive_pair_gap (P t) (hA t i) (hA t j) ((continuous_success n).measurable.comp (hp t i))
      ((continuous_success n).measurable.comp (hp t j))
      (fun ω => success_mem_unit (hpb t ω i)) (fun ω => success_mem_unit (hpb t ω j)))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (integral_nonneg fun ω =>
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (positiveMask_bounds _).1 (positiveMask_bounds _).1) (abs_nonneg _)) (sq_nonneg _))
  · intro ε hε
    have ht : Tendsto (fun t => (∫ ω, populationPairMean
        (fun i j => positiveMask (A t ω i)*positiveMask (A t ω j)*|success n (p t ω i)-success n (p t ω j)|) ∂P t)/(ε/2)^n)
        atTop (𝓝 0) := by simpa only [zero_div] using hgap.div_const ((ε/2)^n)
    filter_upwards [ht.eventually_lt_const (half_pos hε)] with t ht'
    have hh := integral_mono (hpi t) (((hsi t).div_const ((ε/2)^n)).add (integrable_const (ε/2)))
      (fun ω => populationPairMean_le (hm t) (fun i j => by
        by_cases hi : 0 < A t ω i
        · by_cases hj : 0 < A t ω j
          · simp only [positiveMask,if_pos hi,if_pos hj,one_mul]
            have hh := gap_le_success_gap hn (hpb t ω i) (hpb t ω j) (half_pos hε)
            linarith
          · simp only [positiveMask,if_neg hj,mul_zero,zero_mul,zero_div,zero_add]
            exact (half_pos hε).le
        · simp only [positiveMask,if_neg hi,zero_mul,zero_div,zero_add]
          exact (half_pos hε).le))
    simp only [Pi.add_apply] at hh
    rw [integral_add ((hsi t).div_const _) (integrable_const _), integral_div, integral_const,
      probReal_univ, one_smul] at hh
    linarith

end FCAppendix.PayOnce.CovarianceConcentration
