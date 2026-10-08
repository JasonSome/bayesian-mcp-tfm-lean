import FCAppendix.PayOnce.PopulationSampling
import FCAppendix.PayOnce.FocalProfileTransport

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CovarianceConcentration
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem profileAction_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (fun d : UserProfile m n => (d i).1)
      (userProfileLaw Γ) (Γ.F ⊗ₘ Γ.σ) :=
  (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).comp
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i)

theorem integral_profile_mean_action (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : ℝ × JointAction n → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, ‖f x‖ ≤ K) :
    (∫ d, populationMean (fun i => f (d i).1) ∂userProfileLaw Γ) =
      ∫ x, f x ∂(Γ.F ⊗ₘ Γ.σ) := by
  have hfi i : Integrable (fun d : UserProfile m n => f (d i).1) (userProfileLaw Γ) :=
    Integrable.of_bound (hf.comp (profileAction_measurePreserving Γ i).measurable).aestronglyMeasurable
      K (Filter.Eventually.of_forall fun d => hK (d i).1)
  have he i : (∫ d : UserProfile m n, f (d i).1 ∂userProfileLaw Γ) =
      ∫ x, f x ∂(Γ.F ⊗ₘ Γ.σ) := by
    have hp := profileAction_measurePreserving Γ i
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm
  rw [integral_populationMean _ _ hfi]
  simp only [he,populationMean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem integrable_populationMean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (f : Ω → ι → ℝ) (hf : ∀ i, Integrable (fun ω => f ω i) P) :
    Integrable (fun ω => populationMean (f ω)) P :=
  (integrable_finsetSum _ (fun i _ => hf i)).div_const _

theorem tendsto_population_gap_of_two_gaps
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (p q r : ∀ t, Ω t → ι t → ℝ)
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hq : ∀ t i, Measurable (fun ω => q t ω i))
    (hr : ∀ t i, Measurable (fun ω => r t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0:ℝ) 1)
    (hqb : ∀ t ω i, q t ω i ∈ Icc (0:ℝ) 1)
    (hrb : ∀ t ω i, r t ω i ∈ Icc (0:ℝ) 1)
    (h₁ : Tendsto (fun t => ∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t) atTop (𝓝 0))
    (h₂ : Tendsto (fun t => ∫ ω, populationMean (fun i => |q t ω i-r t ω i|) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationMean (fun i => |p t ω i-r t ω i|) ∂P t) atTop (𝓝 0) := by
  have hI₁ t := integrable_populationMean (P t) (fun ω i => |p t ω i-q t ω i|)
    (fun i => integrable_abs_gap (P t) (hp t i) (hq t i) (fun ω => hpb t ω i) (fun ω => hqb t ω i))
  have hI₂ t := integrable_populationMean (P t) (fun ω i => |q t ω i-r t ω i|)
    (fun i => integrable_abs_gap (P t) (hq t i) (hr t i) (fun ω => hqb t ω i) (fun ω => hrb t ω i))
  have hI₃ t := integrable_populationMean (P t) (fun ω i => |p t ω i-r t ω i|)
    (fun i => integrable_abs_gap (P t) (hp t i) (hr t i) (fun ω => hpb t ω i) (fun ω => hrb t ω i))
  have ht := h₁.add h₂
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => integral_nonneg fun _ =>
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)) _ ht
  intro t
  have hh := integral_mono (hI₃ t) ((hI₁ t).add (hI₂ t)) (fun ω => by
    change (∑ i, |p t ω i-r t ω i|)/(Fintype.card (ι t):ℝ) ≤
      (∑ i, |p t ω i-q t ω i|)/(Fintype.card (ι t):ℝ)+
        (∑ i, |q t ω i-r t ω i|)/(Fintype.card (ι t):ℝ)
    rw [← add_div,← Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => abs_sub_le _ _ _)
      (Nat.cast_nonneg _))
  have hadd : (∫ ω, populationMean (fun i => |p t ω i-q t ω i|)+
      populationMean (fun i => |q t ω i-r t ω i|) ∂P t) =
      (∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t)+
        ∫ ω, populationMean (fun i => |q t ω i-r t ω i|) ∂P t :=
    integral_add (hI₁ t) (hI₂ t)
  exact hh.trans_eq hadd

end FCAppendix.PayOnce.CovarianceConcentration

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem populationMean_abs_sub_le {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    |populationMean p-populationMean q| ≤ populationMean (fun i => |p i-q i|) := by
  unfold populationMean
  rw [← sub_div,← Finset.sum_sub_distrib,abs_div,
    abs_of_nonneg (show (0:ℝ) ≤ (Fintype.card ι:ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs (fun i => p i-q i) Finset.univ)
    (show (0:ℝ) ≤ (Fintype.card ι:ℝ) from Nat.cast_nonneg _)

theorem tendsto_population_test_gap
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (p q : ∀ t, Ω t → ι t → ℝ)
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hq : ∀ t i, Measurable (fun ω => q t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0:ℝ) 1)
    (hqb : ∀ t ω i, q t ω i ∈ Icc (0:ℝ) 1)
    (f : ℝ → ℝ) (hf : Continuous f) (hfb : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc (0:ℝ) 1)
    {K : ℝ} (hK : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x-f y| ≤ K*|x-y|)
    (hgap : Tendsto (fun t => ∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationMean (fun i => |f (p t ω i)-f (q t ω i)|) ∂P t) atTop (𝓝 0) := by
  have hI t := integrable_populationMean (P t) (fun ω i => |p t ω i-q t ω i|)
    (fun i => integrable_abs_gap (P t) (hp t i) (hq t i) (fun ω => hpb t ω i) (fun ω => hqb t ω i))
  have hfI t := integrable_populationMean (P t) (fun ω i => |f (p t ω i)-f (q t ω i)|)
    (fun i => integrable_abs_gap (P t) (hf.measurable.comp (hp t i)) (hf.measurable.comp (hq t i))
      (fun ω => hfb _ (hpb t ω i)) (fun ω => hfb _ (hqb t ω i)))
  have ht : Tendsto (fun t => K*(∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t))
      atTop (𝓝 0) := by simpa only [mul_zero] using hgap.const_mul K
  apply squeeze_zero (fun _ => integral_nonneg fun _ =>
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)) _ ht
  intro t
  have hh := integral_mono (hfI t) ((hI t).const_mul K) (fun ω => by
    change (∑ i, |f (p t ω i)-f (q t ω i)|)/(Fintype.card (ι t):ℝ) ≤
      K*((∑ i, |p t ω i-q t ω i|)/(Fintype.card (ι t):ℝ))
    rw [← mul_div_assoc,Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hK _ (hpb t ω i) _ (hqb t ω i))
      (Nat.cast_nonneg _))
  have he : (∫ ω, K*populationMean (fun i => |p t ω i-q t ω i|) ∂P t) =
      K*(∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t) := integral_const_mul _ _
  exact hh.trans_eq he

theorem tendsto_population_expectation_of_gap
    {Ω ι : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] [∀ t, Fintype (ι t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (p q : ∀ t, Ω t → ι t → ℝ)
    (hp : ∀ t i, Measurable (fun ω => p t ω i))
    (hq : ∀ t i, Measurable (fun ω => q t ω i))
    (hpb : ∀ t ω i, p t ω i ∈ Icc (0:ℝ) 1)
    (hqb : ∀ t ω i, q t ω i ∈ Icc (0:ℝ) 1)
    {a : ℝ} (ha : ∀ t, (∫ ω, populationMean (q t ω) ∂P t) = a)
    (hgap : Tendsto (fun t => ∫ ω, populationMean (fun i => |p t ω i-q t ω i|) ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, populationMean (p t ω) ∂P t) atTop (𝓝 a) := by
  have hI₁ t := integrable_populationMean (P t) (p t) (fun i =>
    UnitInterval.integrable _ _ (hp t i) (fun ω => (hpb t ω i).1) (fun ω => (hpb t ω i).2))
  have hI₂ t := integrable_populationMean (P t) (q t) (fun i =>
    UnitInterval.integrable _ _ (hq t i) (fun ω => (hqb t ω i).1) (fun ω => (hqb t ω i).2))
  have hI₃ t := integrable_populationMean (P t) (fun ω i => |p t ω i-q t ω i|)
    (fun i => integrable_abs_gap (P t) (hp t i) (hq t i) (fun ω => hpb t ω i) (fun ω => hqb t ω i))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hgap
  intro t
  rw [← ha t,← integral_sub (hI₁ t) (hI₂ t),Real.norm_eq_abs]
  exact abs_integral_le_integral_abs.trans
    (integral_mono ((hI₁ t).sub (hI₂ t)).abs (hI₃ t) (fun ω => populationMean_abs_sub_le _ _))

end FCAppendix.PayOnce.CovarianceConcentration
