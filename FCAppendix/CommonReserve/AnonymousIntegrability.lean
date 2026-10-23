import FCAppendix.CommonReserve.AnonymousReserve
import FCAppendix.CommonReserve.MixedInterim

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def anonymousActualPayment (Γ : Bayes.FiniteGame m n c Seed) (i : Fin m)
    (p : JointAction n × Bayes.Sample m n Seed) : ℝ :=
  p.1.bid * Γ.A.charge (Bayes.focalCount Γ i p.1 p.2).val +
    Γ.g * Γ.G.charge (Bayes.focalCount Γ i p.1 p.2).val

theorem measurable_anonymousActualPayment (Γ : Bayes.FiniteGame m n c Seed) (i : Fin m) :
    Measurable (anonymousActualPayment Γ i) :=
  (((measurable_bid n).comp measurable_fst).mul
    ((measurable_of_countable (fun k : Fin (n + 1) => Γ.A.charge k.val)).comp
      (Bayes.measurable_focalCount_joint Γ i))).add
    (((measurable_of_countable (fun k : Fin (n + 1) => Γ.G.charge k.val)).comp
      (Bayes.measurable_focalCount_joint Γ i)).const_mul Γ.g)

theorem anonymousActualPayment_nonneg (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (p : JointAction n × Bayes.Sample m n Seed) :
    0 ≤ anonymousActualPayment Γ i p :=
  add_nonneg (mul_nonneg p.1.bid_nonneg (Γ.A.nonneg _
    (Nat.le_of_lt_succ (Bayes.focalCount Γ i p.1 p.2).isLt)))
    (mul_nonneg Γ.g_nonneg (Γ.G.nonneg _
      (Nat.le_of_lt_succ (Bayes.focalCount Γ i p.1 p.2).isLt)))

theorem integrable_anonymousActualPayment_pure (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) :
    Integrable (fun ω => anonymousActualPayment Γ i (a, ω)) (Bayes.sampleLaw Γ) :=
  ((CountLaw.integrable_comp _ _ (Bayes.measurable_focalCount Γ i a)
    (fun k => Γ.A.charge k.val)).const_mul a.bid).add
    ((CountLaw.integrable_comp _ _ (Bayes.measurable_focalCount Γ i a)
      (fun k => Γ.G.charge k.val)).const_mul Γ.g)

theorem anonymousCost_eq_actual_integral (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) :
    anonymousCost Γ i a = ∫ ω, anonymousActualPayment Γ i (a, ω) ∂Bayes.sampleLaw Γ := by
  have hA : Integrable (fun ω => a.bid * Γ.A.charge (Bayes.focalCount Γ i a ω).val)
      (Bayes.sampleLaw Γ) :=
    (CountLaw.integrable_comp (Bayes.sampleLaw Γ) _ (Bayes.measurable_focalCount Γ i a)
      (fun k => Γ.A.charge k.val)).const_mul a.bid
  have hG : Integrable (fun ω => Γ.g * Γ.G.charge (Bayes.focalCount Γ i a ω).val)
      (Bayes.sampleLaw Γ) :=
    (CountLaw.integrable_comp (Bayes.sampleLaw Γ) _ (Bayes.measurable_focalCount Γ i a)
      (fun k => Γ.G.charge k.val)).const_mul Γ.g
  change anonymousCost Γ i a = ∫ ω,
    (a.bid * Γ.A.charge (Bayes.focalCount Γ i a ω).val +
      Γ.g * Γ.G.charge (Bayes.focalCount Γ i a ω).val) ∂Bayes.sampleLaw Γ
  rw [integral_add hA hG, integral_const_mul, integral_const_mul]
  simp only [anonymousCost, CountLaw.charge, Bayes.problem_outcome, CountLaw.expect_ofMeasure]

theorem integrable_anonymousCost_of_bestResponse (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) (ν : Measure (JointAction n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Bayes.problem Γ i).BestResponse v a) :
    Integrable (anonymousCost Γ i) ν := by
  apply (anonymousInterim Γ r hr hT i).integrable_cost_of_bestResponse ν
    (measurable_anonymousCost Γ i) v (add_nonneg Γ.g_nonneg hr)
  filter_upwards [hν] with a ha
  exact (anonymousInterim_bestResponse Γ r hr hT i v a).mpr ha

theorem integrable_anonymousActualPayment_of_bestResponse (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) (ν : Measure (JointAction n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Bayes.problem Γ i).BestResponse v a) :
    Integrable (anonymousActualPayment Γ i) (ν.prod (Bayes.sampleLaw Γ)) := by
  apply (integrable_prod_iff (measurable_anonymousActualPayment Γ i).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (integrable_anonymousActualPayment_pure Γ i), ?_⟩
  have he : (fun a => ∫ ω, ‖anonymousActualPayment Γ i (a, ω)‖ ∂Bayes.sampleLaw Γ) =
      anonymousCost Γ i := by
    funext a
    rw [anonymousCost_eq_actual_integral]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      change ‖anonymousActualPayment Γ i (a, ω)‖ = anonymousActualPayment Γ i (a, ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (anonymousActualPayment_nonneg Γ i (a, ω))]
  rw [he]
  exact integrable_anonymousCost_of_bestResponse Γ r hr hT i v ν hν

theorem anonymous_mixed_actual_payment_eq_cost (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) (ν : Measure (JointAction n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Bayes.problem Γ i).BestResponse v a) :
    (∫ p, anonymousActualPayment Γ i p ∂ν.prod (Bayes.sampleLaw Γ)) =
      ∫ a, anonymousCost Γ i a ∂ν := by
  rw [integral_prod _ (integrable_anonymousActualPayment_of_bestResponse Γ r hr hT i v ν hν)]
  simp_rw [← anonymousCost_eq_actual_integral]

end FCAppendix.CommonReserve
