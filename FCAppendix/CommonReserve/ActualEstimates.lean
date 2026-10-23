import FCAppendix.CommonReserve.ActualInterim

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

namespace FiniteGame

theorem shortfall_deviated_eq (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (a : Action n r) (ω : Sample m n r Seed) :
    shortfall p (deviated i a ω) Γ.policy ω.2 i =
      ∑ j, max (p - Bayes.entryBid (a.val j)) 0 * Γ.focalIndicator i j a ω := by
  classical
  simp [shortfall, accepted, Finset.sum_filter, focalIndicator, deviated, mul_ite]

theorem measurable_shortfall_joint (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) :
    Measurable (fun q : Action n r × Sample m n r Seed =>
      shortfall p (deviated i q.1 q.2) Γ.policy q.2.2 i) := by
  simp_rw [Γ.shortfall_deviated_eq]
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun q : Action n r × Sample m n r Seed =>
      Bayes.entryBid (q.1.val j)) :=
    Bayes.measurable_entryBid.comp
      (((measurable_pi_apply j).comp measurable_subtype_coe).comp measurable_fst)
  exact ((measurable_const.sub hm).max measurable_const).mul
    (Γ.measurable_focalIndicator_joint i j)

theorem shortfall_deviated_le (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (a : Action n r) (ω : Sample m n r Seed) :
    shortfall p (deviated i a ω) Γ.policy ω.2 i ≤ (n : ℝ) * max p 0 := by
  rw [Γ.shortfall_deviated_eq]
  calc
    _ ≤ ∑ _j : Fin n, max p 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply le_trans (mul_le_of_le_one_right (le_max_right _ _)
        (Γ.focalIndicator_le_one i j a ω))
      exact max_le_max (sub_le_self _ (Γ.entryBid_nonneg a j)) le_rfl
    _ = _ := by simp

theorem integrable_shortfall (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (a : Action n r) :
    Integrable (fun ω => shortfall p (deviated i a ω) Γ.policy ω.2 i) Γ.sampleLaw := by
  simp_rw [Γ.shortfall_deviated_eq]
  exact integrable_finsetSum _ (fun j _ => (Γ.integrable_focalIndicator i j a).const_mul _)

theorem measurable_paymentError (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) :
    Measurable (Γ.paymentError i p) :=
  (Γ.measurable_shortfall_joint i p).stronglyMeasurable.integral_prod_right'.measurable

theorem paymentError_nonneg (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (a : Action n r) : 0 ≤ Γ.paymentError i p a :=
  integral_nonneg fun ω => shortfall_nonneg p (deviated i a ω) Γ.policy ω.2 i

theorem paymentError_le (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (a : Action n r) : Γ.paymentError i p a ≤ (n : ℝ) * max p 0 := by
  have hh := integral_mono (Γ.integrable_shortfall i p a)
    (integrable_const ((n : ℝ) * max p 0)) (Γ.shortfall_deviated_le i p a)
  simpa only [paymentError, integral_const, probReal_univ, one_smul] using hh

theorem integrable_paymentError (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ)
    (ν : Measure (Action n r)) [IsFiniteMeasure ν] :
    Integrable (Γ.paymentError i p) ν := by
  apply Integrable.of_bound (Γ.measurable_paymentError i p).aestronglyMeasurable
    ((n : ℝ) * max p 0)
  exact Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Γ.paymentError_nonneg i p a)]
    exact Γ.paymentError_le i p a

theorem purePayoff_le_price_error (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p v : ℝ) (a : Action n r) :
    Γ.purePayoff i v a ≤ (v - Γ.g - p) * (Γ.outcome i a).success -
      p * (Γ.outcome i a).duplicates + Γ.paymentError i p a := by
  have hS := Γ.integrable_count_test i a (fun k => successIndicator k.val)
  have hD := Γ.integrable_count_test i a (fun k => (k.val : ℝ) - successIndicator k.val)
  have hSD : Integrable (fun ω => (v - Γ.g - p) * successIndicator (Γ.focalCount i a ω).val -
      p * (((Γ.focalCount i a ω).val : ℝ) - successIndicator (Γ.focalCount i a ω).val))
      Γ.sampleLaw := (hS.const_mul (v - Γ.g - p)).sub (hD.const_mul p)
  have hh := integral_mono (Γ.integrable_purePayoff i v a)
    (hSD.add (Γ.integrable_shortfall i p a))
    (fun ω => payoff_le_price_error v Γ.g p Γ.g_nonneg Γ.G
      (deviated i a ω) Γ.policy ω.2 i)
  simp only [Pi.add_apply] at hh
  rw [integral_add hSD (Γ.integrable_shortfall i p a),
    integral_sub (hS.const_mul (v - Γ.g - p)) (hD.const_mul p),
    integral_const_mul, integral_const_mul] at hh
  simpa only [purePayoff, paymentError, CountLaw.success,
    CountLaw.duplicates_eq_expect, outcome_expect] using hh

theorem integrable_duplicates (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsFiniteMeasure ν] :
    Integrable (fun a => (Γ.outcome i a).duplicates) ν :=
  (Γ.integrable_outcome_expect i ν (fun k => (k.val : ℝ))).sub
    (Γ.integrable_outcome_expect i ν (fun k => successIndicator k.val))

theorem mixedOutcome_load (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsProbabilityMeasure ν] :
    (Γ.mixedOutcome i ν).load = ∫ a, (Γ.outcome i a).load ∂ν :=
  Γ.mixedOutcome_expect i ν _

theorem mixedOutcome_duplicates (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsProbabilityMeasure ν] :
    (Γ.mixedOutcome i ν).duplicates = ∫ a, (Γ.outcome i a).duplicates ∂ν := by
  simp_rw [CountLaw.duplicates_eq_expect]
  exact Γ.mixedOutcome_expect i ν _

theorem envelope_le_mixed_price_error (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p v : ℝ) (ν : Measure (Action n r)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ a ∂ν, (Γ.interim i).BestResponse v a) :
    Γ.envelope i v ≤ (v - Γ.g - p) * (Γ.mixedOutcome i ν).success -
      p * (Γ.mixedOutcome i ν).duplicates + ∫ a, Γ.paymentError i p a ∂ν := by
  have he : Γ.purePayoff i v =ᵐ[ν] fun _ => Γ.envelope i v := by
    filter_upwards [hν] with a ha
    simpa only [interim_payoff, interim_envelope] using
      (Γ.interim i).bestResponse_iff_attains v a |>.mp ha
  have hi : Integrable (Γ.purePayoff i v) ν := (integrable_const _).congr he.symm
  have hS : Integrable (fun a => (Γ.outcome i a).success) ν :=
    Γ.integrable_outcome_expect i ν (fun k => successIndicator k.val)
  have hD := Γ.integrable_duplicates i ν
  have hSD : Integrable (fun a => (v - Γ.g - p) * (Γ.outcome i a).success -
      p * (Γ.outcome i a).duplicates) ν := (hS.const_mul (v - Γ.g - p)).sub (hD.const_mul p)
  have hh := integral_mono hi (hSD.add
    (Γ.integrable_paymentError i p ν)) (Γ.purePayoff_le_price_error i p v)
  simp only [Pi.add_apply] at hh
  rw [integral_congr_ae he, integral_const, probReal_univ, one_smul,
    integral_add hSD (Γ.integrable_paymentError i p ν),
    integral_sub (hS.const_mul (v - Γ.g - p)) (hD.const_mul p),
    integral_const_mul, integral_const_mul,
    ← Γ.mixedOutcome_success i ν, ← Γ.mixedOutcome_duplicates i ν] at hh
  exact hh

def typePaymentError (Γ : FiniteGame m n c r Seed) (i : Fin m) (p v : ℝ) : ℝ :=
  ∫ a, Γ.paymentError i p a ∂Γ.σ v

theorem measurable_typePaymentError (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) :
    Measurable (Γ.typePaymentError i p) :=
  ((Γ.measurable_paymentError i p).comp
    (show Measurable (fun x : ℝ × Action n r => x.2) from
      measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem typePaymentError_nonneg (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p v : ℝ) : 0 ≤ Γ.typePaymentError i p v :=
  integral_nonneg (Γ.paymentError_nonneg i p)

theorem typePaymentError_le (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p v : ℝ) : Γ.typePaymentError i p v ≤ (n : ℝ) * max p 0 := by
  have h := integral_mono (Γ.integrable_paymentError i p (Γ.σ v))
    (integrable_const ((n : ℝ) * max p 0)) (Γ.paymentError_le i p)
  simpa only [typePaymentError, integral_const, probReal_univ, one_smul] using h

theorem integrable_typePaymentError (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (Γ.typePaymentError i p) μ := by
  apply Integrable.of_bound (Γ.measurable_typePaymentError i p).aestronglyMeasurable
    ((n : ℝ) * max p 0)
  exact Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Γ.typePaymentError_nonneg i p v)]
    exact Γ.typePaymentError_le i p v

@[simp] theorem mixedOutcome_strategy (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) : Γ.mixedOutcome i (Γ.σ v) = Γ.typeOutcome i v := rfl

theorem typeOutcome_expect (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (v : ℝ) (f : Fin (n + 1) → ℝ) :
    (Γ.typeOutcome i v).expect f = ∫ a, (Γ.outcome i a).expect f ∂Γ.σ v :=
  Γ.mixedOutcome_expect i (Γ.σ v) f

theorem measurable_typeOutcome_expect (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) : Measurable (fun v => (Γ.typeOutcome i v).expect f) := by
  simp_rw [typeOutcome_expect]
  exact ((Γ.measurable_outcome_expect i f).comp
    (show Measurable (fun x : ℝ × Action n r => x.2) from
      measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem integrable_typeOutcome_expect (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Fin (n + 1) → ℝ) :
    Integrable (fun v => (Γ.typeOutcome i v).expect f) μ :=
  Integrable.of_bound (Γ.measurable_typeOutcome_expect i f).aestronglyMeasurable
    (∑ k, ‖f k‖) (Eventually.of_forall fun v => (Γ.typeOutcome i v).norm_expect_le_sum_norm f)

theorem ae_envelope_le_type_price_error (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) (hΓ : Γ.UsersOptimal) :
    ∀ᵐ v ∂Γ.F, Γ.envelope i v ≤
      (v - Γ.g - p) * (Γ.typeOutcome i v).success -
        p * (Γ.typeOutcome i v).duplicates + Γ.typePaymentError i p v := by
  filter_upwards [hΓ i] with v hv
  exact Γ.envelope_le_mixed_price_error i p v (Γ.σ v) (by
    filter_upwards [hv] with a ha
    exact (Γ.interim_bestResponse i v a).mpr ha)

theorem accepted_singleton_subset (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b : ℝ) (hb : r ≤ b) (ω : Sample m n r Seed) :
    accepted (deviated i (singleton j b hb) ω) Γ.policy ω.2 i ⊆ {j} := by
  classical
  intro l hl
  have hp := accepted_present _ Γ.policy ω.2 i l hl
  by_contra hne
  have hlj : l ≠ j := by simpa using hne
  exact hp (by simp [deviated, singleton, hlj])

theorem count_singleton_le_one (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b : ℝ) (hb : r ≤ b) (ω : Sample m n r Seed) :
    count (deviated i (singleton j b hb) ω) Γ.policy ω.2 i ≤ 1 := by
  simpa only [count, Finset.card_singleton] using
    Finset.card_le_card (Γ.accepted_singleton_subset i j b hb ω)

theorem payment_singleton (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b : ℝ) (hb : r ≤ b) (ω : Sample m n r Seed) :
    payment (deviated i (singleton j b hb) ω) Γ.policy ω.2 i =
      b * count (deviated i (singleton j b hb) ω) Γ.policy ω.2 i := by
  classical
  have he : payment (deviated i (singleton j b hb) ω) Γ.policy ω.2 i =
      ∑ _l ∈ accepted (deviated i (singleton j b hb) ω) Γ.policy ω.2 i, b := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlj : l = j := Finset.mem_singleton.mp (Γ.accepted_singleton_subset i j b hb ω hl)
    simp [deviated, hlj, singleton, Bayes.entryBid]
  rw [he]
  simp [count, mul_comm]

theorem singleton_payoff_eq (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b : ℝ) (hb : r ≤ b) (v : ℝ) :
    Γ.purePayoff i v (singleton j b hb) =
      (v - Γ.g - b) * (Γ.outcome i (singleton j b hb)).success := by
  have hn : 1 ≤ n := by have := j.isLt; omega
  have he (ω : Sample m n r Seed) :
      payoff v Γ.g Γ.G (deviated i (singleton j b hb) ω) Γ.policy ω.2 i =
        (v - Γ.g - b) * successIndicator
          (count (deviated i (singleton j b hb) ω) Γ.policy ω.2 i) := by
    have hK := Γ.count_singleton_le_one i j b hb ω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with hz | hone
    · simp [payoff, Γ.payment_singleton, hz, Γ.G.zero, successIndicator]
    · simp only [payoff, Γ.payment_singleton, hone, Γ.G.one hn,
        successIndicator, one_ne_zero, if_false, Nat.cast_one, mul_one]
      ring
  simp only [purePayoff, he, integral_const_mul, CountLaw.success, outcome_expect,
    focalCount]

theorem singleton_envelope_lower (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (p d ε v : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hε : 0 ≤ ε) (hb : r ≤ p + d)
    (hS : 1 - ε ≤ (Γ.outcome i (singleton j (p + d) hb)).success) :
    max (v - Γ.g - p) 0 - (d + ε * max (v - Γ.g) 0) ≤ Γ.envelope i v := by
  have hU0 : 0 ≤ Γ.envelope i v := by
    simpa only [interim_envelope] using (Γ.interim i).envelope_nonneg v
  have hU := (Γ.interim i).action_le_envelope v (singleton j (p + d) hb)
  rw [interim_payoff, interim_envelope, Γ.singleton_payoff_eq] at hU
  have hS0 := (Γ.outcome i (singleton j (p + d) hb)).success_nonneg
  have hS1 := (Γ.outcome i (singleton j (p + d) hb)).success_le_one
  have hw := le_max_left (v - Γ.g) 0
  have hw0 := le_max_right (v - Γ.g) 0
  by_cases hv : v - Γ.g - p ≤ 0
  · rw [max_eq_right hv]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hv)]
    by_cases hvd : v - Γ.g - p - d ≤ 0
    · nlinarith
    · have hm := mul_le_mul_of_nonneg_left hS (le_of_not_ge hvd)
      have he := mul_le_mul_of_nonneg_left
        (show v - Γ.g - p - d ≤ max (v - Γ.g) 0 by linarith) hε
      nlinarith

end FiniteGame
end FCAppendix.CommonReserve
